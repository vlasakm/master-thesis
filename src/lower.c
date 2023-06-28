#include "ir.h"
#include "inst.h"
#include "x86-64.h"

typedef struct {
	Arena *arena;
	GArena *labels;
	MFunction *function;
	MBlock *block;
	Oper index;
	size_t block_cnt;
	size_t callee_saved_reg_start;
} TranslationState;

static void
add_inst_to_block(MBlock *block, Inst *new)
{
	prepend_inst(&block->insts, new);
}


static Inst *
add_inst(TranslationState *ts, InstKind kind, u8 subkind, X86Mode mode)
{
	Inst *new = create_inst(ts->arena, kind, subkind, mode);
	add_inst_to_block(ts->block, new);
	return new;
}

static void
add_copy(TranslationState *ts, Oper dest, Oper src)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV, M_Cr);
	IREG1(inst) = dest;
	IREG2(inst) = src;
}

static Inst *
add_load(TranslationState *ts, Oper dest, Oper addr)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV, M_CM);
	IREG(inst) = dest;
	IBASE(inst) = addr;
	IINDEX(inst) = R_NONE;
	return inst;
}

static Inst *
add_store(TranslationState *ts, Oper addr, Oper value)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV, M_Mr);
	IREG(inst) = value;
	IBASE(inst) = addr;
	IINDEX(inst) = R_NONE;
	return inst;
}

static void
add_lea(TranslationState *ts, Oper dest, Oper base, Oper disp)
{
	Inst *inst = add_inst(ts, IK_MOV, LEA, M_CM);
	IREG(inst) = dest;
	IBASE(inst) = base;
	IINDEX(inst) = R_NONE;
	IDISP(inst) = disp;
}

static void
add_lea_label(TranslationState *ts, Oper dest, Oper label)
{
	Inst *inst = add_inst(ts, IK_MOV, LEA, M_CM);
	IREG(inst) = dest;
	IBASE(inst) = R_NONE;
	IINDEX(inst) = R_NONE;
	ILABEL(inst) = label;
}

static void
add_mov_imm(TranslationState *ts, Oper dest, u64 imm)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV, M_CI);
	IREG(inst) = dest;
	set_imm64(inst, imm);
}

static Inst *
add_binop_imm(TranslationState *ts, X86Group1 op, Oper reg, Oper imm)
{
	Inst *inst = add_inst(ts, IK_BINALU, op, M_Ri);
	inst->writes_flags = true;
	IREG(inst) = reg;
	IIMM(inst) = imm;
	return inst;
}

static void
add_set_zero(TranslationState *ts, Oper oper)
{
	// Set zero with `mov` so that we don't introduce additional constraints
	// on the register through XOR register uses.
	// TODO: xor oper, oper
	Inst *inst = add_inst(ts, IK_MOV, MOV, M_CI);
	IREG(inst) = oper;
	set_imm64(inst, 0);
}

static void
add_unop(TranslationState *ts, X86Group3 op, Oper op1)
{
	Inst *inst = add_inst(ts, IK_UNALU, op, M_R);
	inst->writes_flags = true;
	IREG(inst) = op1;
}

static void
add_binop(TranslationState *ts, X86Group1 op, Oper op1, Oper op2)
{
	Inst *inst = add_inst(ts, IK_BINALU, op, M_Rr);
	inst->writes_flags = true;
	IREG1(inst) = op1;
	IREG2(inst) = op2;
}

static void
add_cmp(TranslationState *ts, X86Group1 op, Oper op1, Oper op2)
{
	Inst *inst = add_inst(ts, IK_BINALU, op, M_rr);
	inst->writes_flags = true;
	IREG1(inst) = op1;
	IREG2(inst) = op2;
}

static void
add_shift(TranslationState *ts, X86Group2 op, Oper op1, Oper op2)
{
	Inst *inst = add_inst(ts, IK_SHIFT, op, M_Rr);
	// Don't mark this instruction as writing flags. The instruction doesn't
	// write flags if the shift amount is zero.
	//inst->writes_flags = true;
	IREG1(inst) = op1;
	IREG2(inst) = op2;
	assert(op2 == R_RCX);
}

static void
add_push(TranslationState *ts, Oper oper)
{
	Inst *inst = add_inst(ts, IK_PUSH, 0, M_r);
	IREG(inst) = oper;
}

static void
add_pop(TranslationState *ts, Oper oper)
{
	Inst *inst = add_inst(ts, IK_POP, 0, M_C);
	IREG(inst) = oper;
}

static void
add_setcc(TranslationState *ts, CondCode cc, Oper oper)
{
	// NOTE: We model setcc with a read/write mode, since only part of the
	// register is written, so the previous value is observed as well. In
	// particular we often zero out the register before using setcc on it,
	// so by reading here we ensure that the zeroing out is not optimized
	// away.
	Inst *inst = add_inst(ts, IK_SETCC, cc, M_R);
	inst->reads_flags = true;
	IREG(inst) = oper;
}

static void
add_imul3(TranslationState *ts, Oper dest, Oper arg, Oper imm)
{
	Inst *inst = add_inst(ts, IK_IMUL3, 0, M_Cri);
	inst->writes_flags = true;
	IREG(inst) = dest;
	IREG2(inst) = arg;
	IIMM(inst) = imm;
}

static void
add_jmp(TranslationState *ts, Oper block_index)
{
	Inst *inst = add_inst(ts, IK_JUMP, 0, M_L);
	ILABEL(inst) = block_index;
}

static void
add_jcc(TranslationState *ts, CondCode cc, Oper block_index)
{
	Inst *inst = add_inst(ts, IK_JCC, cc, M_L);
	inst->reads_flags = true;
	ILABEL(inst) = block_index;
}

static void
add_call(TranslationState *ts, Oper function_reg, Oper arg_cnt)
{
	Inst *inst = add_inst(ts, IK_CALL, 0, M_rCALL);
	IREG(inst) = function_reg;
	IARG_CNT(inst) = arg_cnt;
}

static Inst *
add_entry(TranslationState *ts, Oper arg_cnt)
{
	Inst *inst = add_inst(ts, IK_ENTRY, 0, M_ENTRY);
	IARG_CNT(inst) = arg_cnt;
	return inst;
}

static void
add_cqo(TranslationState *ts)
{
	add_inst(ts, IK_CQO, 0, M_AD);
}

static void
translate_call(TranslationState *ts, Oper res, Oper fun, Oper *args, size_t arg_cnt, bool vararg)
{
	// TODO: struct arguments

	// -1 for terminating zero
	size_t arg_regs = ARRAY_LEN(argument_regs) - 1;
	size_t gpr_index = 0;
	for (size_t i = 0; gpr_index < arg_regs && i < arg_cnt; i++) {
		add_copy(ts, argument_regs[gpr_index], args[i]);
		gpr_index++;
	}
	// Odd number of pushed arguments => have to realign the stack to 16 bytes
	bool odd_push = arg_cnt > arg_regs && arg_cnt & 1;
	if (odd_push) {
		add_binop_imm(ts, G1_SUB, R_RSP, 8);
	}
	for (size_t i = arg_cnt; i > arg_regs; i--) {
		add_push(ts, args[i - 1]);
	}
	if (vararg) {
		add_set_zero(ts, R_RAX);
	}
	add_call(ts, fun, gpr_index);
	// Pop arguments from the stack (if any)
	if (arg_cnt > arg_regs) {
		Oper pop_size = 8 * (arg_cnt - arg_regs + odd_push);
		if (pop_size > 0) {
			add_binop_imm(ts, G1_ADD, R_RSP, pop_size);
		}
	}
	// Copy return value
	add_copy(ts, res, R_RAX);
}

static void
add_load_with_disp(TranslationState *ts, Oper dest, Oper base, Oper disp)
{
	Inst *load = create_load_with_disp(ts->arena, dest, base, disp);
	add_inst_to_block(ts->block, load);
}

static void
translate_prologue(TranslationState *ts)
{
	Function *function = ts->function->func;

	// In prologue we emit a "virtual" entry instruction which marks all
	// argument registers as defined. This is necessary for later stages
	// which might expect anything used (and argument registers are used,
	// see below), to have a corresponding definition.
	Inst *entry = add_entry(ts, type_function_param_cnt(function->base.type));

	// Classic x86-64 prologue. We could do without it, and instead of
	// addressing relative to the base pointer, we could address relative to
	// the stack pointer. Doing it the traditional way makes at least some
	// tools usable with code generated by use, since we don't output any
	// debug information.
	add_push(ts, R_RBP);
	add_copy(ts, R_RBP, R_RSP);

	// Add instruction to make stack space, since we may spill we don't know
	// how much stack space to reserve yet, we will replace the dummy '42'
	// with proper stack space requirement after register allocation. Note
	// that due to constraints of encoding of this instruction, we can't
	// address stack frame larger than 2 GiB (32 bit signed relative
	// offfset). On the x86-64 this is much bigger than the entire available
	// stack, but on other architectures where immediate offsets are
	// smaller, this may need more consideration.
	ts->function->make_stack_space = add_binop_imm(ts, G1_SUB, R_RSP, 42);

	// Save callee saved registers to temporaries. That way the registers
	// don't automatically intefere with everything (since they will be
	// "read" by the return instruction). If it makes sense to use the
	// callee saved registers, they will be used, if not, due to coalescing
	// these temporaries will likely be coalesced with the registers and the
	// copies eliminated.
	ts->callee_saved_reg_start = ts->index;
	for (size_t i = 0; i < ARRAY_LEN(saved); i++) {
		add_copy(ts, ts->index++, saved[i]);
	}

	// Handle the incoming arguments. First 6 arguments come from registers,
	// the rest are passed on the stack.
	size_t arg_cnt = type_function_param_cnt(function->base.type);
	size_t gpr_index = 0;
	//             [ ...       ]
	//             [ ARG8      ]
	// RBP + 16    [ ARG7      ]
	// RBP +  8 -> [ RET. ADDR ]
	// RBP +  0 -> [ RBP       ]
	Oper stack_offset = 16;
	for (size_t i = 0; i < arg_cnt; i++) {
		Argument *argument = &function->args[i];
		switch (VTYPE(argument)->kind) {
		case TY_VOID:
		case TY_CHAR:
		case TY_FUNCTION:
			UNREACHABLE();
		case TY_INT:
		case TY_POINTER:
			if (gpr_index < ARRAY_LEN(argument_regs) - 1) {
				add_copy(ts, VINDEX(argument), argument_regs[gpr_index]);
				gpr_index++;
			} else {
				add_load_with_disp(ts, VINDEX(argument), R_RBP, stack_offset);
				stack_offset += 8;
			}
			break;
		case TY_STRUCT:
			NOT_IMPLEMENTED("struct arguments");
			break;
		}
	}
	IARG_CNT(entry) = gpr_index;
}

static void
translate_return(TranslationState *ts, Oper *ret_val)
{
	if (ret_val) {
		add_copy(ts, R_RAX, *ret_val);
	}
	// Restore callee saved registers. See prologue for more details.
	size_t callee_saved_reg = ts->callee_saved_reg_start;
	for (size_t i = 0; i < ARRAY_LEN(saved); i++) {
		add_copy(ts, saved[i], callee_saved_reg++);
	}
	add_copy(ts, R_RSP, R_RBP);
	add_pop(ts, R_RBP);
	Inst *ret = add_inst(ts, IK_RET, 0, M_RET);
	if (ret_val) {
		// Make return instruction read the returned value.
		// NOTE: This has to be updated when multiple return registers
		// are needed.
		IREG(ret) = R_RAX;
	}

}

static void
translate_unop(TranslationState *ts, X86Group3 op, Oper res, Oper arg)
{
	add_copy(ts, res, arg);
	add_unop(ts, op, res);
}

static void
translate_binop(TranslationState *ts, X86Group1 op, Oper res, Oper arg1, Oper arg2)
{
	add_copy(ts, res, arg1);
	add_binop(ts, op, res, arg2);
}

static void
translate_shift(TranslationState *ts, X86Group2 op, Oper res, Oper arg1, Oper arg2)
{
	add_copy(ts, res, arg1);
	add_copy(ts, R_RCX, arg2);
	add_shift(ts, op, res, R_RCX);
}

typedef enum {
	SK_SIGNED,
	SK_UNSIGNED,
} SignednessKind;

typedef enum {
	DR_QUOTIENT,
	DR_REMAINDER,
} DivisionResult;

static void
translate_div(TranslationState *ts, Oper res, Oper arg1, Oper arg2, SignednessKind sign, DivisionResult dr)
{
	// First copy 64-bit dividend into rax.
	add_copy(ts, R_RAX, arg1);
	Oper op;
	if (sign == SK_SIGNED) {
		op = G3_IDIV;
		// If the division is signed, sign-extend rax into rdx.
		add_cqo(ts);
	} else {
		op = G3_DIV;
		// If the division is unsigned, zero-extend rax into rdx.
		add_set_zero(ts, R_RDX);
	}
	// Perform division of 128-bit rdx:rax pair by the divisor in arbitrary
	// register.
	Inst *inst = add_inst(ts, IK_MULDIV, op, M_ADr);
	IREG(inst) = arg2;

	// Copy the wanted result into the result register.
	Oper result = dr == DR_REMAINDER ? R_RDX : R_RAX;
	add_copy(ts, res, result);
}

static void
translate_cmpop(TranslationState *ts, CondCode cc, Oper res, Oper arg1, Oper arg2)
{
	// Zero out register first, so we don't change the flags before setcc.
	add_set_zero(ts, res);
	add_cmp(ts, G1_CMP, arg1, arg2);
	add_setcc(ts, cc, res);
}

size_t
add_label(GArena *labels, Value *value)
{
	// Add a value to the array of labels, but only if it is not already
	// there. I.e. we perform deduplication, since a lot of labels are
	// reused.
	Value **existing = garena_array(labels, Value *);
	size_t index = garena_cnt(labels, Value *);
	for (size_t i = index; i--;) {
		if (existing[i] == value) {
			return i;
		}
	}
	garena_push_value(labels, Value *, value);
	return index;
}

Oper
translate_operand(TranslationState *ts, Value *operand)
{
	Oper res;
	switch (operand->kind) {
	case VK_BLOCK:
		res = operand->index;
		break;
	case VK_FUNCTION:
	case VK_GLOBAL:
	case VK_STRING: {
		size_t label_index = add_label(ts->labels, operand);
		res = ts->index++;
		add_lea_label(ts, res, label_index);
		break;
	}
	case VK_CONSTANT: {
		Constant *k = (void*) operand;
		res = ts->index++;
		add_mov_imm(ts, res, k->k);
		break;
	}
	case VK_ALLOCA: {
		Alloca *alloca = (Alloca *) operand;
		res = ts->index++;
		add_lea(ts, res, R_RBP, alloca->stack_offset);
		break;
	}
	default:
		res = operand->index;
		break;
	}
	return res;
}

void
translate_value(TranslationState *ts, Value *v)
{
	Oper ops[256];
	Value **operands = value_operands(v);
	size_t operand_cnt = value_operand_cnt(v);
	assert(operand_cnt < ARRAY_LEN(ops));
	for (size_t i = 0; i < operand_cnt; i++) {
		ops[i] = translate_operand(ts, operands[i]);
	}

	Oper res = v->index;

	switch (v->kind) {
	case VK_NOP:
	case VK_UNDEFINED:
		break;
	case VK_IDENTITY:
		add_copy(ts, res, ops[0]);
		break;
	case VK_ALLOCA: {
		Alloca *alloca = (Alloca *) v;
		size_t size = alloca->size;
		size_t alignment = type_alignment(v->type);
		alloca->stack_offset = mfunction_reserve_stack_space(ts->function, size, alignment);
		break;
	}
	case VK_ADD:  translate_binop(ts, G1_ADD, res, ops[0], ops[1]); break;
	case VK_SUB:  translate_binop(ts, G1_SUB, res, ops[0], ops[1]); break;
	case VK_MUL:  translate_binop(ts, G1_IMUL, res, ops[0], ops[1]); break;
	case VK_UDIV: translate_div(ts, res, ops[0], ops[1], SK_UNSIGNED, DR_QUOTIENT); break;
	case VK_SDIV: translate_div(ts, res, ops[0], ops[1], SK_SIGNED, DR_QUOTIENT); break;
	case VK_UREM: translate_div(ts, res, ops[0], ops[1], SK_UNSIGNED, DR_REMAINDER); break;
	case VK_SREM: translate_div(ts, res, ops[0], ops[1], SK_SIGNED, DR_REMAINDER); break;
	case VK_AND:  translate_binop(ts, G1_AND, res, ops[0], ops[1]); break;
	case VK_OR:   translate_binop(ts, G1_OR, res, ops[0], ops[1]); break;
	case VK_SHL:  translate_shift(ts, G2_SHL, res, ops[0], ops[1]); break;
	case VK_SAR:  translate_shift(ts, G2_SAR, res, ops[0], ops[1]); break;
	case VK_SLR:  translate_shift(ts, G2_SHR, res, ops[0], ops[1]); break;
	case VK_NEG:  translate_unop(ts, G3_NEG, res, ops[0]); break;
	case VK_NOT:  translate_unop(ts, G3_NOT, res, ops[0]); break;
	case VK_EQ:   translate_cmpop(ts, CC_E, res, ops[0], ops[1]); break;
	case VK_NEQ:  translate_cmpop(ts, CC_NE, res, ops[0], ops[1]); break;
	case VK_SLT:  translate_cmpop(ts, CC_L, res, ops[0], ops[1]); break;
	case VK_SLEQ: translate_cmpop(ts, CC_LE, res, ops[0], ops[1]); break;
	case VK_SGT:  translate_cmpop(ts, CC_G, res, ops[0], ops[1]); break;
	case VK_SGEQ: translate_cmpop(ts, CC_GE, res, ops[0], ops[1]); break;
	case VK_ULT:  translate_cmpop(ts, CC_B, res, ops[0], ops[1]); break;
	case VK_ULEQ: translate_cmpop(ts, CC_BE, res, ops[0], ops[1]); break;
	case VK_UGT:  translate_cmpop(ts, CC_A, res, ops[0], ops[1]); break;
	case VK_UGEQ: translate_cmpop(ts, CC_AE, res, ops[0], ops[1]); break;

	case VK_LOAD: {
		Inst *load = add_load(ts, res, ops[0]);
		if (pointer_child(LOAD_ADDR(v)->type)->kind == TY_CHAR) {
			IS(load) = MOVSX8;
		}
		break;
	}
	case VK_STORE: {
		Inst *store = add_store(ts, ops[0], ops[1]);
		if (pointer_child(STORE_ADDR(v)->type)->kind == TY_CHAR) {
			IS(store) = MOV8;
		}
		break;
	}
	case VK_GET_INDEX_PTR: {
		size_t size = type_size(pointer_child(v->type));
		Oper size_oper = ts->index++;
		add_imul3(ts, size_oper, ops[1], size);
		translate_binop(ts, G1_ADD, res, ops[0], size_oper);
		break;
	}
	case VK_GET_MEMBER_PTR: {
		Field *field = get_member(v);
		// A hack. Since ops[1] (the field index) already got
		// translated, let's change it to the field's offset.
		set_imm64(ts->block->insts.prev, field->offset);
		translate_binop(ts, G1_ADD, res, ops[0], ops[1]);
		break;
	}
	case VK_CALL: {
		bool vararg = type_as_function(CALL_FUN(v)->type)->vararg;
		size_t arg_cnt = value_operand_cnt(v) - 1;
		translate_call(ts, res, ops[0], &ops[1], arg_cnt, vararg);
		break;
	}
	case VK_JUMP: {
		add_jmp(ts, ops[0]);
		break;
	}
	case VK_BRANCH:
		add_cmp(ts, G1_TEST, ops[0], ops[0]);
		add_jcc(ts, CC_Z, ops[2]);
		add_jmp(ts, ops[1]);
		break;
	case VK_RET: {
		Oper *return_value = v->operand_cnt == 1 ? &ops[0] : NULL;
		translate_return(ts, return_value);
		break;
	}
	case VK_CONSTANT:
	case VK_BLOCK:
	case VK_FUNCTION:
	case VK_GLOBAL:
	case VK_STRING:
	case VK_ARGUMENT:
		UNREACHABLE();
		break;
	case VK_PHI:
		// SSA should have been deconstructed _before_ translation.
		UNREACHABLE();
		break;
	}
}

MFunction *
translate_function(Arena *arena, GArena *labels, Function *function)
{
	MFunction *mfunction = mfunction_create(arena, function, labels);

	TranslationState ts_ = {
		.arena = arena,
		.labels = labels,
		.index = function->value_cnt,
		.block = NULL,
		.function = mfunction,
	};
	TranslationState *ts = &ts_;

	Block **post_order = function->post_order;
	size_t i = 0;
	for (size_t b = function->block_cnt; b--;) {
		Block *block = post_order[b];
		MBlock *mblock = mblock_create(arena, block);
		mfunction->mblocks[i] = mblock;
		mblock->index = i;
		i++;
		ts->block = mblock;
		if (block == function->entry) {
			translate_prologue(ts);
		}
		FOR_EACH_IN_BLOCK(block, v) {
			translate_value(ts, v);
		}
	}

	mfunction->vreg_cnt = ts->index;
	function->mfunction = mfunction;
	return mfunction;
}
