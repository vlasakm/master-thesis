#include <stdio.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdalign.h>
#include <string.h>
#include <setjmp.h>
#include <assert.h>
#include <errno.h>

#include "utils.h"
#include "str.h"
#include "table.h"
#include "arena.h"
#include "worklist.h"
#include "type.h"
#include "ir.h"
#include "inst.h"
#include "x86-64.h"
#include "parser.h"

Str
arena_vaprintf(Arena *arena, const char *fmt, va_list ap)
{
	va_list ap_orig;
	// save original va_list (vprintf changes it)
	va_copy(ap_orig, ap);

	size_t available = arena->current->size - arena->current->pos;
	void *mem = ((u8 *) arena->current) + arena->current->pos;
	ASAN_UNPOISON_MEMORY_REGION(mem, available);
	int len = vsnprintf(mem, available, fmt, ap);
	assert(len >= 0);
	len += 1; // terminating null
	if ((size_t) len <= available) {
		arena->current->pos += (size_t) len;
		ASAN_POISON_MEMORY_REGION(((unsigned char *) arena->current) + arena->current->pos, available - len);
	} else {
		mem = arena_alloc(arena, (size_t) len);
		vsnprintf(mem, (size_t) len, fmt, ap_orig);
	}
	va_end(ap_orig);
	return (Str) { .str = mem, .len = len - 1 };
}

Str PRINTF_LIKE(2)
arena_aprintf(Arena *arena, const char *fmt, ...)
{
	va_list ap;
	va_start(ap, fmt);
	Str str = arena_vaprintf(arena, fmt, ap);
	va_end(ap);
	return str;
}

typedef struct {
	Arena *arena;
	GArena *labels;
	MFunction *function;
	MBlock *block;
	size_t stack_space;
	Oper index;
	size_t block_cnt;
	size_t callee_saved_reg_start;
	Inst *make_stack_space;
} TranslationState;

Inst *
create_inst(Arena *arena, InstKind kind, int subkind)
{
	//InstDesc *desc = &inst_desc[op];
	//size_t operand_cnt = desc->label_cnt;
	//Inst *inst = arena_alloc(arena, sizeof(*inst) + operand_cnt * sizeof(inst->ops[0]));
	Inst *inst = arena_alloc(arena, sizeof(*inst) + 6 * sizeof(inst->ops[0]));
	inst->kind = kind;
	inst->subkind = subkind;
	inst->flags_observed = false; // Redefined later by analysis.
	inst->writes_flags = false; // Default is no flags.
	inst->reads_flags = false; // Default is no flags.
	memset(&inst->ops[0], 0, 6 * sizeof(inst->ops[0]));
	//for (size_t i = 0; i < 6; i++) {
	//	inst->ops[i] = va_arg(ap, Oper);
	//}
	return inst;
}

static void
add_inst_(TranslationState *ts, Inst *new)
{
	Inst *head = &ts->block->insts;
	Inst *last = head->prev;
	new->prev = last;
	new->next = head;
	last->next = new;
	head->prev = new;
}


static Inst *
add_inst(TranslationState *ts, InstKind kind, int subkind)
{
	Inst *new = create_inst(ts->arena, kind, subkind);
	add_inst_(ts, new);
	return new;
}

static void
add_copy(TranslationState *ts, Oper dest, Oper src)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV);
	inst->mode = M_Cr;
	IREG1(inst) = dest;
	IREG2(inst) = src;
}

static void
add_load(TranslationState *ts, Oper dest, Oper addr)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV);
	inst->mode = M_CM;
	IREG(inst) = dest;
	IBASE(inst) = addr;
}

static void
add_store(TranslationState *ts, Oper addr, Oper value)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV);
	inst->mode = M_Mr;
	IREG(inst) = value;
	IBASE(inst) = addr;
}

static void
add_lea(TranslationState *ts, Oper dest, Oper base, Oper disp)
{
	Inst *inst = add_inst(ts, IK_MOV, LEA);
	inst->mode = M_CM;
	IREG(inst) = dest;
	IBASE(inst) = base;
	IDISP(inst) = disp;
}

static void
add_lea_label(TranslationState *ts, Oper dest, Oper label)
{
	Inst *inst = add_inst(ts, IK_MOV, LEA);
	inst->mode = M_CM;
	IREG(inst) = dest;
	IBASE(inst) = R_NONE;
	ILABEL(inst) = label;
}

static void
add_mov_imm(TranslationState *ts, Oper dest, u64 imm)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV);
	inst->mode = M_CI;
	IREG(inst) = dest;
	set_imm64(inst, imm);
}

static void
add_set_zero(TranslationState *ts, Oper oper)
{
	// Set zero with `mov` so that we don't introduce additional constraints
	// on the register through XOR register uses.
	// TODO: xor oper, oper
	Inst *inst = add_inst(ts, IK_MOV, MOV);
	inst->mode = M_CI;
	IREG(inst) = oper;
	set_imm64(inst, 0);
}

static void
add_unop(TranslationState *ts, X86Group3 op, Oper op1)
{
	Inst *inst = add_inst(ts, IK_UNALU, op);
	inst->mode = M_R;
	inst->writes_flags = true;
	IREG(inst) = op1;
}

static void
add_binop(TranslationState *ts, X86Group1 op, Oper op1, Oper op2)
{
	Inst *inst = add_inst(ts, IK_BINALU, op);
	inst->mode = M_Rr;
	inst->writes_flags = true;
	IREG1(inst) = op1;
	IREG2(inst) = op2;
}

static void
add_cmp(TranslationState *ts, X86Group1 op, Oper op1, Oper op2)
{
	Inst *inst = add_inst(ts, IK_BINALU, op);
	inst->mode = M_rr;
	inst->writes_flags = true;
	IREG1(inst) = op1;
	IREG2(inst) = op2;
}

static void
add_shift(TranslationState *ts, X86Group2 op, Oper op1, Oper op2)
{
	Inst *inst = add_inst(ts, IK_SHIFT, op);
	inst->mode = M_Rr;
	inst->writes_flags = true;
	IREG1(inst) = op1;
	IREG2(inst) = op2;
	assert(op2 == R_RCX);
}

static void
add_push(TranslationState *ts, Oper oper)
{
	Inst *inst = add_inst(ts, IK_PUSH, 0);
	inst->mode = M_r;
	IREG(inst) = oper;
}

static void
add_pop(TranslationState *ts, Oper oper)
{
	Inst *inst = add_inst(ts, IK_POP, 0);
	inst->mode = M_C;
	IREG(inst) = oper;
}

static void
add_setcc(TranslationState *ts, CondCode cc, Oper oper)
{
	Inst *inst = add_inst(ts, IK_SETCC, cc);
	inst->mode = M_R; // partial register read
	inst->reads_flags = true;
	IREG(inst) = oper;
}

static void
add_imul3(TranslationState *ts, Oper dest, Oper arg, Oper imm)
{
	Inst *inst = add_inst(ts, IK_IMUL3, 0);
	inst->mode = M_Cri;
	inst->writes_flags = true;
	IREG(inst) = dest;
	IREG2(inst) = arg;
	IIMM(inst) = imm;
}

static void
add_jmp(TranslationState *ts, Oper block_index)
{
	Inst *inst = add_inst(ts, IK_JUMP, 0);
	inst->mode = M_L;
	ILABEL(inst) = block_index;
}

static void
add_jcc(TranslationState *ts, CondCode cc, Oper block_index)
{
	Inst *inst = add_inst(ts, IK_JCC, cc);
	inst->mode = M_L;
	inst->reads_flags = true;
	ILABEL(inst) = block_index;
}

static void
add_call(TranslationState *ts, Oper function_reg, Oper arg_cnt)
{
	Inst *inst = add_inst(ts, IK_CALL, 0);
	inst->mode = M_rCALL;
	IREG(inst) = function_reg;
	IARG_CNT(inst) = arg_cnt;
}

static Inst *
add_entry(TranslationState *ts, Oper arg_cnt)
{
	Inst *inst = add_inst(ts, IK_ENTRY, 0);
	inst->mode = M_ENTRY;
	IARG_CNT(inst) = arg_cnt;
	return inst;
}

static void
add_cqo(TranslationState *ts)
{
	Inst *inst = add_inst(ts, IK_CQO, 0);
	inst->mode = M_AD;
}

static void
translate_call(TranslationState *ts, Oper res, Oper fun, Oper *args, size_t arg_cnt)
{
	// TODO: struct arguments
	size_t gpr_index = 0;
	for (size_t i = 0; gpr_index < ARRAY_LEN(argument_regs) - 1 && i < arg_cnt; i++) {
		add_copy(ts, argument_regs[gpr_index], args[i]);
		gpr_index++;
	}
	for (size_t i = arg_cnt; i > ARRAY_LEN(argument_regs) - 1; i--) {
		add_push(ts, args[i - 1]);
	}
	add_call(ts, fun, gpr_index);
	add_copy(ts, res, R_RAX);
}

static Inst *
add_load_with_disp(TranslationState *ts, Oper dest, Oper addr, Oper disp)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV);
	inst->mode = M_CM;
	IREG(inst) = dest;
	IBASE(inst) = addr;
	IDISP(inst) = disp;
	return inst;
}

static Inst *
create_store_with_disp(TranslationState *ts, Oper dest, Oper addr, Oper disp)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV);
	inst->mode = M_Mr;
	IREG(inst) = dest;
	IBASE(inst) = addr;
	IDISP(inst) = disp;
	return inst;
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
	// how much stack space to reserve yet, we will replace the dummy '0'
	// with proper stack space requirement after register allocation. Note
	// that due to constraints of encoding of this instruction, we can't
	// address stack frame larger than 2 GiB (32 bit signed relative
	// offfset). On the x86-64 this is much bigger than the entire available
	// stack, but on other architectures where immediate offsets are
	// smaller, this may need more consideration.
	ts->make_stack_space = add_inst(ts, IK_BINALU, G1_SUB);
	Inst *inst = ts->make_stack_space;
	inst->mode = M_Ri;
	inst->writes_flags = true;
	IREG(inst) = R_RSP;
	IIMM(inst) = 0;

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
	// TODO: ret "reads" return value callee saved registers
	Inst *ret = add_inst(ts, IK_RET, 0); // TODO: subkind = calling convention?
	ret->mode = M_RET;
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
	Inst *inst = add_inst(ts, IK_MULDIV, op);
	inst->mode = M_ADr;
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

typedef struct {
	TranslationState *ts;
	Oper opers[10];
} TranslateOperandState;

size_t
add_label(GArena *labels, Value *value)
{
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

void
translate_operand(void *user_data, size_t i, Value **operand_)
{
	TranslateOperandState *tos = user_data;
	TranslationState *ts = tos->ts;
	Value *operand = *operand_;
	Oper res;
	switch (operand->kind) {
	case VK_BLOCK:
		res = operand->index;
		break;
	case VK_FUNCTION: {
		//Function *function = (void*) operand;
		size_t label_index = add_label(ts->labels, operand);
		res = tos->ts->index++;
		add_lea_label(tos->ts, res, label_index);
		break;
	}
	case VK_GLOBAL: {
		//Global *global = (void*) operand;
		res = tos->ts->index++;
		size_t label_index = add_label(ts->labels, operand);
		add_lea_label(tos->ts, res, label_index);
		break;
	}
	case VK_CONSTANT: {
		Constant *k = (void*) operand;
		res = tos->ts->index++;
		add_mov_imm(tos->ts, res, k->k);
		break;
	}
	case VK_ALLOCA: {
		Alloca *alloca = (Alloca *) operand;
		res = tos->ts->index++;
		add_lea(tos->ts, res, R_RBP, - 8 - alloca->size);
		break;
	}
	default:
		res = operand->index;
		break;
	}
	tos->opers[i] = res;
}

void
translate_value(TranslationState *ts, Value *v)
{
	TranslateOperandState tos_;
	TranslateOperandState *tos = &tos_;
	tos->ts = ts;
	if (v->kind == VK_PHI) {
		// Don't translate phi nor its operands -- they are handled in
		// the predecessors.
		return;
	}
	fprintf(stderr, "Translating: ");
	print_value(stderr, v);
	for_each_operand(v, translate_operand, tos);
	Oper *ops = &tos->opers[0];
	//Oper res = ts->index++;
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
		alloca->size = ts->stack_space;
		ts->stack_space += size;
		break;
	}
	case VK_CONSTANT:
	case VK_BLOCK:
	case VK_FUNCTION:
	case VK_GLOBAL:
	case VK_ARGUMENT:
		UNREACHABLE();
		break;

	case VK_ADD:
		translate_binop(ts, G1_ADD, res, ops[0], ops[1]);
		break;
	case VK_SUB:
		translate_binop(ts, G1_SUB, res, ops[0], ops[1]);
		break;
	case VK_MUL:
		translate_binop(ts, G1_IMUL, res, ops[0], ops[1]);
		break;
	case VK_UDIV:
		translate_div(ts, res, ops[0], ops[1], SK_UNSIGNED, DR_QUOTIENT);
		break;
	case VK_SDIV:
		translate_div(ts, res, ops[0], ops[1], SK_SIGNED, DR_QUOTIENT);
		break;
	case VK_UREM:
		translate_div(ts, res, ops[0], ops[1], SK_UNSIGNED, DR_REMAINDER);
		break;
	case VK_SREM:
		translate_div(ts, res, ops[0], ops[1], SK_SIGNED, DR_REMAINDER);
		break;
	case VK_AND:
		translate_binop(ts, G1_AND, res, ops[0], ops[1]);
		break;
	case VK_OR:
		translate_binop(ts, G1_OR, res, ops[0], ops[1]);
		break;
	case VK_SHL:
		translate_shift(ts, G2_SHL, res, ops[0], ops[1]);
		break;
	case VK_SAR:
		translate_shift(ts, G2_SAR, res, ops[0], ops[1]);
		break;
	case VK_SLR:
		translate_shift(ts, G2_SHR, res, ops[0], ops[1]);
		break;
	case VK_NEG:
		translate_unop(ts, G3_NEG, res, ops[0]);
		break;
	case VK_NOT:
		translate_unop(ts, G3_NOT, res, ops[0]);
		break;
	case VK_EQ:
		translate_cmpop(ts, CC_E, res, ops[0], ops[1]);
		break;
	case VK_NEQ:
		translate_cmpop(ts, CC_NE, res, ops[0], ops[1]);
		break;
	case VK_SLT:
		translate_cmpop(ts, CC_L, res, ops[0], ops[1]);
		break;
	case VK_SLEQ:
		translate_cmpop(ts, CC_LE, res, ops[0], ops[1]);
		break;
	case VK_SGT:
		translate_cmpop(ts, CC_G, res, ops[0], ops[1]);
		break;
	case VK_SGEQ:
		translate_cmpop(ts, CC_GE, res, ops[0], ops[1]);
		break;
	case VK_ULT:
		translate_cmpop(ts, CC_B, res, ops[0], ops[1]);
		break;
	case VK_ULEQ:
		translate_cmpop(ts, CC_BE, res, ops[0], ops[1]);
		break;
	case VK_UGT:
		translate_cmpop(ts, CC_A, res, ops[0], ops[1]);
		break;
	case VK_UGEQ:
		translate_cmpop(ts, CC_AE, res, ops[0], ops[1]);
		break;

	case VK_LOAD:
		add_load(ts, res, ops[0]);
		break;
	case VK_STORE:
		add_store(ts, ops[0], ops[1]);
		break;
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
		Operation *call = (void *) v;
		size_t arg_cnt = type_function_param_cnt(call->operands[0]->type);
		translate_call(ts, res, ops[0], &ops[1], arg_cnt);
		break;
	}
	case VK_JUMP: {
		Block *current = ts->block->block;
		Block *succ = (Block *) ((Operation *) v)->operands[0];
		size_t pred_index = block_index_of_pred(succ, current);
		size_t i = 0;
		FOR_EACH_PHI_IN_BLOCK(succ, phi) {
			// TODO: save the phi operands somewhere else
			translate_operand(tos, 9, &phi->operands[pred_index]);
			add_copy(ts, ops[i++] = ts->index++, ops[9]);
		}
		i = 0;
		FOR_EACH_PHI_IN_BLOCK(succ, phi) {
			add_copy(ts, VINDEX(phi), ops[i++]);
		}
		add_jmp(ts, succ->base.index);
		break;
	}
	case VK_BRANCH:
		add_cmp(ts, G1_TEST, ops[0], ops[0]);
		add_jcc(ts, CC_Z, ops[2]);
		add_jmp(ts, ops[1]);
		break;
	case VK_RET:
		translate_return(ts, &ops[0]);
		break;
	case VK_RETVOID:
		translate_return(ts, NULL);
		break;
	case VK_PHI: {
		// Nothing to do. We translate phis in jumps from predecessors.
		break;
	}
	}
}

typedef struct RegAllocState RegAllocState;

typedef struct {
	size_t n;
	size_t N;
	u8 *matrix;

	GArena *adj_list;
} InterferenceGraph;

void
ig_grow(InterferenceGraph *ig, size_t old_capacity, size_t new_capacity)
{
	if (old_capacity >= new_capacity) {
		return;
	}
	GROW_ARRAY(ig->matrix, new_capacity * new_capacity);
	GROW_ARRAY(ig->adj_list, new_capacity);
	ZERO_ARRAY(&ig->adj_list[old_capacity], new_capacity - old_capacity);
}

void
ig_reset(InterferenceGraph *ig, size_t size)
{
	ig->n = size;
	ig->N = size * size;
	ZERO_ARRAY(ig->matrix, ig->N);
	for (size_t i = 0; i < size; i++) {
		garena_restore(&ig->adj_list[i], 0);
	}
}

void
ig_free(InterferenceGraph *ig, size_t capacity)
{
	FREE_ARRAY(ig->matrix, capacity * capacity);
	for (size_t i = 0; i < capacity; i++) {
		garena_free(&ig->adj_list[i]);
	}
	FREE_ARRAY(ig->adj_list, capacity);
}

bool
ig_interfere(InterferenceGraph *ig, Oper op1, Oper op2)
{
	if (op1 == R_NONE || op2 == R_NONE) {
		return true;
	}
	u8 one = ig->matrix[op1 * ig->n + op2];
	u8 two = ig->matrix[op2 * ig->n + op1];
	assert(one == two);
	return one;
}

void
print_mfunction(FILE *f, MFunction *mfunction)
{
	print_str(f, mfunction->func->name);
	fprintf(f, ":\n");
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		fprintf(f, ".BB%zu:\n", mblock->block->base.index);
		for (Inst *inst = mblock->insts.next; inst != &mblock->insts; inst = inst->next) {
			fprintf(f, "\t");
			print_inst(f, mfunction, inst);
			fprintf(f, "\n");
		}
	}
}

struct RegAllocState {
	Arena *arena;
	MFunction *mfunction;
	size_t vreg_capacity;
	size_t block_capacity;
	size_t move_capacity;

	// Parameters
	size_t reg_avail;

	// Final register allocation
	Oper *reg_assignment;

	u8 *to_spill;
	Oper *alias;

	// Spill cost related
	u8 *def_count;
	u8 *use_count;
	u8 *unspillable;

	// Degrees of nodes.
	u32 *degree;

	InterferenceGraph ig;
	WorkList live_set;
	WorkList uninterrupted;
	u8 *ever_interrupted;
	WorkList block_work_list;
	WorkList *live_in;

	// Worklists for the different register allocation phases
	WorkList spill_wl;
	WorkList freeze_wl;
	WorkList simplify_wl;
	WorkList moves_wl;
	WorkList active_moves_wl;
	WorkList stack;

	GArena gmoves; // Array of Inst *
	GArena *move_list; // Array of GArena of Oper
};

void
reg_alloc_state_init(RegAllocState *ras, Arena *arena)
{
	*ras = (RegAllocState) {
		.arena = arena,
		.reg_avail = 14,
	};
}

void
reg_alloc_state_reset(RegAllocState *ras)
{
	assert(ras->mfunction->vreg_cnt > 0);
	size_t old_vreg_capacity = ras->vreg_capacity;
	if (ras->vreg_capacity == 0) {
		ras->vreg_capacity = 64;
	}
	while (ras->vreg_capacity < ras->mfunction->vreg_cnt) {
		ras->vreg_capacity += ras->vreg_capacity;
	}
	size_t old_block_capacity = ras->block_capacity;
	if (ras->block_capacity == 0) {
		ras->block_capacity = 16;
	}
	while (ras->block_capacity < ras->mfunction->mblock_cnt) {
		ras->block_capacity += ras->block_capacity;
	}

	if (old_block_capacity < ras->block_capacity) {
		wl_grow(&ras->block_work_list, ras->block_capacity);
		GROW_ARRAY(ras->live_in, ras->block_capacity);
		ZERO_ARRAY(&ras->live_in[old_block_capacity], ras->block_capacity - old_block_capacity);
		for (size_t i = old_block_capacity; i < ras->block_capacity; i++) {
			wl_grow(&ras->live_in[i], ras->vreg_capacity);
		}
	}

	if (old_vreg_capacity < ras->vreg_capacity) {
		GROW_ARRAY(ras->reg_assignment, ras->vreg_capacity);
		GROW_ARRAY(ras->to_spill, ras->vreg_capacity);
		GROW_ARRAY(ras->alias, ras->vreg_capacity);
		GROW_ARRAY(ras->def_count, ras->vreg_capacity);
		GROW_ARRAY(ras->use_count, ras->vreg_capacity);
		GROW_ARRAY(ras->unspillable, ras->vreg_capacity);
		GROW_ARRAY(ras->degree, ras->vreg_capacity);
		ig_grow(&ras->ig, old_vreg_capacity, ras->vreg_capacity);
		wl_grow(&ras->live_set, ras->vreg_capacity);
		wl_grow(&ras->uninterrupted, ras->vreg_capacity);
		GROW_ARRAY(ras->ever_interrupted, ras->vreg_capacity);
		for (size_t i = 0; i < old_block_capacity; i++) {
			wl_grow(&ras->live_in[i], ras->vreg_capacity);
		}
		wl_grow(&ras->spill_wl, ras->vreg_capacity);
		wl_grow(&ras->freeze_wl, ras->vreg_capacity);
		wl_grow(&ras->simplify_wl, ras->vreg_capacity);
		//wl_grow(&ras->moves_wl, ras->vreg_capacity);
		//wl_grow(&ras->active_moves_wl, ras->vreg_capacity);
		wl_grow(&ras->stack, ras->vreg_capacity);
		// gmoves doesn't need to grow
		GROW_ARRAY(ras->move_list, ras->vreg_capacity);
		ZERO_ARRAY(&ras->move_list[old_vreg_capacity], ras->vreg_capacity - old_vreg_capacity);
	}

	ZERO_ARRAY(ras->reg_assignment, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->to_spill, ras->mfunction->vreg_cnt);
	for (size_t i = 0; i < ras->mfunction->vreg_cnt; i++) {
		ras->alias[i] = i;
	}
	ZERO_ARRAY(ras->def_count, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->use_count, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->unspillable, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->degree, ras->mfunction->vreg_cnt);
	ig_reset(&ras->ig, ras->mfunction->vreg_cnt);
	wl_reset(&ras->live_set);
	wl_reset(&ras->uninterrupted);
	ZERO_ARRAY(ras->ever_interrupted, ras->vreg_capacity);
	wl_reset(&ras->block_work_list);
	for (size_t i = 0; i < ras->mfunction->mblock_cnt; i++) {
		wl_reset(&ras->live_in[i]);
	}
	wl_reset(&ras->spill_wl);
	wl_reset(&ras->freeze_wl);
	wl_reset(&ras->simplify_wl);
	//wl_reset(&ras->moves_wl);
	//wl_reset(&ras->active_moves_wl);
	wl_reset(&ras->stack);
	garena_restore(&ras->gmoves, 0);
	for (size_t i = 0; i < ras->mfunction->vreg_cnt; i++) {
		garena_restore(&ras->move_list[i], 0);
	}
}

void
reg_alloc_state_free(RegAllocState *ras)
{
	FREE_ARRAY(ras->reg_assignment, ras->vreg_capacity);
	FREE_ARRAY(ras->to_spill, ras->vreg_capacity);
	FREE_ARRAY(ras->alias, ras->vreg_capacity);
	FREE_ARRAY(ras->def_count, ras->vreg_capacity);
	FREE_ARRAY(ras->use_count, ras->vreg_capacity);
	FREE_ARRAY(ras->unspillable, ras->vreg_capacity);
	FREE_ARRAY(ras->degree, ras->vreg_capacity);
	ig_free(&ras->ig, ras->vreg_capacity);
	wl_free(&ras->live_set);
	wl_free(&ras->uninterrupted);
	FREE_ARRAY(ras->ever_interrupted, ras->vreg_capacity);
	wl_reset(&ras->block_work_list);
	wl_free(&ras->block_work_list);
	for (size_t i = 0; i < ras->block_capacity; i++) {
		wl_free(&ras->live_in[i]);
	}
	FREE_ARRAY(ras->live_in, ras->block_capacity);
	wl_free(&ras->spill_wl);
	wl_free(&ras->freeze_wl);
	wl_free(&ras->simplify_wl);
	wl_free(&ras->moves_wl);
	wl_free(&ras->active_moves_wl);
	wl_free(&ras->stack);
	garena_free(&ras->gmoves);
	for (size_t i = 0; i < ras->vreg_capacity; i++) {
		garena_free(&ras->move_list[i]);
	}
	FREE_ARRAY(ras->move_list, ras->vreg_capacity);
}

void
reg_alloc_state_init_for_function(RegAllocState *ras, MFunction *mfunction)
{
	ras->mfunction = mfunction;
	//reg_alloc_state_reset(ras);
}

bool
is_alias(RegAllocState *ras, Oper u)
{
	return ras->alias[u] != u;
}

Oper
get_alias(RegAllocState *ras, Oper u)
{
	while (u != ras->alias[u]) {
		u = ras->alias[u];
	}
	return u;
}

void
ig_add(InterferenceGraph *ig, Oper op1, Oper op2)
{
	assert(op1 < ig->n);
	assert(op2 < ig->n);
	if (op1 == op2 || ig_interfere(ig, op1, op2)) {
		return;
	}
	fprintf(stderr, "Adding interference ");
	print_reg(stderr, op1);
	fprintf(stderr, " ");
	print_reg(stderr, op2);
	fprintf(stderr, "\n");
	assert(ig->matrix[op1 * ig->n + op2] == 0);
	assert(ig->matrix[op2 * ig->n + op1] == 0);
	ig->matrix[op1 * ig->n + op2] = 1;
	ig->matrix[op2 * ig->n + op1] = 1;
	if (op1 >= R__MAX) {
		garena_push_value(&ig->adj_list[op1], Oper, op2);
	}
	if (op2 >= R__MAX) {
		garena_push_value(&ig->adj_list[op2], Oper, op1);
	}
	// TODO: Restructure Interefrence graph and Register allocation state.
	RegAllocState *ras = container_of(ig, RegAllocState, ig);
	ras->degree[op1]++;
	ras->degree[op2]++;
}


void
get_live_out(RegAllocState *ras, Block *block, WorkList *live_set)
{
	// live-out of this block is the union of live-ins of all
	// successors
	wl_reset(live_set);
	FOR_EACH_BLOCK_SUCC(block, succ) {
		wl_union(live_set, &ras->live_in[(*succ)->mblock->index]);
	}
}


void
for_each_def(Inst *inst, void (*fun)(void *user_data, Oper *def), void *user_data)
{
	InsFormat *mode = &formats[inst->mode];
	for (size_t i = mode->def_start; i < mode->def_end; i++) {
		fun(user_data, &inst->ops[i]);
	}
	if (mode->def_cnt_given_by_arg_cnt) {
		size_t def_cnt = IARG_CNT(inst);
		for (size_t i = 0; i < def_cnt; i++) {
			fun(user_data, &mode->extra_defs[i]);
		}
	} else {
		for (Oper *def = mode->extra_defs; *def != R_NONE; def++) {
			fun(user_data, def);
		}
	}
}

void
for_each_use(Inst *inst, void (*fun)(void *user_data, Oper *use), void *user_data)
{
	InsFormat *mode = &formats[inst->mode];
	for (size_t i = mode->use_start; i < mode->use_end; i++) {
		fun(user_data, &inst->ops[i]);
	}
	if (mode->use_cnt_given_by_arg_cnt) {
		size_t use_cnt = IARG_CNT(inst);
		for (size_t i = 0; i < use_cnt; i++) {
			fun(user_data, &mode->extra_uses[i]);
		}
	} else {
		for (Oper *use = mode->extra_uses; *use != R_NONE; use++) {
			fun(user_data, use);
		}
	}
}

void
remove_from_set(void *user_data, Oper *oper)
{
	WorkList *live_set = user_data;
	fprintf(stderr, "Removing from live ");
	print_reg(stderr, *oper);
	fprintf(stderr, "\n");
	wl_remove(live_set, *oper);
}

void
add_to_set(void *user_data, Oper *oper)
{
	WorkList *live_set = user_data;
	fprintf(stderr, "Adding to live ");
	print_reg(stderr, *oper);
	fprintf(stderr, "\n");
	wl_add(live_set, *oper);
}

void
live_step(WorkList *live_set, MFunction *mfunction, Inst *inst)
{
	fprintf(stderr, "Live step at\t");
	print_inst(stderr, mfunction, inst);
	fprintf(stderr, "\n");
	// Remove definitions from live.
	for_each_def(inst, remove_from_set, live_set);
	// Add uses to live.
	for_each_use(inst, add_to_set, live_set);
}

typedef struct {
	InterferenceGraph *ig;
	Oper live;
} InterferenceState;

void
add_interference_with(void *user_data, Oper *oper)
{
	InterferenceState *is = user_data;
	ig_add(is->ig, *oper, is->live);
}

void
interference_step(RegAllocState *ras, WorkList *live_set, Inst *inst)
{
	InterferenceGraph *ig = &ras->ig;

	// Special handling of moves:
	// 1) We don't want to introduce interference between move source and
	//    destination.
	// 2) We want to note all moves and for all nodes the moves they are
	//    contained in, because we want to try to coalesce the moves later.
	if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Cr) {
		// Remove uses from live to prevent interference between move
		// destination and source.
		for_each_use(inst, remove_from_set, live_set);

		// Accumulate moves.
		size_t index = garena_cnt(&ras->gmoves, Inst *);
		garena_push_value(&ras->gmoves, Inst *, inst);
		garena_push_value(&ras->move_list[inst->ops[0]], Oper, index);
		garena_push_value(&ras->move_list[inst->ops[1]], Oper, index);
	}


	// Add all definitions to live. Because the next step adds
	// interferences between all definitions and all live, we will thus also
	// make all the definitions interfere with each other. Since the
	// liveness step (run after us) removes all definitions, this is OK and
	// local to the current instruction.
	for_each_def(inst, add_to_set, live_set);

	// Add interferences of all definitions with all live.
	InterferenceState is = { .ig = ig };
	FOR_EACH_WL_INDEX(live_set, j) {
		is.live = live_set->dense[j];
		for_each_def(inst, add_interference_with, &is);
	}
}

typedef struct {
	RegAllocState *ras;
	Inst *inst;
	Oper spill_start;
} SpillState;

Oper
get_fresh_vreg_for_spill(RegAllocState *ras)
{
	Oper vreg = ras->mfunction->vreg_cnt++;
	// If we get out of capacity, reserve 3 times that much in the spill
	// array, just so we can progress. The rest of the data structures are
	// only needed in the second reg alloc try, which resets and reallocates
	// them. This still doesn' guarantee, that we won't get out of vregs,
	// because we don't bump the capacity, but at that point, there should
	// be a better solution altogether.
	if (vreg == ras->vreg_capacity) {
		GROW_ARRAY(ras->to_spill, ras->vreg_capacity * 4);
	}
	assert(vreg != 4 * ras->vreg_capacity);
	return vreg;
}

bool
is_to_be_spilled(SpillState *ss, Oper t)
{
	// NOTE: We make sure that even `to_spill` is in bounds even for vregs
	// introduced for spill code, see `get_fresh_vreg_for_spill` above.
	return ss->ras->to_spill[t];
}

void
insert_loads_of_spilled(void *user_data, Oper *src)
{
	SpillState *ss = user_data;
	RegAllocState *ras = ss->ras;
	if (!is_to_be_spilled(ss, *src)) {
		return;
	}
	Inst *inst = ss->inst;

	Oper temp = get_fresh_vreg_for_spill(ras);
	ras->to_spill[temp] = ras->to_spill[*src];
	fprintf(stderr, "load ");
	print_reg(stderr, *src);
	fprintf(stderr, " through ");
	print_reg(stderr, temp);
	Inst *load = create_inst(ras->arena, IK_MOV, MOV);
	//Inst *load = make_inst(ras->arena, OP_MOV_RMC, temp, R_RBP, 8 + ras->to_spill[src]);
	load->mode = M_CM;
	load->prev = inst->prev;
	load->next = inst;
	IREG(load) = temp;
	IBASE(load) = R_RBP;
	IDISP(load) = - 8 - ras->to_spill[*src];

	inst->prev->next = load;
	inst->prev = load;

	*src = temp;
}

void
insert_stores_of_spilled(void *user_data, Oper *dest)
{
	SpillState *ss = user_data;
	RegAllocState *ras = ss->ras;
	if (!is_to_be_spilled(ss, *dest)) {
		return;
	}
	Inst *inst = ss->inst;

	// If the "to be spilled" register has actually been introduced only
	// after we started spilling (i.e. it is bigger than `spill_start`, then
	// we actually have a definition of a use in this same instruction.
	// Think:
	//
	//    add t20, t21
	//
	// If use of t20 has been spilled through t30, and we have:
	//
	//    mov t30, [rbp+t20]
	//    add t30, t21
	//
	// Then we need to store t30 and not introduce a new vreg:
	//
	//    mov t30, [rbp+t20]
	//    add t30, t21
	//    mov [rbp+t20], t30
	//
	// Of course at that point we could also have:
	//
	//    add [rbp+t20], t21
	//
	// But:
	//  1) that is the business of the instruction selection,
	//  2) it may be actually worse, depending on the surrounding code.
	//
	// For example if we originally had:
	//
	//    mov t20, t22
	//    add t20, t21
	//
	// Then we don't want store followed immediately by a load:
	//
	//    mov [rbp+t20], t22
	//    add [rbp+t20], t21
	//
	// But instead we would want:
	//
	//    mov t30, t22
	//    add t30, t21
	//    mov [rbp+t20], t30
	//
	Oper temp;
	if (*dest >= ss->spill_start) {
		temp = *dest;
	} else {
		temp = get_fresh_vreg_for_spill(ras);
	}
	fprintf(stderr, "store ");
	print_reg(stderr, *dest);
	fprintf(stderr, " through ");
	print_reg(stderr, temp);
	fprintf(stderr, "\n");

	//Inst *store = make_inst(ras->arena, OP_MOV_MCR, R_RBP, temp, 8 + ras->to_spill[dest]);
	Inst *store = create_inst(ras->arena, IK_MOV, MOV);
	store->mode = M_Mr;
	store->prev = inst;
	store->next = inst->next;
	IREG(store) = temp;
	IBASE(store) = R_RBP;
	IDISP(store) = - 8 - ras->to_spill[*dest];

	inst->next->prev = store;
	inst->next = store;
	inst = inst->next;

	*dest = temp;
}

// Add spill code, coalesce registers that were found to be coalescable before
// the first potential spill.
void
rewrite_program(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	SpillState ss_ = {
		.ras = ras,
		.spill_start = mfunction->vreg_cnt,
	}, *ss = &ss_;
	print_mfunction(stderr, mfunction);
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		for (Inst *inst = mblock->insts.next; inst != &mblock->insts; inst = inst->next) {
			ss->inst = inst;
			fprintf(stderr, "\n");
			print_inst(stderr, mfunction, inst);
			fprintf(stderr, "\n");
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Cr) {
				Oper dest = inst->ops[0];
				Oper src = inst->ops[1];
				bool spill_dest = is_to_be_spilled(ss, dest);
				bool spill_src = is_to_be_spilled(ss, src);
				if (spill_dest && spill_src) {
					// If this would be essentially:
					//    mov [rbp+X], [rbp+X]
					// we can just get rid of the copy.
					assert(false);
					if (ras->to_spill[dest] == ras->to_spill[src]) {
						inst->prev->next = inst->next;
						inst->next->prev = inst->prev;
					}
				} else if (spill_dest) {
					inst->mode = M_Mr;
					IREG(inst) = src;
					IBASE(inst) = R_RBP;
					IDISP(inst) = - 8 - ras->to_spill[dest];
				} else if (spill_src) {
					inst->mode = M_CM;
					IREG(inst) = dest;
					IBASE(inst) = R_RBP;
					IDISP(inst) = - 8 - ras->to_spill[src];
				}
				continue;
			}
			//print_inst_d(stderr, inst);
			//fprintf(stderr, "\n");
			// Add loads for all spilled uses.
			for_each_use(inst, insert_loads_of_spilled, ss);
			// Add stores for all spilled defs.
			for_each_def(inst, insert_stores_of_spilled, ss);
		}
	}
	print_mfunction(stderr, mfunction);
}

void
apply_reg_assignment(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		for (Inst *inst = mblock->insts.next; inst != &mblock->insts; inst = inst->next) {
			// TODO: different number of register slots per target
			// TODO: store number of registers in mode
			InsFormat *mode = &formats[inst->mode];
			size_t end = mode->use_end > mode->def_end ? mode->use_end : mode->def_end;
			for (size_t i = 0; i < end; i++) {
				inst->ops[i] = ras->reg_assignment[get_alias(ras, inst->ops[i])];
			}
		}
	}
}

typedef struct {
	GArena *uses;
	Value *current;
} GetUsesState;

void
add_uses(void *user_data, size_t i, Value **operand_)
{
	GetUsesState *gus = user_data;
	Value *operand = *operand_;
	if (operand->index == 0) {
		return;
	}
	garena_push_value(&gus->uses[operand->index], Value *, gus->current);
}

void
get_uses(Function *function)
{
	GROW_ARRAY(function->uses, function->value_cnt);
	ZERO_ARRAY(function->uses, function->value_cnt);
	GetUsesState gus = {
		.uses = function->uses,
	};
	for (size_t b = 0; b < function->block_cnt; b++) {
		Block *block = function->post_order[b];
		FOR_EACH_IN_BLOCK(block, v) {
			gus.current = v;
			for_each_operand(v, add_uses, &gus);
		}
	}
}

void
free_uses(Function *function)
{
	for (size_t i = 0; i < function->value_cnt; i++) {
		garena_free(&function->uses[i]);
	}
	free(function->uses);
}

void
mem2reg(Function *function)
{
	Block *entry = function->entry;
	FOR_EACH_IN_BLOCK(entry, v) {
		if (v->kind != VK_ALLOCA) {
			continue;
		}
		Alloca *alloca = (void *) v;
		Value **uses = garena_array(&function->uses[v->index], Value *);
		size_t use_cnt = garena_cnt(&function->uses[v->index], Value *);
		print_value(stderr, v);
		for (size_t i = 0; i < use_cnt; i++) {
			Value *use = uses[i];
			if (VK(use) == VK_STORE && STORE_ADDR(use) == v && STORE_VALUE(use) != v) {
				continue;
			}
			if (VK(use) == VK_LOAD && LOAD_ADDR(use) == v) {
				continue;
			}
			alloca->optimizable = false;
		}
	}
}

bool
is_optimizable_alloca(Value *v)
{
	return VK(v) == VK_ALLOCA && ((Alloca *) v)->optimizable;
}

typedef struct {
	Arena *arena;
	Function *function;
	Value ***var_map;
	Value **canonical;
} ValueNumberingState;

Value *read_variable(ValueNumberingState *vns, Block *block, Value *variable);

void
add_phi_operands(ValueNumberingState *vns, Operation *phi, Block *block, Value *variable)
{
	size_t i = 0;
	FOR_EACH_BLOCK_PRED(block, pred) {
		phi->operands[i++] = read_variable(vns, *pred, variable);
	}
}

typedef struct {
	Operation *phi;
	Value *variable;
} IncompletePhi;

void
write_variable(ValueNumberingState *vns, Block *block, Value *variable, Value *value)
{
	fprintf(stderr, "Writing var %zu from block %zu with value %zu\n", VINDEX(variable), VINDEX(block), VINDEX(value));
	vns->var_map[VINDEX(block)][VINDEX(variable)] = value;
}

Value *
read_variable(ValueNumberingState *vns, Block *block, Value *variable)
{
	fprintf(stderr, "Reading var %zu from block %zu\n", VINDEX(variable), VINDEX(block));
	assert(!block->pending);
	Value *value = vns->var_map[VINDEX(block)][VINDEX(variable)];
	if (value) {
		fprintf(stderr, "Have locally %zu\n", VINDEX(value));
	} else if (block->filled_pred_cnt != block_pred_cnt(block)) {
		fprintf(stderr, "Not sealed\n");
		assert(block_pred_cnt(block) > 1);
		// Not all predecessors are filled yet. We only insert a phi,
		// but initialize it later, when sealing, because only then we
		// actually can read from all predecessors.
		IncompletePhi phi = {
			.phi = insert_phi(vns->arena, block, pointer_child(variable->type)),
			.variable = variable,
		};
		garena_push_value(&block->incomplete_phis, IncompletePhi, phi);
		value = &phi.phi->base;
	} else if (block_pred_cnt(block) == 1) {
		fprintf(stderr, "Single pred\n");
		Block *pred = block_preds(block)[0];
		value = read_variable(vns, pred, variable);
	} else {
		fprintf(stderr, "Merge\n");
		// We already filled all predecessors.
		block->pending = true;
		Operation *phi = insert_phi(vns->arena, block, pointer_child(variable->type));
		add_phi_operands(vns, phi, block, variable);
		block->pending = false;
		value = &phi->base;
	}
	// Memoize
	write_variable(vns, block, variable, value);
	return value;
}

void
canonicalize(void *user_data, size_t i, Value **operand)
{
	ValueNumberingState *vns = user_data;
	Value *canonical = vns->canonical[VINDEX(*operand)];
	if (canonical) {
		*operand = canonical;
	}
}

void
seal_block(ValueNumberingState *vns, Block *block)
{
	size_t incomplete_phi_cnt = garena_cnt(&block->incomplete_phis, IncompletePhi);
	IncompletePhi *incomplete_phis = garena_array(&block->incomplete_phis, IncompletePhi);
	for (size_t i = 0; i < incomplete_phi_cnt; i++) {
		IncompletePhi *inc = &incomplete_phis[i];
		add_phi_operands(vns, inc->phi, block, inc->variable);
	}
	garena_free(&block->incomplete_phis);
}

void
value_numbering(Arena *arena, Function *function)
{
	size_t block_cnt = function->block_cnt;
	size_t value_cnt = function->value_cnt;

	ValueNumberingState vns_ = {
		.arena = arena,
		.function = function,
	}, *vns = &vns_;

	GROW_ARRAY(vns->canonical, value_cnt);
	ZERO_ARRAY(vns->canonical, value_cnt);

	GROW_ARRAY(vns->var_map, function->block_cap);
	ZERO_ARRAY(vns->var_map, function->block_cap);
	for (size_t b = 0; b < block_cnt; b++) {
		Block *block = function->post_order[b];
		GROW_ARRAY(vns->var_map[VINDEX(block)], value_cnt);
		ZERO_ARRAY(vns->var_map[VINDEX(block)], value_cnt);
	}

	seal_block(vns, function->entry);

	for (size_t b = block_cnt; b--;) {
		Block *block = function->post_order[b];
		FOR_EACH_IN_BLOCK(block, v) {
			switch (VK(v)) {
			case VK_ALLOCA:
				if (is_optimizable_alloca(v)) {
					remove_value(v);
					continue;
				}
				break;
			case VK_LOAD:
				if (is_optimizable_alloca(LOAD_ADDR(v))) {
					Value *val = read_variable(vns, block, LOAD_ADDR(v));
					vns->canonical[VINDEX(v)] = val;
					remove_value(v);
					continue;
				}
				break;
			case VK_STORE:
				if (is_optimizable_alloca(STORE_ADDR(v))) {
					write_variable(vns, block, STORE_ADDR(v), STORE_VALUE(v));
					remove_value(v);
					continue;
				}
			default:
				break;
			}
			for_each_operand(v, canonicalize, vns);
		}

		FOR_EACH_BLOCK_SUCC(block, succ) {
			if (++(*succ)->filled_pred_cnt == block_pred_cnt((*succ))) {
				seal_block(vns, (*succ));
			}
		}
	}
	FREE_ARRAY(vns->canonical, value_cnt);
	for (size_t b = 0; b < block_cnt; b++) {
		Block *block = function->post_order[b];
		FREE_ARRAY(vns->var_map[VINDEX(block)], value_cnt);
	}
	FREE_ARRAY(vns->var_map, block_cnt);
}

void
merge_simple_blocks(Arena *arena, Function *function)
{
	WorkList worklist = {0};
	size_t block_cap = 1;
	while (block_cap < function->block_cap) {
		block_cap *= 2;
	}
	wl_grow(&worklist, block_cap);
	for (size_t b = function->block_cnt; b--;) {
		Block *block = function->post_order[b];
		wl_add(&worklist, block->base.index);
	}
	Oper b;
	while (wl_take(&worklist, &b)) {
		Block *block = function->post_order[b];
		if (block_succ_cnt(block) != 1) {
			continue;
		}
		Block *succ = block_succs(block)[0];
		if (block_pred_cnt(succ) != 1) {
			continue;
		}
		// Block has one successor, and the successor has only one
		// predecessor. We can just merge the blocks together
		// and get rid of the jump.
		fprintf(stderr, "Merging block%zu with block%zu\n", block->base.index, succ->base.index);

		// Replace all references to `succ` in its successors, to point
		// to `block` instead.
		FOR_EACH_BLOCK_SUCC(succ, ssucc) {
			FOR_EACH_BLOCK_PRED(*ssucc, pred) {
				if (*pred == succ) {
					*pred = block;
					break;
				}
			}
		}

		// Successors of block are fixed up automatically, because they
		// are taken implicitly from the terminator instruction.

		FOR_EACH_IN_BLOCK(succ, v) {
			v->parent = &block->base;
		}

		// Remove the jump instruction from `block`.
		remove_value(block->base.prev);
		// Append `succ` to the `block`.
		block->base.prev->next = succ->base.next;
		succ->base.next->prev = block->base.prev;
		succ->base.prev->next = &block->base;
		block->base.prev = succ->base.prev;
		//prepend_value(&block->base, succ->base.next);
		// Remove the redundant and unwanted `succ` block header.
		//remove_value(&succ->base);

		wl_add(&worklist, b);
	}
	wl_free(&worklist);

	// Recompute function->post_order, since we invalidated it.
	compute_preorder(function);
}

void
thread_jumps(Arena *arena, Function *function)
{
	WorkList worklist = {0};
	size_t block_cap = 1;
	while (block_cap < function->block_cap) {
		block_cap *= 2;
	}
	wl_grow(&worklist, block_cap);
	for (size_t b = function->block_cnt; b--;) {
		Block *block = function->post_order[b];
		wl_add(&worklist, block->base.index);
	}
	Oper b;
	while (wl_take(&worklist, &b)) {
		Block *block = function->post_order[b];
		if (VK(block->base.next) != VK_JUMP) {
			continue;
		}
		Block *succ = block_succs(block)[0];
		// Block is empty and has only one successor. We can just
		// forward the jumps from predecessors to the successor.
		fprintf(stderr, "Threading block%zu to block%zu\n", block->base.index, succ->base.index);

		// Replace all references to `block` in its predecessors, to
		// point to `succ` instead.
		FOR_EACH_BLOCK_PRED(block, pred) {
			FOR_EACH_BLOCK_PRED(*pred, s) {
				if (*s == block) {
					*s = succ;
					break;
				}
			}
			wl_add(&worklist, (*pred)->base.index);
		}
	}
	wl_free(&worklist);

	// Recompute function->post_order, since we invalidated it.
	compute_preorder(function);
}

void
split_critical_edges(Arena *arena, Function *function)
{
	for (size_t b = function->block_cnt; b--;) {
		Block *succ = function->post_order[b];
		if (block_pred_cnt(succ) <= 1) {
			// OK.
			continue;
		}
		FOR_EACH_BLOCK_PRED(succ, pred_) {
			Block *pred = *pred_;
			if (block_succ_cnt(pred) <= 1) {
				// OK.
				continue;
			}
			// Otherwise we have a critical edge (from block to with
			// multiple successors to block with multiple
			// predecessors). We split it by introducing a new
			// block.
			fprintf(stderr, "Splitting critical edge from block%zu to block%zu\n", VINDEX(pred), VINDEX(succ));
			Block *new = create_block(arena, function);
			block_add_pred(new, pred);
			Value *jump = create_unary(arena, new, VK_JUMP, &TYPE_VOID, &succ->base);
			jump->parent = &new->base;
			jump->index = function->value_cnt++;
			prepend_value(&new->base, jump);
			FOR_EACH_BLOCK_SUCC(pred, s) {
				if (*s == succ) {
					*s = new;
				}
			}
			FOR_EACH_BLOCK_PRED(succ, p) {
				if (*p == pred) {
					*p = new;
				}
			}
		}
	}

	// Recompute function->post_order, since we invalidated it.
	compute_preorder(function);
}

typedef struct {
	Block *block;
	Value *value;
} PendingPhi;

void
single_exit(Arena *arena, Function *function)
{
	GArena gphis = {0};
	for (size_t b = function->block_cnt; b--;) {
		Block *block = function->post_order[b];
		Value *value = NULL;
		switch (VK(block->base.prev)) {
		case VK_RET:
			value = ((Operation *) block->base.prev)->operands[0];
			break;
		case VK_RETVOID:
			break;
		default:
			continue;
		}
		garena_push_value(&gphis, PendingPhi, ((PendingPhi) { .block = block, value = value }));
	}
	PendingPhi *phis = garena_array(&gphis, PendingPhi);
	size_t phi_cnt = garena_cnt(&gphis, PendingPhi);
	if (phi_cnt == 1) {
		garena_free(&gphis);
		return;
	}
	Block *ret_block = create_block(arena, function);

	bool ret_void = VK(phis[0].block->base.prev) == VK_RETVOID;

	for (size_t i = 0; i < phi_cnt; i++) {
		PendingPhi *phi = &phis[i];
		Block *pred = phi->block;
		Value *jump = create_unary(arena, pred, VK_JUMP, &TYPE_VOID, &ret_block->base);
		jump->index = function->value_cnt++;
		jump->parent = &pred->base;
		remove_value(pred->base.prev);
		prepend_value(&pred->base, jump);
		block_add_pred(ret_block, pred);
	}

	Value *ret_inst;
	if (ret_void) {
		ret_inst = &create_operation(arena, ret_block, VK_RETVOID, &TYPE_VOID, 0)->base;
	} else {
		Type *type = phis[0].value->type;
		Operation *phi = insert_phi(arena, ret_block, type);
		phi->base.index = function->value_cnt++;
		for (size_t i = 0; i < phi_cnt; i++) {
			phi->operands[i] = phis[i].value;
		}
		ret_inst = create_unary(arena, ret_block, VK_RET, &TYPE_VOID, &phi->base);
	}
	ret_inst->index = function->value_cnt++;
	ret_inst->parent = &ret_block->base;
	prepend_value(&ret_block->base, ret_inst);

	garena_free(&gphis);

	// Recompute function->post_order, since we invalidated it.
	compute_preorder(function);
}

void
mark_defs_with_uninterrupted_uses_unspillable(void *user_data, Oper *def_)
{
	RegAllocState *ras = user_data;
	Oper def = *def_;
	// Check if this definition has a following use and the live range is
	// uninterrupted by any death of other live range. Make sure that the
	// use is really uninterrupted, by checking global flag which forbids
	// interruptions.
	if (wl_remove(&ras->uninterrupted, def) && !ras->ever_interrupted[def]) {
		ras->unspillable[def] = true;
		if (def >= R__MAX) {
			fprintf(stderr, "Marking ");
			print_reg(stderr, def);
			fprintf(stderr, " as unspillable\n");
		}
	}
	// Update def count.
	ras->def_count[def] += 1;
	// Update liveness.
	wl_remove(&ras->live_set, def);
}

void
detect_interrupting_deaths(void *user_data, Oper *use_)
{
	RegAllocState *ras = user_data;
	Oper use = *use_;
	if (!wl_has(&ras->live_set, use)) {
		WorkList *uninterrupted = &ras->uninterrupted;
		FOR_EACH_WL_INDEX(uninterrupted, i) {
			Oper op = uninterrupted->dense[i];
			ras->ever_interrupted[op] = true;
		}
		wl_reset(uninterrupted);
	}
}

void
add_live(void *user_data, Oper *use_)
{
	RegAllocState *ras = user_data;
	Oper use = *use_;
	// Update use count.
	ras->use_count[use] += 1;
	// Update liveness and add note that this use is uninterrupted for now.
	wl_add(&ras->live_set, use);
	wl_add(&ras->uninterrupted, use);
}

void
calculate_spill_cost(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	WorkList *live_set = &ras->live_set;

	for (Oper b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		Block *block = mblock->block;
		get_live_out(ras, block, live_set);
		// We currently can't make unspillable those vregs whose live
		// ranges cross basic block boundaries. Make sure we don't mark
		// them unspillable by marking them as "interrupted somewhere"
		// (in this case by basic block boundary).
		FOR_EACH_WL_INDEX(live_set, i) {
			Oper live_across_block = live_set->dense[i];
			ras->ever_interrupted[live_across_block] = true;
		}
		for (Inst *inst = mblock->insts.prev; inst != &mblock->insts; inst = inst->prev) {
			for_each_def(inst, mark_defs_with_uninterrupted_uses_unspillable, ras);
			for_each_use(inst, detect_interrupting_deaths, ras);
			for_each_use(inst, add_live, ras);
		}
	}
}

MFunction *
translate_function(Arena *arena, GArena *labels, Function *function)
{
	Block **post_order = function->post_order;

	MFunction *mfunction = arena_alloc(arena, sizeof(*mfunction));
	memset(mfunction, 0, sizeof(*mfunction));
	mfunction->func = function;
	mfunction->labels = labels;
	mfunction->mblocks = arena_alloc(arena, function->block_cnt * sizeof(mfunction->mblocks[0]));
	mfunction->mblock_cnt = 0; // incremented when each block is inserted

	TranslationState ts_ = {
		.arena = arena,
		.labels = labels,
		.index = function->value_cnt,
		.stack_space = 8,
		.block = NULL,
		.function = mfunction,
	};
	TranslationState *ts = &ts_;

	for (size_t b = function->block_cnt; b--;) {
	//for (size_t j = 0; j < function->block_cnt; j++) {
		Block *block = post_order[b];
		//printf(".L%zu:\n", function->block_cnt - b - 1);
		MBlock *mblock = arena_alloc(arena, sizeof(*mblock));
		memset(mblock, 0, sizeof(*mblock));
		mfunction->mblocks[mfunction->mblock_cnt++] = mblock;
		mblock->insts.kind = IK_BLOCK;
		mblock->insts.subkind = 0;
		mblock->insts.mode = M_NONE;
		mblock->insts.next = &mblock->insts;
		mblock->insts.prev = &mblock->insts;
		mblock->block = block;
		//mblock->index = block->base.index;
		mblock->index = mfunction->mblock_cnt - 1;
		block->mblock = mblock;
		ts->block = mblock;
		if (block == function->entry) {
			translate_prologue(ts);
		}
		FOR_EACH_IN_BLOCK(block, v) {
			translate_value(ts, v);
		}
	}

	mfunction->vreg_cnt = ts->index;
	mfunction->stack_space = ts->stack_space;
	mfunction->make_stack_space = ts->make_stack_space;
	function->mfunc = mfunction;
	return mfunction;
}

void
liveness_analysis(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	WorkList *live_set = &ras->live_set;

	wl_init_all_reverse(&ras->block_work_list, mfunction->mblock_cnt);
	Oper b;
	while (wl_take(&ras->block_work_list, &b)) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		Block *block = mblock->block;
		get_live_out(ras, block, live_set);
		fprintf(stderr, "Live out %zu: ", mblock->block->base.index);
		FOR_EACH_WL_INDEX(live_set, i) {
			print_reg(stderr, live_set->dense[i]);
			fprintf(stderr, ", ");
		}
		fprintf(stderr, "\n");
		// process the block back to front, updating live_set in the
		// process
		for (Inst *inst = mblock->insts.prev; inst != &mblock->insts; inst = inst->prev) {
			live_step(live_set, mfunction, inst);
		}
		if (!wl_eq(live_set, &ras->live_in[b])) {
			WorkList tmp = ras->live_in[b];
			ras->live_in[b] = *live_set;
			*live_set = tmp;
			FOR_EACH_BLOCK_PRED(block, pred) {
				wl_add(&ras->block_work_list, (*pred)->mblock->index);
			}
		}
	}
}

void
build_interference_graph(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	WorkList *live_set = &ras->live_set;

	for (Oper b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		Block *block = mblock->block;
		get_live_out(ras, block, live_set);
		for (Inst *inst = mblock->insts.prev; inst != &mblock->insts; inst = inst->prev) {
			interference_step(ras, live_set, inst);
			live_step(live_set, mfunction, inst);
		}
	}

	// Physical registers are initialized with infinite degree. This makes
	// sure that simplification doesn't ever see tham transition to
	// non-significant degree and thus pushing them on the stack.
	for (size_t i = 0; i < R__MAX; i++) {
		ras->degree[i] = ras->mfunction->vreg_cnt + ras->reg_avail;
	}
}

bool
is_move_related(RegAllocState *ras, Oper i)
{
	//fprintf(stderr, "Is move related ");
	//print_reg(stderr, i);
	//fprintf(stderr, "\n");
	//Inst **moves = garena_array(&ras->gmoves, Inst *);
	GArena *gmove_list = &ras->move_list[i];
	Oper *move_list = garena_array(gmove_list, Oper);
	size_t move_cnt = garena_cnt(gmove_list, Oper);
	for (size_t i = 0; i < move_cnt; i++) {
		Oper move_index = move_list[i];
		//Inst *move = moves[move_index];
		//fprintf(stderr, "Moved in \t");
		//print_inst(stderr, ras->mfunction, move);
		//fprintf(stderr, "\n");
		if (wl_has(&ras->active_moves_wl, move_index) || wl_has(&ras->moves_wl, move_index)) {
			return true;
		}
	}
	//fprintf(stderr, "Not move related\n");
	return false;
}


void
for_each_adjacent(RegAllocState *ras, Oper op, void (*fun)(RegAllocState *ras, Oper neighbour))
{
	assert(op >= R__MAX);
	GArena *gadj_list = &ras->ig.adj_list[op];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t i = 0; i < adj_cnt; i++) {
		Oper neighbour = adj_list[i];
		if (wl_has(&ras->stack, neighbour) || is_alias(ras, neighbour)) {
			continue;
		}
		fun(ras, neighbour);
	}
}

void
for_each_move(RegAllocState *ras, Oper u, void (*fun)(RegAllocState *ras, Oper u, Oper m, Inst *move))
{
	Inst **moves = garena_array(&ras->gmoves, Inst *);
	GArena *gmove_list = &ras->move_list[u];
	Oper *move_list = garena_array(gmove_list, Oper);
	size_t move_cnt = garena_cnt(gmove_list, Oper);
	for (size_t i = 0; i < move_cnt; i++) {
		Oper move_index = move_list[i];
		if (wl_has(&ras->active_moves_wl, move_index) || wl_has(&ras->moves_wl, move_index)) {
			fun(ras, u, move_index, moves[move_index]);
		}
	}
}

bool
is_precolored(RegAllocState *ras, Oper op)
{
	return op < R__MAX;
}

bool
is_trivially_colorable(RegAllocState *ras, Oper op)
{
	return ras->degree[op] < ras->reg_avail;
}

bool
is_significant(RegAllocState *ras, Oper op)
{
	return ras->degree[op] >= ras->reg_avail;
}

void
initialize_worklists(RegAllocState *ras)
{
	size_t move_cnt = garena_cnt(&ras->gmoves, Inst *);
	size_t old_move_capacity = ras->move_capacity;
	if (ras->move_capacity == 0) {
		ras->move_capacity = 16;
	}
	while (ras->move_capacity < move_cnt) {
		ras->move_capacity += ras->move_capacity;
	}
	if (old_move_capacity < ras->move_capacity) {
		wl_grow(&ras->moves_wl, ras->move_capacity);
		wl_grow(&ras->active_moves_wl, ras->move_capacity);
	}
	wl_reset(&ras->moves_wl);
	wl_init_all(&ras->moves_wl, move_cnt);
	wl_reset(&ras->active_moves_wl);

	size_t vreg_cnt = ras->mfunction->vreg_cnt;
	for (size_t i = R__MAX; i < vreg_cnt; i++) {
		GArena *gadj_list = &ras->ig.adj_list[i];
		size_t adj_cnt = garena_cnt(gadj_list, Oper);
		assert(adj_cnt == ras->degree[i]);
		if (is_significant(ras, i)) {
			wl_add(&ras->spill_wl, i);
			fprintf(stderr, "Starting in spill ");
			print_reg(stderr, i);
			fprintf(stderr, " (%zu)\n", (size_t) ras->degree[i]);
		} else if (is_move_related(ras, i)) {
			fprintf(stderr, "Starting in freeze ");
			print_reg(stderr, i);
			wl_add(&ras->freeze_wl, i);
			fprintf(stderr, " (%zu)\n", (size_t) ras->degree[i]);
		} else {
			wl_add(&ras->simplify_wl, i);
			fprintf(stderr, "Starting in simplify ");
			print_reg(stderr, i);
			fprintf(stderr, " (%zu)\n", (size_t) ras->degree[i]);
		}
	}
}

double
spill_metric(RegAllocState *ras, Oper i)
{
	fprintf(stderr, "Spill cost for ");
	print_reg(stderr, i);
	fprintf(stderr, " degree: %"PRIu32", defs: %zu, uses: %zu, unspillable: %d\n", ras->degree[i], (size_t) ras->def_count[i], (size_t) ras->use_count[i], (int) ras->unspillable[i]);
	if (ras->unspillable[i]) {
		return 0.0;
	}
	return (double) ras->degree[i] / (ras->def_count[i] + ras->use_count[i]);
}

void
enable_move(RegAllocState *ras, Oper u, Oper m, Inst *move)
{
	(void) u;
	if (wl_remove(&ras->active_moves_wl, m)) {
		fprintf(stderr, "Enabling move: \t");
		print_inst(stderr, ras->mfunction, move);
		fprintf(stderr, "\n");
		wl_add(&ras->moves_wl, m);
	}
}

void
enable_moves_for_one(RegAllocState *ras, Oper op)
{
	for_each_move(ras, op, enable_move);
}

void
decrement_degree(RegAllocState *ras, Oper op)
{
	fprintf(stderr, "Removing interference with ");
	print_reg(stderr, op);
	fprintf(stderr, "\n");
	assert(ras->degree[op] > 0);
	ras->degree[op]--;
	if (is_trivially_colorable(ras, op)) {
		fprintf(stderr, "%zu %zu\n", (size_t) op, (size_t) R__MAX);
		assert(op >= R__MAX);
		enable_moves_for_one(ras, op);
		for_each_adjacent(ras, op, enable_moves_for_one);
		wl_remove(&ras->spill_wl, op);
		//fprintf(stderr, "Move from spill to %s ", is_move_related(ras, op) ? "freeze" : "simplify");
		//print_reg(stderr, op);
		//fprintf(stderr, "\n");
		if (is_move_related(ras, op)) {
			wl_add(&ras->freeze_wl, op);
		} else {
			wl_add(&ras->simplify_wl, op);
		}
	}
}

void
freeze_move(RegAllocState *ras, Oper u, Oper m, Inst *move)
{
	fprintf(stderr, "freezing in: \t");
	print_inst(stderr, ras->mfunction, move);
	fprintf(stderr, "\n");
	if (!wl_remove(&ras->active_moves_wl, m)) {
		wl_remove(&ras->moves_wl, m);
	}
	Oper v = move->ops[0] != u ? move->ops[0] : move->ops[1];
	if (!is_move_related(ras, v) && is_trivially_colorable(ras, v)) {
		fprintf(stderr, "Move from freeze to simplify in freeze ");
		print_reg(stderr, v);
		fprintf(stderr, "\n");
		wl_remove(&ras->freeze_wl, v);
		wl_add(&ras->simplify_wl, v);
	}
}

void
freeze_moves(RegAllocState *ras, Oper u)
{
	fprintf(stderr, "Freezing moves of ");
	print_reg(stderr, u);
	fprintf(stderr, "\n");
	for_each_move(ras, u, freeze_move);
}

void
freeze_one(RegAllocState *ras, Oper i)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->moves_wl));

	fprintf(stderr, "Freezing node ");
	print_reg(stderr, i);
	fprintf(stderr, "\n");

	wl_add(&ras->simplify_wl, i);
	freeze_moves(ras, i);
}

void
simplify_one(RegAllocState *ras, Oper i)
{
	fprintf(stderr, "Pushing ");
	print_reg(stderr, i);
	fprintf(stderr, "\n");

	wl_add(&ras->stack, i);
	for_each_adjacent(ras, i, decrement_degree);
}

void
choose_and_spill_one(RegAllocState *ras)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->moves_wl));
	assert(!wl_empty(&ras->spill_wl));

	fprintf(stderr, "Potential spill\n");

	Oper candidate = OPER_MAX;
	double max = 0.0;
	WorkList *spill_wl = &ras->spill_wl;
	FOR_EACH_WL_INDEX(spill_wl, j) {
		Oper i = spill_wl->dense[j];
		double curr = spill_metric(ras, i);
		// Prefer for spill either more beneficial candidates (with
		// bigger metric) or "earlier" vregs ("smaller index"). This
		// comes in handy for spilling callee saved registers, where we
		// want to spill `rbx` first, since encoding it is (sometimes)
		// shorter.
		if (curr > max || (curr == max && i < candidate)) {
			max = curr;
			candidate = i;
		}
	}

	fprintf(stderr, "Choosing for spill ");
	print_reg(stderr, candidate);
	fprintf(stderr, "\n");
	assert(candidate != OPER_MAX);
	assert(max > 0.0);

	wl_remove(&ras->spill_wl, candidate);
	wl_add(&ras->simplify_wl, candidate);
	freeze_moves(ras, candidate);
}

void
add_to_worklist(RegAllocState *ras, Oper op)
{
	if (!is_precolored(ras, op) && !is_move_related(ras, op) && is_trivially_colorable(ras, op)) {
		fprintf(stderr, "Move from freeze to simplify ");
		print_reg(stderr, op);
		fprintf(stderr, "\n");
		wl_remove(&ras->freeze_wl, op);
		wl_add(&ras->simplify_wl, op);
	}
}

size_t
significant_neighbour_cnt(RegAllocState *ras, Oper op)
{
	size_t n = 0;
	assert(op >= R__MAX);
	GArena *gadj_list = &ras->ig.adj_list[op];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t j = 0; j < adj_cnt; j++) {
		Oper t = adj_list[j];
		if (wl_has(&ras->stack, t) || is_alias(ras, t)) {
			continue;
		}
		n += is_significant(ras, t);
	}
	return n;
}

bool
ok(RegAllocState *ras, Oper t, Oper r)
{
	return is_trivially_colorable(ras, t) || is_precolored(ras, t) || ig_interfere(&ras->ig, t, r);
}

bool
precolored_coalesce_heuristic(RegAllocState *ras, Oper u, Oper v)
{
	assert(v >= R__MAX);
	GArena *gadj_list = &ras->ig.adj_list[v];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t j = 0; j < adj_cnt; j++) {
		Oper t = adj_list[j];
		if (wl_has(&ras->stack, t) || is_alias(ras, t)) {
			continue;
		}
		if (!ok(ras, t, u)) {
			return false;
		}
	}
	return true;
}

bool
conservative_coalesce_heuristic(RegAllocState *ras, Oper u, Oper v)
{
	size_t n = significant_neighbour_cnt(ras, u) + significant_neighbour_cnt(ras, v);
	return n < ras->reg_avail;
}

bool
are_coalesceble(RegAllocState *ras, Oper u, Oper v)
{
	if (u < R__MAX) {
		return precolored_coalesce_heuristic(ras, u, v);
	} else {
		return conservative_coalesce_heuristic(ras, u, v);
	}
}

void
combine(RegAllocState *ras, Oper u, Oper v)
{
	fprintf(stderr, "Combining " );
	print_reg(stderr, u);
	fprintf(stderr, " and " );
	print_reg(stderr, v);
	fprintf(stderr, "\n");

	assert(v >= R__MAX);
	if (!wl_remove(&ras->freeze_wl, v)) {
		assert(wl_remove(&ras->spill_wl, v));
	}

	// Set `v` as alias of `u`. Caller should already pass canonical `u`
	// and `v`, which are not aliases themselves.
	ras->alias[v] = u;

	// Add moves of `v` to `u`.
	Oper *other_moves = garena_array(&ras->move_list[v], Oper);
	size_t other_move_cnt = garena_cnt(&ras->move_list[v], Oper);
	for (size_t i = 0; i < other_move_cnt; i++) {
		// NOTE: would deduplication be beneficial?
		garena_push_value(&ras->move_list[u], Oper, other_moves[i]);
	}

	// Add edges of `v` to `u`.
	GArena *gadj_list = &ras->ig.adj_list[v];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t i = 0; i < adj_cnt; i++) {
		Oper t = adj_list[i];
		if (wl_has(&ras->stack, t) || is_alias(ras, t)) {
			continue;
		}
		// Add `u` as a neighbour to `v`'s neighbour `t`.
		ig_add(&ras->ig, u, t);
		// Since we coalesce `u` and `v`, we should remove `v` as a
		// neighbour. The important thing that we want to achieve is
		// actually decrement of `t`'s degree, which might make it
		// trivially colorable.
		//
		// We can get away with not removing `v` from adjacency list of
		// `u`, because aliased registers are skipped or resolve by
		// those iterating over them.
		decrement_degree(ras, t);
	}

	if (is_significant(ras, u) && wl_remove(&ras->freeze_wl, u)) {
		fprintf(stderr, "Move combined ");
		print_reg(stderr, u);
		fprintf(stderr, " from freeze to spill\n");
		wl_add(&ras->spill_wl, u);
	}
}

void
coalesce_move(RegAllocState *ras, Oper m)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->simplify_wl));
	MFunction *mfunction = ras->mfunction;

	Inst **moves = garena_array(&ras->gmoves, Inst *);
	Inst *move = moves[m];
	fprintf(stderr, "Coalescing: \t");
	print_inst(stderr, mfunction, move);
	fprintf(stderr, "\n");

	Oper u = get_alias(ras, move->ops[0]);
	Oper v = get_alias(ras, move->ops[1]);
	if (v < R__MAX) {
		Oper tmp = u;
		u = v;
		v = tmp;
	}

	if (u == v) {
		// already coalesced
		fprintf(stderr, "Already coalesced: \t");
		print_inst(stderr, mfunction, move);
		fprintf(stderr, "\n");
		add_to_worklist(ras, u);
	} else if (v < R__MAX || ig_interfere(&ras->ig, u, v)) {
		// constrained
		fprintf(stderr, "Constrained: \t");
		print_inst(stderr, mfunction, move);
		fprintf(stderr, "\n");
		add_to_worklist(ras, u);
		add_to_worklist(ras, v);
	} else if (are_coalesceble(ras, u, v)) {
		// coalesce
		combine(ras, u, v);
		add_to_worklist(ras, u);
	} else {
		fprintf(stderr, "Moving to active: \t");
		print_inst(stderr, mfunction, move);
		fprintf(stderr, "\n");
		wl_add(&ras->active_moves_wl, m);
	}
}

bool
assign_registers(RegAllocState *ras)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->spill_wl));
	assert(wl_empty(&ras->freeze_wl));
	assert(wl_empty(&ras->moves_wl));

	bool have_spill = false;
	MFunction *mfunction = ras->mfunction;

	// Physical registers are assigned themselves.
	for (size_t i = 0; i < R__MAX; i++) {
		ras->reg_assignment[i] = i;
	}

	Oper i;
	while (wl_take_back(&ras->stack, &i)) {
		assert(i >= R__MAX);
		fprintf(stderr, "Popping ");
		print_reg(stderr, i);
		fprintf(stderr, "\n");
		Oper used = 0;
		// If this one neighbours with some node that
		// has already color allocated (i.e. not on the
		// the stack) and it is not spilled (i.e. not R_NONE), make sure we
		// don't use the same register.
		GArena *gadj_list = &ras->ig.adj_list[i];
		Oper *adj_list = garena_array(gadj_list, Oper);
		size_t adj_cnt = garena_cnt(gadj_list, Oper);
		for (size_t j = 0; j < adj_cnt; j++) {
			Oper neighbour = get_alias(ras, adj_list[j]);
			if (!wl_has(&ras->stack, neighbour) && ras->reg_assignment[neighbour] != R_NONE) {
				used |= 1 << (ras->reg_assignment[neighbour] - 1);
			}
		}
		Oper reg = 0;
		for (size_t ri = 1; ri <= ras->reg_avail; ri++) {
			size_t mask = 1 << (ri - 1);
			if ((used & mask) == 0) {
				reg = ri;
				break;
			}
		}
		if (reg == 0) {
			fprintf(stderr, "Out of registers at ");
			print_reg(stderr, i);
			fprintf(stderr, "\n");
			ras->to_spill[i] = mfunction->stack_space;
			assert(mfunction->stack_space < 240);
			mfunction->stack_space += 8;
			have_spill = true;
		}
		ras->reg_assignment[i] = reg;
		fprintf(stderr, "allocated ");
		print_reg(stderr, i);
		fprintf(stderr, " to ");
		print_reg(stderr, reg);
		fprintf(stderr, "\n");
	}
	for (size_t i = 0; i < mfunction->vreg_cnt; i++) {
		if (is_alias(ras, i)) {
			fprintf(stderr, "Coalesced ");
			print_reg(stderr, i);
			fprintf(stderr, " to ");
			print_reg(stderr, get_alias(ras, i));
			fprintf(stderr, "\n");
		}
	}
	return !have_spill;
}

// Move all arguments and callee saved registers to temporaries at the
// start of the function. Then restore callee saved registers at the end
// of the function.

// Make all caller saved registers interfere with calls.


void
reg_alloc_function(RegAllocState *ras, MFunction *mfunction)
{
	print_mfunction(stderr, mfunction);

	reg_alloc_state_init_for_function(ras, mfunction);

	for (;;) {
		reg_alloc_state_reset(ras);
		liveness_analysis(ras);
		build_interference_graph(ras);
		calculate_spill_cost(ras);
		initialize_worklists(ras);

		Oper i;
	simplify:
		while (wl_take_back(&ras->simplify_wl, &i)) {
			simplify_one(ras, i);
		}
		if (wl_take(&ras->moves_wl, &i)) {
			coalesce_move(ras, i);
			goto simplify;
		}
		if (wl_take_back(&ras->freeze_wl, &i)) {
			freeze_one(ras, i);
			goto simplify;
		}
		if (!wl_empty(&ras->spill_wl)) {
			choose_and_spill_one(ras);
			goto simplify;
		}

		if (assign_registers(ras)) {
			break;
		}
		rewrite_program(ras);
	}

	// Fixup stack space amount reserved at the start of the function
	if (mfunction->make_stack_space) {
		IIMM(mfunction->make_stack_space) = mfunction->stack_space;
	}
	apply_reg_assignment(ras);
}

void
increment_count(void *user_data, Oper *oper)
{
	u8 *count = user_data;
	count[*oper]++;
}

void
decrement_count(void *user_data, Oper *oper)
{
	u8 *count = user_data;
	count[*oper]--;
}

typedef struct {
	Inst *inst;
	Inst **only_def;
	u8 *def_cnt;
} LastDefState;

void
track_last_def(void *user_data, Oper *oper)
{
	LastDefState *lds = user_data;
	// It is important that we set this to NULL if any second definition
	// exists, otherwise decrements of the def count might make it seem
	// like there was only one definition.
	lds->only_def[*oper] = lds->def_cnt[*oper] == 1 ? lds->inst : NULL;
}

void
calculate_def_use_info(MFunction *mfunction)
{
	GROW_ARRAY(mfunction->def_count, mfunction->vreg_cnt);
	GROW_ARRAY(mfunction->use_count, mfunction->vreg_cnt);
	GROW_ARRAY(mfunction->only_def, mfunction->vreg_cnt);
	ZERO_ARRAY(mfunction->def_count, mfunction->vreg_cnt);
	ZERO_ARRAY(mfunction->use_count, mfunction->vreg_cnt);
	ZERO_ARRAY(mfunction->only_def, mfunction->vreg_cnt);

	GROW_ARRAY(mfunction->block_use_count, mfunction->func->block_cap);
	ZERO_ARRAY(mfunction->block_use_count, mfunction->func->block_cap);

	LastDefState lds = { .only_def = mfunction->only_def, .def_cnt = mfunction->def_count };
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		bool flags_needed = false;
		for (Inst *inst = mblock->insts.prev; inst != &mblock->insts; inst = inst->prev) {
			lds.inst = inst;
			for_each_def(inst, increment_count, mfunction->def_count);
			for_each_def(inst, track_last_def, &lds);
			for_each_use(inst, increment_count, mfunction->use_count);
			inst->flags_observed = flags_needed;
			if (inst->writes_flags) {
				flags_needed = false;
			}
			if (inst->reads_flags) {
				flags_needed = true;
			}

			if (IM(inst) == M_L) {
				mfunction->block_use_count[ILABEL(inst)]++;
			}
		}
	}
}

void
mfunction_free(MFunction *mfunction)
{
	FREE_ARRAY(mfunction->def_count, mfunction->vreg_cnt);
	FREE_ARRAY(mfunction->use_count, mfunction->vreg_cnt);
	FREE_ARRAY(mfunction->only_def, mfunction->vreg_cnt);

	FREE_ARRAY(mfunction->block_use_count, mfunction->mblock_cnt);
}

bool
is_rip_relative(Inst *inst)
{
	return IBASE(inst) == R_NONE;
}

bool
is_memory_same(Inst *a, Inst *b)
{
	return ISCALE(a) == ISCALE(b) && IINDEX(a) == IINDEX(b) && IBASE(a) == IBASE(b) && IDISP(a) == IDISP(b);
}

void
copy_memory(Inst *dest, Inst *src)
{
	// This copies normal x86-64 addressing mode:
	//     [base+scale*index+disp]
	ISCALE(dest) = ISCALE(src);
	IINDEX(dest) = IINDEX(src);
	IBASE(dest) = IBASE(src);
	IDISP(dest) = IDISP(src);
        // The other addressing mode is:
        //     [rip+disp]
        // It uses IBASE(inst) = R_NONE and the displacement is actually
        // label+displacement, which are encoded using ILABEL(inst) and
        // IDISP(inst). Since we copy IBASE IDISP above and ILABEL aliases with
        // ISCALE, which we also copied above, it works for both cases.
}

bool
try_replace_by_immediate(MFunction *mfunction, Inst *inst, Oper o)
{
	Inst *def = mfunction->only_def[o];
	if (!def) {
		return false;
	}
	assert(mfunction->def_count[o] == 1);
	if (!(IK(def) == IK_MOV && IS(def) == MOV && IM(def) == M_CI)) {
		return false;
	}
	if (!pack_into_oper(get_imm64(def), &IIMM(inst))) {
		return false;
	}
	if (--mfunction->use_count[IREG(def)] == 0) {
		assert(--mfunction->def_count[IREG(def)] == 0);
		def->prev->next = def->next;
		def->next->prev = def->prev;
	}
	return true;
}

bool
try_combine_memory(MFunction *mfunction, Inst *inst)
{
	Inst *def = mfunction->only_def[IBASE(inst)];
	if (!def) {
		return false;
	}
	assert(mfunction->def_count[IBASE(inst)] == 1);
	if (IK(def) != IK_MOV || IS(def) != LEA) {
		return false;
	}
	// If this isn't RIP-relative addressing, and base isn't RBP, then we
	// bail out, if the definition may be ambigous.
	if (IBASE(def) != R_NONE && IBASE(def) != R_RBP && mfunction->def_count[IBASE(def)] > 1) {
		return false;
	}
	if (IINDEX(inst)) {
		// We could try harder to support some combinations, but we
		// currently don't. E.g. if only has one index or both have same
		// index and both scales are 1 (making the combined scale 2),
		// etc.
		return false;
	}
	if (IBASE(def) == R_NONE) {
		// Assert that RIP-relative addressing doesn't have an index.
		assert(IINDEX(def) == R_NONE);
	}
	// If the current instruction is RIP-relative or it has a scale, then we
	// also don't do anything currently.
	if (IBASE(inst) == R_NONE || ISCALE(inst) != 0) {
		return false;
	}
	// Try to add together the displacements. If they don't fit into 32
	// bits, then we bail out.
	if (!pack_into_oper((u64) IDISP(inst) + (u64) IDISP(def), &IDISP(inst))) {
		return false;
	}
	IBASE(inst) = IBASE(def);
	// NOTE: ISCALE essentially copies ILABEL in case of rip relative
	// addressing
	ISCALE(inst) = ISCALE(def);
	IINDEX(inst) = IINDEX(def);
	if (--mfunction->use_count[IREG(def)] == 0) {
		assert(--mfunction->def_count[IREG(def)] == 0);
		def->prev->next = def->next;
		def->next->prev = def->prev;
	}
	return true;
}

bool
try_combine_label(MFunction *mfunction, Inst *inst)
{
	Inst *def = mfunction->only_def[IREG(inst)];
	if (!def) {
		return false;
	}
	assert(mfunction->def_count[IREG(inst)] == 1);
	// We are looking for rip relative addressing (i.e. IBASE == R_NONE),
	// but also without any other displacement other than the label (i.e.
	// IDISP == 0).
	if (IK(def) != IK_MOV || IS(def) != LEA || IBASE(def) != R_NONE || IDISP(def) != 0) {
		return false;
	}
	ILABEL(inst) = ILABEL(def);
	if (--mfunction->use_count[IREG(def)] == 0) {
		def->prev->next = def->next;
		def->next->prev = def->prev;
	}
	return true;
}

void
peephole(MFunction *mfunction, Arena *arena, bool last_pass)
{
	u8 *use_cnt = mfunction->use_count;
	u8 *def_cnt = mfunction->def_count;
	Inst **defs = mfunction->only_def;
	u8 *block_use_cnt = mfunction->block_use_count;
	print_str(stderr, mfunction->func->name);
	fprintf(stderr, "\n");
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		Inst *inst = mblock->insts.next;
		while (inst != &mblock->insts) {
			print_inst(stderr, mfunction, inst);
			fprintf(stderr, "\n");
			fflush(stderr);
			// mov rax, rax
			// =>
			// [deleted]
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Cr && IREG(inst) == IREG2(inst)) {
				use_cnt[IREG(inst)]--;
				def_cnt[IREG(inst)]--;
				inst->prev->next = inst->next;
				inst->next->prev = inst->prev;
				goto next;
			}

			// mov t13, ... (where t13 is not used further)
			// =>
			// deleted
			//
			// xor t14, t14 (where t14 is not used further)
			// =>
			// deleted
			if ((IM(inst) == M_CI || IM(inst) == M_Cr || IM(inst) == M_CM || IM(inst) == M_Cn) && use_cnt[IREG(inst)] == 0) {
				def_cnt[IREG(inst)]--;
				for_each_use(inst, decrement_count, use_cnt);
				inst->prev->next = inst->next;
				inst->next->prev = inst->prev;
				goto next;
			}

			// cmp rax, 0
			// =>
			// test rax, rax
			if (IK(inst) == IK_BINALU && IS(inst) == G1_CMP && IM(inst) == M_ri && IIMM(inst) == 0) {
				use_cnt[IREG(inst)]++;
				IS(inst) = G1_TEST;
				IM(inst) = M_rr;
				IREG2(inst) = IREG(inst);
				continue;
			}

			// test/cmp ..., ... (and no flags observed)
			// =>
			// [deleted]
			if (IK(inst) == IK_BINALU && (IS(inst) == G1_TEST || IS(inst) == G1_CMP) && !IOF(inst)) {
				for_each_use(inst, decrement_count, use_cnt);
				inst->prev->next = inst->next;
				inst->next->prev = inst->prev;
				goto next;
			}

			// mov t20, 0 (and flags not observed)
			// =>
			// xor t20, t20 (sets flags, but noone will read them)
			if (false && IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_CI && get_imm64(inst) == 0 && !IOF(inst)) {
				// the second occurence doesn't count as use
				IK(inst) = IK_BINALU;
				IS(inst) = G1_XOR;
				IM(inst) = M_Cn;
				IWF(inst) = true;
				IREG2(inst) = IREG(inst);
				continue;
			}

			// add ..., 1 (and flags not observed)
			// =>
			// inc ...
			// Probably not worth it.
			// https://www.agner.org/optimize/microarchitecture.pdf
			if (false) {}

			Inst *prev = inst->prev;
			if (!prev) {
				goto next;
			}

			// lea t32, [rbp-16] // IK_MOV ANY M_C*
			// mov t14, t32
			// =>
			// lea t14, [rbp-16]
			//
			// mov t27, 1
			// mov t18, t27
			// =>
			// mov t18, 1
			if (IK(inst) == IK_MOV && IM(inst) == M_Cr && (IM(prev) == M_CI || IM(prev) == M_Cr || IM(prev) == M_CM) && IREG(prev) == IREG2(inst) && use_cnt[IREG(prev)] == 1) {
				def_cnt[IREG(prev)]--;
				use_cnt[IREG(prev)]--;
				IREG(prev) = IREG(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				prev->next = inst->next;
				inst = prev;
				continue;
			}

			// mov t12, 8
			// add t11, t12
			// =>
			//|mov t12, 8|
			// add t11, 8
			if (IK(inst) == IK_BINALU && (IM(inst) == M_Rr || IM(inst) == M_rr) && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && IREG(prev) == IREG2(inst) && pack_into_oper(get_imm64(prev), &IIMM(inst))) {
				inst->mode = IM(inst) == M_Rr ? M_Ri : M_ri;
				IREG2(inst) = R_NONE;
				if (--use_cnt[IREG(prev)] == 0) {
					--def_cnt[IREG(prev)];
					inst->prev = prev->prev;
					prev->prev->next = inst;
				}
				inst = inst;
				continue;
			}

			// mov t34, 3
			// mov [t14], t34
			// =>
			//|mov t34, 3|
			// mov [t14], 3
			if (IK(inst) == IK_MOV && IM(inst) == M_Mr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && IREG(prev) == IREG(inst) && pack_into_oper(get_imm64(prev), &IIMM(inst))) {
				IM(inst) = M_Mi;
				if (--use_cnt[IREG(prev)] == 0) {
					--def_cnt[IREG(prev)];
					inst->prev = prev->prev;
					prev->prev->next = inst;
				}
				inst = inst;
				continue;
			}

			// lea t25, [rbp-24]
			// mov t26, [t25]
			// =>
			// mov t26, [rbp-24]
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_CM && IINDEX(inst) == R_NONE && ISCALE(inst) == 0 && IDISP(inst) == 0 && IK(prev) == IK_MOV && IS(prev) == LEA && IM(prev) == M_CM && IBASE(inst) == IREG(prev) && use_cnt[IREG(prev)] == 1) {
				def_cnt[IREG(prev)]--;
				use_cnt[IREG(prev)]--;
				IS(prev) = MOV;
				IREG(prev) = IREG(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// mov rcx, [global1]
			// add rax, rcx
			// =>
			// add rax, [global1]
			if (IK(inst) == IK_BINALU && IM(inst) == M_Rr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CM && IREG2(inst) == IREG(prev) && IREG(inst) != IREG2(inst) && use_cnt[IREG(prev)] == 1) {
				def_cnt[IREG(prev)]--;
				use_cnt[IREG(prev)]--;
				IM(prev) = M_RM;
				IK(prev) = IK(inst);
				IS(prev) = IS(inst);
				IREG(prev) = IREG(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// mov t13, [rbp-16]
			// cmp t13, 10
			// =>
			// cmp [rbp-16], 10
			if (IK(inst) == IK_BINALU && IM(inst) == M_ri && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CM) {
				IM(inst) = M_Mi;
				ISCALE(inst) = ISCALE(prev);
				IINDEX(inst) = IINDEX(prev);
				IBASE(inst) = IBASE(prev);
				IDISP(inst) = IDISP(prev);
				inst->prev = prev->prev;
				prev->prev->next = inst;
				inst = inst;
			}


			// mov rax, 1
			// add rax, 2
			// =>
			// mov rax, 3
			if (IK(inst) == IK_BINALU && IM(inst) == M_Ri && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && IREG(inst) == IREG(prev)) {
				def_cnt[IREG(inst)]--;
				use_cnt[IREG(inst)]--;
				u64 value = get_imm64(prev);
				u64 right = IIMM(inst);
				// Let's just say that any kind of overflow is
				// undefined behaviour and not complicate this
				// piece of code.
				switch (IS(inst)) {
				case G1_ADD:  value += right; break;
				case G1_OR:   value |= right; break;
				case G1_AND:  value &= right; break;
				case G1_SUB:  value -= right; break;
				case G1_XOR:  value ^= right; break;
				case G1_IMUL: value *= right; break;
				default: goto skip;
				}
				set_imm64(prev, value);
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			skip:;
			}

			// mov rcx, 5
			// neg rcx ; W
			// =>
			// mov rcx, -5
			if (IK(inst) == IK_UNALU && IM(inst) == M_R && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && IREG(inst) == IREG(prev)) {
				def_cnt[IREG(inst)]--;
				use_cnt[IREG(inst)]--;
				u64 value = get_imm64(prev);
				switch (IS(inst)) {
				case G3_NEG: value = -value; break;
				case G3_NOT: value = ~value; break;
				default: UNREACHABLE();
				}
				set_imm64(prev, value);
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// mov t43, 4
			// imul t43, t19 ; W
			// =>
			// mov t43, t19
			// imul t43, 4
			if (IK(inst) == IK_BINALU && g1_is_commutative(IS(inst)) && IM(inst) == M_Rr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && pack_into_oper(get_imm64(prev), &IIMM(inst))) {
				IM(prev) = M_Cr;
				IREG2(prev) = IREG2(inst);
				IM(inst) = M_Ri;
			}

			// lea t14, [rbp-16]
			// add t14, 8
			// =>
			// lea t14, [rbp-8]
			if (IK(inst) == IK_BINALU && IS(inst) == G1_ADD && IM(inst) == M_Ri && IK(prev) == IK_MOV && IS(prev) == LEA && IREG(prev) == IREG(inst)) {
				def_cnt[IREG(inst)]--;
				use_cnt[IREG(inst)]--;
				IDISP(prev) += IIMM(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				prev->next = inst->next;
				inst = prev;
				continue;
			}

			// mov [G], t27
			// mov t28, [G]
			// =>
			// mov [G], t27
			// mov t28, t27
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_CM && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_Mr && is_memory_same(inst, prev)) {
				use_cnt[IREG(prev)]++;
				IM(inst) = M_Cr;
				IREG2(inst) = IREG(prev);
				inst = inst;
				continue;
			}

			// lea rax, [rbp-8]
			// mov qword [rax], 3
			// =>
			// mov qword [rbp-8], 3
			if (IK(inst) == IK_MOV && IS(inst) == MOV && (IM(inst) == M_Mi || IM(inst) == M_Mr) && IK(prev) == IK_MOV && IS(prev) == LEA && IINDEX(prev) == R_NONE && ISCALE(prev) == 0 && IBASE(inst) == IREG(prev) && use_cnt[IREG(prev)] == 1) {
				IBASE(inst) = IBASE(prev);
				IDISP(inst) += IDISP(prev);
				inst->prev = prev->prev;
				prev->prev->next = inst;
				inst = inst;
				continue;
			}

			// add t17, 8
			// mov qword [t17], 5
			// =>
			// mov qword [t17+8], 5
			// NOTE: only valid if t17 is not used anywhere
			if (IK(inst) == IK_MOV && IS(inst) == MOV && (IM(inst) == M_Mi || IM(inst) == M_Mr) && IK(prev) == IK_BINALU && IS(prev) == G1_ADD && IM(prev) == M_Ri && IBASE(inst) == IREG(prev) && use_cnt[IBASE(inst)] == 2) {
				def_cnt[IBASE(inst)]--;
				use_cnt[IBASE(inst)]--;
				IDISP(inst) += IIMM(prev);
				inst->prev = prev->prev;
				prev->prev->next = inst;
				inst = inst;
				continue;
			}

			Inst *pprev = prev->prev;
			if (!pprev) {
				goto next;
			}

			// CP
			// mov t35, 8
			// mov t14, t34
			// add t14, t35
			// =>
			// mov t14, t34
			// add t14, 8
			if (false && IK(inst) == IK_BINALU && IM(inst) == M_Rr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_Cr && IK(pprev) == IK_MOV && IS(pprev) == MOV && IM(pprev) == M_CI && IREG(pprev) == IREG2(inst) && use_cnt[IREG2(inst)] == 1 && pack_into_oper(get_imm64(pprev), &IIMM(inst))) {
				def_cnt[IREG2(inst)]--;
				use_cnt[IREG2(inst)]--;
				IM(inst) = M_Ri;
				pprev->prev->next = prev;
				prev->prev = pprev->prev;
				inst = prev;
				continue;
			}

			// CP
			// mov t22, [H]
			// mov t23, ...
			// add t23, t22
			// =>
			// mov t23, ...
			// add t23, [H]
			if (IK(inst) == IK_BINALU && IM(inst) == M_Rr && IK(prev) == IK_MOV && IS(prev) == MOV && IREG(prev) == IREG(inst) && IREG(pprev) == IREG2(inst) && use_cnt[IREG(pprev)] == 1 && def_cnt[IREG(inst)] == 2 && ((IM(pprev) == M_CI && pack_into_oper(get_imm64(pprev), &IIMM(pprev)))|| IM(pprev) == M_Cr || IM(pprev) == M_CM)) {
				// We made sure that def_cnt of t23 is 2, which
				// is the two definitions we see in this
				// peephole. This should guarantee us, that t23
				// isn't in any way connected to definition of
				// of [H] (because then there would be an
				// additional definition).
				def_cnt[IREG(pprev)]--;
				use_cnt[IREG(pprev)]--;
				IK(pprev) = IK(inst);
				IS(pprev) = IS(inst);
				switch (IM(pprev)) {
				case M_CI: IM(pprev) = M_Ri; break;
				case M_Cr: IM(pprev) = M_Rr; break;
				case M_CM: IM(pprev) = M_RM; break;
				default: UNREACHABLE();
				}
				IREG(pprev) = IREG(inst);
				pprev->prev->next = prev;
				prev->prev = pprev->prev;
				prev->next = pprev;
				pprev->prev = prev;
				pprev->next = inst->next;
				inst->next->prev = pprev;
				inst = pprev;
				continue;
			}

			// imul t50, t21, 8 ; W
			// lea t32, [t18+t50]
			// =>
			// lea t32, [t18+8*t50]
			if (mode_has_memory(IM(inst)) && !is_rip_relative(inst) && IINDEX(inst) != R_NONE && IK(prev) == IK_IMUL3 && IM(prev) == M_Cri && IREG(prev) == IINDEX(inst) && IIMM(prev) == 8 && ISCALE(inst) == 0 && use_cnt[IREG(prev)] == 1) {
				use_cnt[IREG(prev)]--;
				ISCALE(inst) = 3;
				IINDEX(inst) = IREG2(prev);
				inst->prev = pprev;
				pprev->next = inst;
				inst = inst;
				continue;
			}

			Inst *ppprev = pprev->prev;

			// mov [rbp-16], t18
			// mov t21, [rbp-16]
			// add t21, t19 ; W
			// mov [rbp-16], t21
			// => (due to a previous optimization)
        		// mov [rbp-16], t18
        		// mov t21, t18
        		// add t21, t19 ; W
        		// mov [rbp-16], t21
			// =>
			// mov t21, t18
			// add t21, t19 ; W
			// mov [rbp-16], t21
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Mr && IK(prev) == IK_BINALU && IM(prev) == M_Rr && IREG(prev) == IREG(inst) && IK(pprev) == IK_MOV && IS(pprev) == MOV && IM(pprev) == M_Cr && IREG(pprev) == IREG(inst) && IK(ppprev) == IK_MOV && IS(ppprev) == MOV && IM(ppprev) == M_Mr && IREG(ppprev) == IREG2(pprev) && is_memory_same(inst, ppprev)) {
				ppprev->prev->next = pprev;
				pprev->prev = ppprev->prev;
				inst = pprev;
				continue;
			}

			// mov rax, [rbp-24]
			// add rax, 1
			// mov [rbp-24], rax
			// =>
			// add [rbp-24], 1
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Mr && ((IK(prev) == IK_BINALU && (IM(prev) == M_Ri || IM(prev) == M_Rr)) || (IK(prev) == IK_UNALU && IM(prev) == M_R)) && IK(pprev) == IK_MOV && IS(pprev) == MOV && IM(pprev) == M_CM && IREG(prev) == IREG(pprev) && IREG(inst) == IREG(prev) && is_memory_same(pprev, inst)) {
				switch (IM(prev)) {
				case M_Ri: IM(prev) = M_Mi; break;
				case M_Rr: IM(prev) = M_Mr; break;
				case M_R:  IM(prev) = M_M;  break;
				default: UNREACHABLE();
				}
				copy_memory(prev, inst);
				prev->prev = pprev->prev;
				pprev->prev->next = prev;
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// imul t36, t44 ; W
			// test t36, t36 ; WO
			// =>
			// imul t36, t44 ; WO
			if (IK(inst) == IK_BINALU && (IS(inst) == G1_CMP || IS(inst) == G1_TEST) && IM(inst) == M_rr && IREG(inst) == IREG2(inst) && IWF(prev) && ((IK(prev) == IK_BINALU && (IM(prev) == M_Rr || IM(prev) == M_Ri || IM(prev) == M_RM)) || (IK(prev) == IK_UNALU && IM(prev) == M_R)) && IREG(prev) == IREG(inst)) {
				IOF(prev) = true;
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// setg t28
			// test t28, t28
			// jz .BB3
			// =>
			// jng .BB2
			if ((IK(inst) == IK_JCC || IK(inst) == IK_CMOVCC || IK(inst) == IK_SETCC) && IS(inst) == CC_Z && IK(prev) == IK_BINALU && IS(prev) == G1_TEST && IM(prev) == M_rr && IREG(prev) == IREG2(prev) && IK(pprev) == IK_SETCC && IREG(prev) == IREG(pprev)) {
				def_cnt[IREG(pprev)]--;
				use_cnt[IREG(pprev)] -= 3; // (2 for test, 1 for setcc)
				IS(inst) = cc_invert(IS(pprev));
				pprev->prev->next = inst;
				inst->prev = pprev->prev;
				// Go back before the flags are set and look for
				// optimization opportunities. For example for
				// the rest of the following pattern:
				// xor t28, t28 ; W
				// cmp t27, t41 ; WO
				// setg t28 ; R
				while (IRF(inst) || IOF(inst)) {
					inst = inst->prev;
				}
				continue;
			}

			// ... t32, CONST
			// ...
			// mov t14, t32
			// =>
			//|... t32, ...|
			// mov t14, CONST
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Cr && try_replace_by_immediate(mfunction, inst, IREG2(inst))) {
				IM(inst) = M_CI;
				set_imm64(inst, IIMM(inst));
				continue;
			}

			// ... t32, CONST
			// ...
			// add t14, t32
			// =>
			//|... t32, ...|
			// add t14, CONST
			if (IK(inst) == IK_BINALU && (IM(inst) == M_Rr || IM(inst) == M_rr) && try_replace_by_immediate(mfunction, inst, IREG2(inst))) {
				assert(IM(inst) == M_rr || inst->writes_flags);
				IM(inst) = IM(inst) == M_Rr ? M_Ri : M_ri;
				continue;
			}

			// ... t32, CONST
			// ...
			// mov [t14], t32
			// =>
			//|... t32, ...|
			// mov [t14], CONST
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Mr && try_replace_by_immediate(mfunction, inst, IREG2(inst))) {
				IM(inst) = M_Mi;
				continue;
			}

			// lea t19, [t18+3]
			// ...
			// lea t20, [t19+4]
			// =>
			// lea t20, [t18+7]
			if (IK(inst) == IK_MOV && IS(inst) == LEA && try_combine_memory(mfunction, inst)) {
				continue;
			}

			// mov t18, 3
			// ...
			// lea 19, [t18+7]
			// =>
			// mov 19, 10
			if (IK(inst) == IK_MOV && IS(inst) == LEA && try_replace_by_immediate(mfunction, inst, IBASE(inst))) {
				// At this point we know that this isn't
				// RIP-relative addressing, since IBASE was
				// found to have unique definition to immediate.
				IDISP(inst) += IIMM(inst);
				IIMM(inst) = 0;
				if (IINDEX(inst) != R_NONE) {
					IBASE(inst) = IINDEX(inst);
				} else {
					IS(inst) = MOV;
					IM(inst) = M_CI;
					set_imm64(inst, IDISP(inst));
				}
				continue;
			}

			// mov t25, 1
			// ...
			// push t25
			// =>
			// push 1
			if (IK(inst) == IK_PUSH && IM(inst) == M_r && try_replace_by_immediate(mfunction, inst, IREG(inst))) {
				IM(inst) = M_I;

			}

			// lea t25, [rbp-24]
			// ...
			// mov t26, [t25]
			// =>
			// mov t26, [rbp-24]
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_CM && try_combine_memory(mfunction, inst)) {
				continue;
			}

			// lea t25, [rbp-24]
			// ...
			// mov [t25], t24
			// =>
			// mov [rbp-24], t24
			if (IK(inst) == IK_MOV && IS(inst) == MOV && (IM(inst) == M_Mr || IM(inst) == M_Mi) && try_combine_memory(mfunction, inst)) {
				continue;
			}

			// lea t53, [rbp-32]
			// ...
			// add t35, [t53+8]
			// =>
			// add t35, [rbp-24]
			if (((IK(inst) == IK_BINALU && (IM(inst) == M_RM || IM(inst) == M_Mr)) || (IK(inst) == IK_UNALU && IM(inst) == M_M)) && try_combine_memory(mfunction, inst)) {
				continue;
			}

			// lea rax, [one]
			// call rax
			//=>
			// call one
			if (IK(inst) == IK_CALL && IM(inst) == M_rCALL && try_combine_label(mfunction, inst)) {
				IM(inst) = M_LCALL;
				continue;
			}

			// mov t26, t18
			// add t26, t34 ; W (no flags observed)
			// =>
			// lea t26, [t18+t34]
			if (IK(inst) == IK_BINALU && IS(inst) == G1_ADD && (IM(inst) == M_Rr || IM(inst) == M_Ri) && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_Cr && IREG(prev) == IREG(inst) && def_cnt[IREG(inst)] == 2) {
				use_cnt[IREG(inst)]--;
				def_cnt[IREG(inst)]--;
				defs[IREG(inst)] = prev;
				IS(prev) = LEA;
				IM(prev) = M_CM;
				IBASE(prev) = IREG2(prev);
				ISCALE(prev) = 0;
				if (IM(inst) == M_Rr) {
					IINDEX(prev) = IREG2(inst);
					IDISP(prev) = 0;
				} else {
					IINDEX(prev) = R_NONE;
					IDISP(prev) = IIMM(inst);
				}
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

		next:
			inst = inst->next;
		}

		if (b == mfunction->mblock_cnt - 1) {
			break;
		}

		Oper next_block_index;
		MBlock *next = NULL;
		size_t i;
		for (i = b + 1; i < mfunction->mblock_cnt; i++) {
			next = mfunction->mblocks[i];
			if (next) {
				next_block_index = next->block->base.index;
				break;
			}
		}
		if (!next) {
			continue;
		}
		Inst *last = mblock->insts.prev;
		Inst *prev = last->prev;

		//     jge .BB3
		//     jmp .BB4
		// .BB3:
		// =>
		//     jl .BB4
		// .BB3:
		if (IK(last) == IK_JUMP && IK(prev) == IK_JCC && ILABEL(prev) == next->block->base.index) {
			IS(prev) = cc_invert(IS(prev));
			ILABEL(prev) = ILABEL(last);
			last->prev->next = last->next;
			last->next->prev = last->prev;
			block_use_cnt[next_block_index]--;
			last = last->prev;
		}

		//     jmp .BB5
		// .BB5:
		// =>
		// .BB5:
		if (IK(last) == IK_JUMP && ILABEL(last) == next->block->base.index) {
			last->prev->next = last->next;
			last->next->prev = last->prev;
			block_use_cnt[next_block_index]--;
			last = last->prev;
		}

		if (last_pass && block_use_cnt[next->block->base.index] == 0) {
			// If there is no reference to the next block (as
			// label), we can just merge it into the current one.
			mfunction->mblocks[i] = NULL;
			last->next = next->insts.next;
			next->insts.next->prev = last;
			next->insts.prev->next = &mblock->insts;
			mblock->insts.prev = next->insts.prev;
			inst = last;
			goto next;
		}
	}
}

typedef struct Error Error;
struct Error {
	Error *next;
	char *kind;
	const u8 *pos;
	u8 *msg;
};

typedef struct {
	Arena arena;
	Str source;
	Error *error_head;
	Error *error_tail;
	jmp_buf loc;
} ErrorContext;

void
error_context_init(ErrorContext *ec)
{
	arena_init(&ec->arena);
	ec->source = (Str) {0};
	ec->error_head = NULL;
	ec->error_tail = NULL;
}

static void
verror(ErrorContext *ec, const u8 *pos, char *kind, bool fatal, const char *fmt, va_list ap)
{
	Error *error = arena_alloc(&ec->arena, sizeof(*error));
	error->msg = (u8 *) arena_vaprintf(&ec->arena, fmt, ap).str;
	error->pos = pos;
	error->kind = kind;
	error->next = NULL;
	if (ec->error_tail) {
		ec->error_tail->next = error;
	}
	ec->error_tail = error;
	if (!ec->error_head) {
		ec->error_head = error;
	}
	if (fatal) {
		longjmp(ec->loc, 1);
	}
}

static void
parser_verror(void *user_data, const u8 *err_pos, const char *msg, va_list ap)
{
	ErrorContext *ec = user_data;
	verror(ec, err_pos, "parse", false, msg, ap);
}

Module *
parse_source(ErrorContext *ec, Arena *arena, Str source)
{
	size_t arena_start = arena_save(arena);
	GArena scratch;
	garena_init(&scratch);
	ec->source = source;
	Module *module = parse(arena, &scratch, source, parser_verror, ec);
	garena_free(&scratch);

	if (!module) {
		arena_restore(arena, arena_start);
		longjmp(ec->loc, 1);
	}
	return module;
}

static void PRINTF_LIKE(2)
argument_error(ErrorContext *ec, const char *msg, ...)
{
	va_list ap;
	va_start(ap, msg);
	verror(ec, NULL, "argument", true, msg, ap);
	va_end(ap);
}

static Str
read_file(ErrorContext *ec, Arena *arena, const char *name)
{
	errno = 0;
	FILE *f = fopen(name, "rb");
	if (!f) {
		argument_error(ec, "Failed to open file '%s': %s", name, strerror(errno));
	}
	if (fseek(f, 0, SEEK_END) != 0) {
		argument_error(ec, "Failed seek in file '%s': %s", name, strerror(errno));
	}
	long tell = ftell(f);
	if (tell < 0) {
		argument_error(ec, "Failed to ftell a file '%s': %s", name, strerror(errno));
	}
	size_t fsize = (size_t) tell;
	assert(fseek(f, 0, SEEK_SET) == 0);
	u8 *buf = arena_alloc(arena, fsize);
	size_t read;
	if ((read = fread(buf, 1, fsize, f)) != fsize) {
		if (feof(f)) {
			fsize = read;
		} else {
			argument_error(ec, "Failed to read file '%s'", name);
		}
	}
	assert(fclose(f) == 0);
	return (Str) { .str = buf, .len = fsize };
}

int
main(int argc, char **argv)
{
	Arena arena_;
	Arena *arena = &arena_;
	arena_init(arena);

	ErrorContext ec;
	error_context_init(&ec);

	if (setjmp(ec.loc) != 0) {
		goto end;
	}

	Function **functions = NULL;
	size_t function_cnt = 0;

	if (argc < 2) {
		goto end;
	}

	Str source = read_file(&ec, arena, argv[1]);
	Module *module = parse_source(&ec, arena, source);
	functions = module->functions;
	function_cnt = module->function_cnt;

	RegAllocState ras;
	reg_alloc_state_init(&ras, arena);
	GArena labels = {0};

	fprintf(stderr, "Globals:\n");
	print_globals(stderr, module);
	fprintf(stderr, "\n");
	for (size_t i = 0; i < function_cnt; i++) {
		number_values(functions[i], R__MAX);
		print_function(stderr, functions[i]);
		merge_simple_blocks(arena, functions[i]);
		print_function(stderr, functions[i]);
		get_uses(functions[i]);
		mem2reg(functions[i]);
		free_uses(functions[i]);
		value_numbering(arena, functions[i]);
		print_function(stderr, functions[i]);
		thread_jumps(arena, functions[i]);
		print_function(stderr, functions[i]);
		split_critical_edges(arena, functions[i]);
		print_function(stderr, functions[i]);
		single_exit(arena, functions[i]);
		print_function(stderr, functions[i]);
		///*
		translate_function(arena, &labels, functions[i]);
		calculate_def_use_info(functions[i]->mfunc);
		print_mfunction(stderr, functions[i]->mfunc);
		peephole(functions[i]->mfunc, arena, false);
		print_mfunction(stderr, functions[i]->mfunc);
		reg_alloc_function(&ras, functions[i]->mfunc);
		print_mfunction(stderr, functions[i]->mfunc);
		calculate_def_use_info(functions[i]->mfunc);
		peephole(functions[i]->mfunc, arena, true);
		print_mfunction(stderr, functions[i]->mfunc);
		//*/
		//peephole(functions[i]->mfunc, arena);
	}

	///*
	reg_alloc_state_free(&ras);

	printf("\tdefault rel\n\n");

	printf("\tsection .data\n");
	for (size_t i = 0; i < module->global_cnt; i++) {
		Global *global = module->globals[i];
		if (global->init) {
			//printf("\talign 8\n");
			print_str(stdout, global->name);
			printf(":\n");
			printf("\tdq\t");
			print_value(stdout, global->init);
			printf("\n");
		}
	}
	printf("\n");

	printf("\tsection .bss\n");
	for (size_t i = 0; i < module->global_cnt; i++) {
		Global *global = module->globals[i];
		Oper size = type_size(pointer_child(global->base.type));
		Oper count = size / type_size(&TYPE_INT);
		if (!global->init) {
			//printf("\talign 8\n");
			print_str(stdout, global->name);
			printf(":\n");
			printf("\tresq\t%"PRIu32"\n", count);
		}
	}
	printf("\n");

	printf("\tsection .text\n");
	printf("\n");
	printf("\tglobal _start\n");
	printf("_start:\n");
	printf("\txor rbp, rbp\n");
	printf("\tand rsp, -8\n");
	printf("\tcall main\n");
	printf("\tmov rdi, rax\n");
	printf("\tmov rax, 60\n");
	printf("\tsyscall\n");

	for (size_t i = 0; i < function_cnt; i++) {
		printf("\n");
		print_mfunction(stdout, functions[i]->mfunc);
	}
	//*/

end:
	for (Error *err = ec.error_head; err; err = err->next) {
		if (!err->pos) {
			fprintf(stderr, "%s error: %s\n", err->kind, err->msg);
			continue;
		}
		const u8 *line_start = ec.source.str;
		size_t line = 0;
		const u8 *pos = ec.source.str;
		for (; pos < err->pos; pos++) {
			if (*pos == '\n') {
				line_start = pos + 1;
				line++;
			}
		}
		size_t col = pos - line_start;
		const u8 *source_end = ec.source.str + ec.source.len;
		const u8 *line_end = pos;
		for (; line_end < source_end && *line_end != '\n'; line_end++) {}
		fprintf(stderr, "[%zu:%zu]: %s error: %s\n", line + 1, col + 1, err->kind, err->msg);
		fprintf(stderr, "  %.*s\n", (int) (line_end - line_start), line_start);
		fprintf(stderr, "  %*s\n", (int) (pos - line_start + 1), "^");
	}

	for (size_t i = 0; i < function_cnt; i++) {
		Function *function = functions[i];
		for (size_t b = 0; b < function->block_cap; b++) {
			Block *block = function->blocks[b];
			free(block->preds_);
		}
		free(function->blocks);
		free(function->post_order);
		mfunction_free(function->mfunc);
	}
	garena_free(&labels);

	arena_free(&ec.arena);
	arena_free(arena);
	return ec.error_head ? EXIT_FAILURE : EXIT_SUCCESS;
}
