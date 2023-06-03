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
#include "regalloc.h"
#include "parser.h"

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
create_inst(Arena *arena, InstKind kind, u8 subkind, X86Mode mode)
{
	// On x86-64 we use uniform representation which always with 6 operands.
	// The operands have different meanings depending on the mode and some
	// modes use as little as 0 of those operands, but we as of now, prefer
	// uniform allocation - this allows to completely change instruction
	// from one mode to another without worrying about the allocation being
	// too small. It also allows the allocations to be reused simply with
	// free list, though this is currently not employed.
	size_t operand_cnt = 6;

	Inst *inst = arena_alloc(arena, sizeof(*inst) + operand_cnt * sizeof(inst->ops[0]));
	inst->kind = kind;
	inst->subkind = subkind;
	inst->mode = mode;
	inst->flags_observed = false; // Redefined later by analysis.
	inst->writes_flags = false; // Default is no flags.
	inst->reads_flags = false; // Default is no flags.
	memset(&inst->ops[0], 0, operand_cnt * sizeof(inst->ops[0]));
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
add_inst(TranslationState *ts, InstKind kind, u8 subkind, X86Mode mode)
{
	Inst *new = create_inst(ts->arena, kind, subkind, mode);
	add_inst_(ts, new);
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
	return inst;
}

static Inst *
add_store(TranslationState *ts, Oper addr, Oper value)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV, M_Mr);
	IREG(inst) = value;
	IBASE(inst) = addr;
	return inst;
}

static void
add_lea(TranslationState *ts, Oper dest, Oper base, Oper disp)
{
	Inst *inst = add_inst(ts, IK_MOV, LEA, M_CM);
	IREG(inst) = dest;
	IBASE(inst) = base;
	IDISP(inst) = disp;
}

static void
add_lea_label(TranslationState *ts, Oper dest, Oper label)
{
	Inst *inst = add_inst(ts, IK_MOV, LEA, M_CM);
	IREG(inst) = dest;
	IBASE(inst) = R_NONE;
	ILABEL(inst) = label;
}

static void
add_mov_imm(TranslationState *ts, Oper dest, u64 imm)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV, M_CI);
	IREG(inst) = dest;
	set_imm64(inst, imm);
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
	inst->writes_flags = true;
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
	size_t gpr_index = 0;
	for (size_t i = 0; gpr_index < ARRAY_LEN(argument_regs) - 1 && i < arg_cnt; i++) {
		add_copy(ts, argument_regs[gpr_index], args[i]);
		gpr_index++;
	}
	for (size_t i = arg_cnt; i > ARRAY_LEN(argument_regs) - 1; i--) {
		add_push(ts, args[i - 1]);
	}
	if (vararg) {
		add_set_zero(ts, R_RAX);
	}
	add_call(ts, fun, gpr_index);
	add_copy(ts, res, R_RAX);
}

static Inst *
add_load_with_disp(TranslationState *ts, Oper dest, Oper addr, Oper disp)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV, M_CM);
	inst->mode = M_CM;
	IREG(inst) = dest;
	IBASE(inst) = addr;
	IDISP(inst) = disp;
	return inst;
}

static Inst *
create_store_with_disp(TranslationState *ts, Oper dest, Oper addr, Oper disp)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV, M_Mr);
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
	ts->make_stack_space = add_inst(ts, IK_BINALU, G1_SUB, M_Ri);
	Inst *inst = ts->make_stack_space;
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
		add_lea(ts, res, R_RBP, - 8 - alloca->size);
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
	if (v->kind == VK_PHI) {
		// Don't translate phi nor its operands -- they are handled in
		// the predecessors.
		return;
	}

	fprintf(stderr, "Translating: ");
	print_value(stderr, v);

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
		alloca->size = ts->stack_space;
		ts->stack_space += size;
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

	case VK_LOAD: {
		Inst *load = add_load(ts, res, ops[0]);
		if (pointer_child(LOAD_ADDR(v)->type)->kind == TY_CHAR) {
			IS(load) = MOVZX8;
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
		Operation *call = (void *) v;
		bool vararg = ((FunctionType *) call->operands[0]->type)->vararg;
		size_t arg_cnt = value_operand_cnt(v) - 1;
		translate_call(ts, res, ops[0], &ops[1], arg_cnt, vararg);
		break;
	}
	case VK_JUMP: {
		Block *current = ts->block->block;
		Block *succ = (Block *) ((Operation *) v)->operands[0];
		size_t pred_index = block_index_of_pred(succ, current);
		size_t i = 0;
		FOR_EACH_PHI_IN_BLOCK(succ, phi) {
			Oper t = translate_operand(ts, phi->operands[pred_index]);
			add_copy(ts, ops[i++] = ts->index++, t);
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

void
merge_simple_blocks(Arena *arena, Function *function)
{
	(void) arena;
	//for (size_t b = function->block_cnt; b--;) {
	for (size_t b = 0; b < function->block_cnt; b++) {
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

		// Fix parent links.
		FOR_EACH_IN_BLOCK(succ, v) {
			v->parent = &block->base;
		}

		// Remove the jump instruction from `block`.
		remove_value(block->base.prev);

		// Append `succ` instructions to `block`.
		block->base.prev->next = succ->base.next;
		succ->base.next->prev = block->base.prev;
		block->base.prev = succ->base.prev;
		block->base.prev->next = &block->base;

		// Make sure we don't operate on the merge successor if it
		// happens to be in processed later.
		succ->base.next = &succ->base;
		succ->base.prev = &succ->base;
	}

	// Recompute function->post_order, since we invalidated it.
	compute_preorder(function);
}

// NOTE: May introduce critical edges.
void
thread_jumps(Arena *arena, Function *function)
{
	(void) arena;
	for (size_t b = 0; b < function->block_cnt; b++) {
		Block *block = function->post_order[b];
		if (VK(block->base.next) != VK_JUMP) {
			continue;
		}
		Block *succ = block_succs(block)[0];
		if (VK(succ->base.next) == VK_PHI) {
			// If the (only) successors has phi nodes, than bail
			// out, since we currently are not able to handle it.
			//continue;
		}
		// Block is empty and has only one successor. We can just
		// forward the jumps from predecessors to the successor.
		fprintf(stderr, "Threading block%zu to block%zu\n", block->base.index, succ->base.index);

		// Replace all references to `block` in its predecessors, to
		// point to `succ` instead.
		FOR_EACH_BLOCK_PRED(block, pred) {
			FOR_EACH_BLOCK_SUCC(*pred, s) {
				if (*s == block) {
					*s = succ;
					break;
				}
			}
		}

		// Swap-remove `block` from the list of predecessors of `succ`.
		// We access the private members `preds_` and `pred_cnt_`
		// directly so we need to be careful about invariants - in
		// particular, the array of predecessors is heap allocated and
		// has limited capacity. Since we only remove a predecessor, it
		// is fine.
		Block **preds = succ->preds_;
		for (size_t i = 0; i < succ->pred_cnt_; i++) {
			if (preds[i] == block) {
				preds[i] = preds[--succ->pred_cnt_];
				break;
			}
		}

		// Add all predecessors of `block` as predecessors to `succ`.
		FOR_EACH_BLOCK_PRED(block, p) {
			block_add_pred(succ, *p);
		}
	}

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
			Value *jump = create_unary(arena, VK_JUMP, &TYPE_VOID, &succ->base);
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
		Value *jump = create_unary(arena, VK_JUMP, &TYPE_VOID, &ret_block->base);
		jump->index = function->value_cnt++;
		jump->parent = &pred->base;
		remove_value(pred->base.prev);
		prepend_value(&pred->base, jump);
		block_add_pred(ret_block, pred);
	}

	Value *ret_inst;
	if (ret_void) {
		ret_inst = &create_operation(arena, VK_RETVOID, &TYPE_VOID, 0)->base;
	} else {
		Type *type = phis[0].value->type;
		Operation *phi = insert_phi(arena, ret_block, type);
		phi->base.index = function->value_cnt++;
		for (size_t i = 0; i < phi_cnt; i++) {
			phi->operands[i] = phis[i].value;
		}
		ret_inst = create_unary(arena, VK_RET, &TYPE_VOID, &phi->base);
	}
	ret_inst->index = function->value_cnt++;
	ret_inst->parent = &ret_block->base;
	prepend_value(&ret_block->base, ret_inst);

	garena_free(&gphis);

	// Recompute function->post_order, since we invalidated it.
	compute_preorder(function);
}

MFunction *
translate_function(Arena *arena, GArena *labels, Function *function)
{
	MFunction *mfunction = mfunction_create(arena, function, labels);

	TranslationState ts_ = {
		.arena = arena,
		.labels = labels,
		.index = function->value_cnt,
		.stack_space = 8,
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
	mfunction->stack_space = ts->stack_space;
	mfunction->make_stack_space = ts->make_stack_space;
	function->mfunction = mfunction;
	return mfunction;
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
	(void) arena;
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
			if (IK(inst) == IK_MOV && IM(inst) == M_Cr && IK(prev) != IK_CMOVCC && (IM(prev) == M_CI || IM(prev) == M_Cr || IM(prev) == M_CM) && IREG(prev) == IREG2(inst) && use_cnt[IREG(prev)] == 1) {
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

		// 	jz .L4 ; R
		// 	mov rdx, rsi
		// .L4:
		// =>
		//      cmovz rdx, rsi
		if (IK(last) == IK_MOV && IS(last) == MOV && IM(last) == M_Cr && IK(prev) == IK_JCC && ILABEL(prev) == next->block->base.index) {
			IK(last) = IK_CMOVCC;
			IS(last) = IS(prev);
			prev->prev->next = prev->next;
			prev->next->prev = prev->prev;
			block_use_cnt[next_block_index]--;
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
	error->msg = arena_vaprintf(&ec->arena, fmt, ap);
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

	RegAllocState *ras = reg_alloc_state_create(arena);
	GArena labels = {0};

	fprintf(stderr, "Globals:\n");
	print_globals(stderr, module);
	fprintf(stderr, "\n");
	for (size_t i = 0; i < function_cnt; i++) {
		if (!function_is_fully_defined(functions[i])) {
			continue;
		}
		number_values(functions[i], R__MAX);
		print_function(stderr, functions[i]);
		merge_simple_blocks(arena, functions[i]);
		print_function(stderr, functions[i]);
		thread_jumps(arena, functions[i]);
		print_function(stderr, functions[i]);
		value_numbering(arena, functions[i]);
		print_function(stderr, functions[i]);
		print_function(stderr, functions[i]);
		split_critical_edges(arena, functions[i]);
		print_function(stderr, functions[i]);
		single_exit(arena, functions[i]);
		print_function(stderr, functions[i]);
		///*
		translate_function(arena, &labels, functions[i]);
		calculate_def_use_info(functions[i]->mfunction);
		print_mfunction(stderr, functions[i]->mfunction);
		peephole(functions[i]->mfunction, arena, false);
		print_mfunction(stderr, functions[i]->mfunction);
		reg_alloc_function(ras, functions[i]->mfunction);
		print_mfunction(stderr, functions[i]->mfunction);
		calculate_def_use_info(functions[i]->mfunction);
		peephole(functions[i]->mfunction, arena, true);
		print_mfunction(stderr, functions[i]->mfunction);
		//*/
		//peephole(functions[i]->mfunc, arena);
	}

	///*
	reg_alloc_state_free(ras);

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
	for (size_t i = 0; i < module->string_cnt; i++) {
		StringLiteral *string = module->strings[i];
		printf("$str%zu:\n", i);
		printf("\tdb\t`");
		print_str(stdout, string->str);
		printf("`,0\n");
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
		Function *function = functions[i];
		printf("\n");
		if (function_is_fully_defined(function)) {
			printf("\tglobal ");
			print_str(stdout, functions[i]->name);
			printf("\n");
			print_mfunction(stdout, functions[i]->mfunction);
		} else {
			printf("\textern ");
			print_value(stdout, &functions[i]->base);
			printf("\n");
		}
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
		mfunction_free(function->mfunction);
	}
	garena_free(&labels);

	arena_free(&ec.arena);
	arena_free(arena);
	return ec.error_head ? EXIT_FAILURE : EXIT_SUCCESS;
}
