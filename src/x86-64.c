#include "x86-64.h"

static const char *reg_repr[] = {
	"NONE",
	"rax",
	"rbx",
	"rcx",
	"rdx",
	"rsi",
	"rdi",
	"r8",
	"r9",
	"r10",
	"r11",
	"r12",
	"r13",
	"r14",
	"r15",

	"rsp",
	"rbp",
};

static const char *reg_repr8[] = {
	"NONE",
	"al",
	"bl",
	"cl",
	"dl",
	"sil",
	"dil",
	"r8b",
	"r9b",
	"r10b",
	"r11b",
	"r12b",
	"r13b",
	"r14b",
	"r15b",

	"spl",
	"bpl",
};

static const char *cc_repr[] = {
	"o",
	"no",
	"b",
	"ae",
	"z",
	"nz",
	"be",
	"a",
	"s",
	"ns",
	"p",
	"np",
	"l",
	"ge",
	"le",
	"g",
};

CondCode
cc_invert(CondCode cc)
{
	// Flip the least significant bit.
	return cc ^ 1;
}

u32
cc_read_flags(CondCode cc)
{
	switch (cc) {
	case CC_O:
	case CC_NO:
		return F_OF;
	case CC_B:
	case CC_AE:
		return F_CF;
	case CC_Z:
	case CC_NZ:
		return F_ZF;
	case CC_BE:
	case CC_A:
		return F_CF | F_ZF;
	case CC_S:
	case CC_NS:
		return F_SF;
	case CC_P:
	case CC_NP:
		return F_PF;
	case CC_L:
	case CC_GE:
		return F_SF | F_OF;
	case CC_LE:
	case CC_G:
		return F_SF | F_ZF | F_OF;
	default:
		UNREACHABLE();
	}
}

static const char *g1_repr[] = {
	"add",
	"or",
	"adc",
	"sbb",
	"and",
	"sub",
	"xor",
	"cmp",

	"imul",
	"test",
};

static const char *g2_repr[] = {
	"rol",
	"ror",
	"rcl",
	"rcr",
	"shl",
	"shr",
	"sal",
	"sar",
};

static const char *g3_repr[] = {
	"test",
	"test",
	"not",
	"neg",
	"mul",
	"imul",
	"div",
	"idiv",
};

bool
g1_is_commutative(X86Group1 g1)
{
	switch (g1) {
	case G1_ADD:
	case G1_IMUL:
	case G1_AND:
	case G1_OR:
	case G1_TEST:
		return true;
	default:
		return false;
	}
}

static const char *ik_repr[] = {
	"",
	"",
	"",
	"",
	"imul",
	"",
	"jmp",
	"call",
	"j",
	"set",
	"cmov",
	"",
	"ret",
	"nop",
	"leave",
	"push",
	"pop",
	"",
	"cqo",
	"; entry",
};

static const char *no_repr[] = {
	"",
};

static const char *mov_repr[] = {
	"mov",
	"lea",
	"movsx",
	"mov",
};

static const char **is_repr[] = {
	no_repr,
	mov_repr,
	g1_repr,
	g3_repr,
	no_repr,
	g2_repr,
	no_repr,
	no_repr,
	cc_repr,
	cc_repr,
	cc_repr,
	g3_repr,
	no_repr,
	no_repr,
	no_repr,
	no_repr,
	no_repr,
	no_repr,
	no_repr,
	no_repr,
};

bool
mode_has_memory(X86Mode m)
{
	switch (m) {
	case M_RM:
	case M_rM:
	case M_CM:
	case M_Mr:
	case M_Mi:
	case M_CMi:
	case M_M:
	case M_MCALL:
	case M_ADM:
	     return true;
	default:
	     return false;
	}
}

Oper none[] = { R_NONE };

Oper rax_rdx[] = { R_RAX, R_RDX, R_NONE };
Oper rax[] = { R_RAX, R_NONE };
Oper rdx[] = { R_RDX, R_NONE };
Oper callee_saved[] = { R_RBX, R_12, R_13, R_14, R_15, R_RBP, R_RSP, R_NONE };
Oper saved[] = { R_RBX, R_12, R_13, R_14, R_15 };
Oper caller_saved[] = { R_RAX, R_RCX, R_RDX, R_RSI, R_RDI, R_8, R_9, R_10, R_11, R_NONE };
Oper argument_regs[] = { R_RDI, R_RSI, R_RDX, R_RCX, R_8, R_9, R_NONE };
//static Oper return_regs[] = { R_RAX, R_RDX };


ModeDescriptor mode_descs[] = {
	[M_Rr]    = { 0, 1, 0, 2,  0, 0, none, none },
	[M_rr]    = { 0, 0, 0, 2,  0, 0, none, none },
	[M_Cr]    = { 0, 1, 1, 2,  0, 0, none, none },
	[M_Cn]    = { 0, 2, 0, 0,  0, 0, none, none },
	[M_RM]    = { 0, 1, 0, 3,  0, 0, none, none },
	[M_rM]    = { 0, 0, 0, 3,  0, 0, none, none },
	[M_CM]    = { 0, 1, 1, 3,  0, 0, none, none },
	[M_Mr]    = { 0, 0, 0, 3,  0, 0, none, none },
	[M_Ri]    = { 0, 1, 0, 1,  0, 0, none, none },
	[M_ri]    = { 0, 0, 0, 1,  0, 0, none, none },
	[M_CI]    = { 0, 1, 0, 0,  0, 0, none, none },
	[M_Mi]    = { 0, 0, 1, 3,  0, 0, none, none },
	[M_Cri]   = { 0, 1, 1, 2,  0, 0, none, none },
	[M_CMi]   = { 0, 1, 1, 3,  0, 0, none, none },
	[M_R]     = { 0, 1, 0, 1,  0, 0, none, none },
	[M_r]     = { 0, 0, 0, 1,  0, 0, none, none },
	[M_C]     = { 0, 1, 0, 0,  0, 0, none, none },
	[M_M]     = { 0, 0, 1, 3,  0, 0, none, none },
	[M_I]     = { 0, 0, 0, 0,  0, 0, none, none },
	[M_L]     = { 0, 0, 0, 0,  0, 0, none, none },
	[M_NONE]  = { 0, 0, 0, 0,  0, 0, none, none },
	[M_LCALL] = { 0, 0, 0, 0,  1, 0, caller_saved, argument_regs },
	[M_rCALL] = { 0, 0, 0, 1,  1, 0, caller_saved, argument_regs },
	[M_MCALL] = { 0, 0, 1, 3,  1, 0, caller_saved, argument_regs },
	[M_RET]   = { 0, 0, 0, 1,  0, 0, none, callee_saved }, // hack for use of R_RAX (and potentially R_RDX)
	[M_ENTRY] = { 0, 0, 0, 1,  0, 1, argument_regs, none },
	[M_ADr]   = { 0, 0, 0, 1,  0, 0, rax_rdx, rax_rdx },
	[M_ADM]   = { 0, 0, 1, 3,  0, 0, rax_rdx, rax_rdx },
	[M_AD]    = { 0, 0, 0, 0,  0, 0, rdx, rax },
};

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

void
set_imm64(Inst *inst, u64 imm)
{
	inst->ops[1] = imm;
	inst->ops[2] = imm >> 32;
}

u64
get_imm64(Inst *inst)
{
	return ((u64) inst->ops[1]) | ((u64) inst->ops[2] << 32);
}

static bool
is_imm32(u64 value)
{
	u32 high = value >> 32;
	return high == 0 || high == UINT32_MAX;
}

u64
sext_imm32(Oper op)
{
	return (op & 0x80000000) ? (0xFFFFFFFF00000000 | op) : op;
}

bool
pack_into_oper(u64 value, Oper *op)
{
	// Most instructions allow 32-bit signed immediates.
	if (is_imm32(value)) {
		*op = (u32) value;
		return true;
	}
	return false;
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
	//
	//     [base+scale*index+disp]

	ISCALE(dest) = ISCALE(src);
	IINDEX(dest) = IINDEX(src);
	IBASE(dest) = IBASE(src);
	IDISP(dest) = IDISP(src);

	// The other addressing mode is:
	//
	//     [rip+disp]
	//
	// It uses IBASE(inst) = R_NONE and the displacement is actually
	// label+displacement, which are encoded using ILABEL(inst) and
	// IDISP(inst). Since we copy IBASE IDISP above and ILABEL aliases with
	// ISCALE, which we also copied above, the code works for both cases.
}

void
copy_flags(Inst *dest, Inst *src)
{
	IRF(dest) = IRF(src);
	IWF(dest) = IWF(src);
	IOF(dest) = IOF(src);
}

void
print_reg(FILE *f, Oper reg)
{
	if (reg < R__MAX) {
		fprintf(f, "%s", reg_repr[reg]);
	} else {
		fprintf(f, "t%"PRIi32, reg);
	}
}

void
print_reg8(FILE *f, Oper reg)
{
	if (reg < R__MAX) {
		fprintf(f, "%s", reg_repr8[reg]);
	} else {
		fprintf(f, "t%"PRIi32, reg);
	}
}

void
print_label(FILE *f, MFunction *mfunction, Inst *inst)
{
	Value *value = garena_array(mfunction->labels, Value *)[ILABEL(inst)];
	print_value(f, value);
	if (VK(value) == VK_FUNCTION && !function_is_fully_defined((Function *) value)) {
		fprintf(f, " wrt ..plt");
	}
}

void
print_mem(FILE *f, MFunction *mfunction, Inst *inst)
{
	fprintf(f, "[");
	if (IBASE(inst) == R_NONE) {
		print_label(f, mfunction, inst);
	} else {
		print_reg(f, IBASE(inst));
		if (IINDEX(inst)) {
			fprintf(f, "+");
			if (ISCALE(inst) != 0) {
				fprintf(f, "%d*", 1 << ISCALE(inst));
			}
			print_reg(f, IINDEX(inst));
		}
	}
	if (IDISP(inst)) {
		fprintf(f, "%+"PRIi32, IDISP(inst));
	}
	fprintf(f, "]");
}

void
print_inst(FILE *f, MFunction *mfunction, Inst *inst)
{
	fprintf(f, "%s%s", ik_repr[IK(inst)], is_repr[IK(inst)][IS(inst)]);
	switch (inst->mode) {
	case M_Rr:
	case M_rr:
	case M_Cr:
	case M_Cn:
		fprintf(f, " ");
		print_reg(f, IREG1(inst));
		fprintf(f, ", ");
		if (IK(inst) == IK_SHIFT) {
			print_reg8(f, IREG2(inst));
		} else {
			print_reg(f, IREG2(inst));
		}
		break;
	case M_RM:
	case M_rM:
	case M_CM:
		fprintf(f, " ");
		print_reg(f, IREG(inst));
		fprintf(f, ", ");
		if (IK(inst) == IK_MOV && IS(inst) == MOVSX8) {
			fprintf(f, "byte ");
		}
		print_mem(f, mfunction, inst);
		break;
	case M_Mr:
		fprintf(f, " ");
		if (IK(inst) == IK_MOV && IS(inst) == MOV8) {
			fprintf(f, "byte ");
			print_mem(f, mfunction, inst);
			fprintf(f, ", ");
			print_reg8(f, IREG(inst));
		} else {
			print_mem(f, mfunction, inst);
			fprintf(f, ", ");
			print_reg(f, IREG(inst));
		}
		break;
	case M_Ri:
	case M_ri:
		fprintf(f, " ");
		print_reg(f, IREG(inst));
		fprintf(f, ", ");
		fprintf(f, "%"PRIi32, IIMM(inst));
		break;
	case M_CI:
		fprintf(f, " ");
		print_reg(f, IREG(inst));
		fprintf(f, ", ");
		fprintf(f, "%"PRIi64, get_imm64(inst));
		break;
	case M_Mi:
		fprintf(f, " ");
		if (IK(inst) == IK_MOV && IS(inst) == MOV8) {
			fprintf(f, "byte ");
		} else {
			fprintf(f, "qword ");
		}
		print_mem(f, mfunction, inst);
		fprintf(f, ", ");
		fprintf(f, "%"PRIi32, IIMM(inst));
		break;
	case M_Cri:
		fprintf(f, " ");
		print_reg(f, IREG1(inst));
		fprintf(f, ", ");
		print_reg(f, IREG2(inst));
		fprintf(f, ", ");
		fprintf(f, "%"PRIi32, IIMM(inst));
		break;
	case M_CMi:
		fprintf(f, " ");
		print_reg(f, IREG(inst));
		fprintf(f, ", ");
		print_mem(f, mfunction, inst);
		fprintf(f, "%"PRIi32, IIMM(inst));
		break;
	case M_R:
	case M_r:
	case M_C:
	case M_ADr:
	case M_rCALL:
		fprintf(f, " ");
		if (IK(inst) == IK_SETCC) {
			print_reg8(f, IREG(inst));
		} else {
			print_reg(f, IREG(inst));
		}
		break;
	case M_ADM:
	case M_M:
	case M_MCALL:
		fprintf(f, " ");
		print_mem(f, mfunction, inst);
		break;
	case M_I:
		fprintf(f, " ");
		fprintf(f, "%"PRIi32, IIMM(inst));
		break;
	case M_L:
		fprintf(f, " ");
		fprintf(f, ".L%"PRIi32, ILABEL(inst));
		break;
	case M_LCALL: {
		fprintf(f, " ");
		print_label(f, mfunction, inst);
		break;
	}
	case M_NONE:
		UNREACHABLE();
		break;
	case M_RET:
		break;
	}

	if (inst->reads_flags || inst->writes_flags || inst->flags_observed) {
		fprintf(f, " ; ");
		fprintf(f, "%s", inst->reads_flags ? "R" : "");
		fprintf(f, "%s", inst->writes_flags ? "W" : "");
		fprintf(f, "%s", inst->flags_observed ? "O" : "");
	}
}
