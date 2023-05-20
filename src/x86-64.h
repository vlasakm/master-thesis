#pragma once

#include "inst.h"

#define IREG(inst) ((inst)->ops[0])
#define IREG1(inst) ((inst)->ops[0])
#define ILABEL(inst) ((inst)->ops[0])
#define IBASE(inst) ((inst)->ops[1])
#define IREG2(inst) ((inst)->ops[1])
#define IINDEX(inst) ((inst)->ops[2])
#define ISCALE(inst) ((inst)->ops[3])
#define IDISP(inst) ((inst)->ops[4])
#define IIMM(inst) (((inst)->ops[5]))
#define IARG_CNT(inst) ((inst)->ops[5])

void set_imm64(Inst *inst, u64 imm);
u64 get_imm64(Inst *inst);
bool pack_into_oper(u64 value, Oper *op);

// R = RW register
// r = R register
// C = W register ("clobber")
// n = no read or write (for xor rax, rax, where read dependency is undesirable)
// M = memory (base R, index R, scale, displacement)
// I = 64-bit immediate
// i = 32-bit immediate
// L = label
// A = RW rax
// D = RW rdx
typedef enum {
	M_Rr,
	M_rr,
	M_Cr,
	M_Cn,
	M_RM,
	M_rM,
	M_CM,
	M_Mr,
	M_Ri,
	M_ri,
	M_CI,
	M_Mi,
	M_Cri,
	M_CMi,
	M_R,
	M_r,
	M_C,
	M_M,
	M_I,
	M_L,
	M_NONE,
	M_LCALL,
	M_rCALL,
	M_MCALL,
	M_RET,
	M_ENTRY,
	M_ADr,
	M_ADM,
	M_AD,
} X86Mode;

typedef enum {
	R_NONE = 0,
	R_RAX,
	R_RBX,
	R_RCX,
	R_RDX,
	R_RSI,
	R_RDI,
	R_8,
	R_9,
	R_10,
	R_11,
	R_12,
	R_13,
	R_14,
	R_15,

	R_RSP,
	R_RBP,

	R__RIP,
	R__MAX,
} Reg;

typedef enum {
	CC_O = 0x00,
	CC_NO = 0x01,
	CC_B = 0x02,
	CC_NAE = 0x02,
	CC_C = 0x02,
	CC_NB = 0x03,
	CC_AE = 0x03,
	CC_NC = 0x03,
	CC_Z = 0x04,
	CC_E = 0x04,
	CC_NZ = 0x05,
	CC_NE = 0x05,
	CC_BE = 0x06,
	CC_NA = 0x06,
	CC_NBE = 0x07,
	CC_A = 0x07,
	CC_S = 0x08,
	CC_NS = 0x09,
	CC_P = 0x0A,
	CC_PE = 0x0A,
	CC_NP = 0x0B,
	CC_PO = 0x0B,
	CC_L = 0x0C,
	CC_NGE = 0x0C,
	CC_NL = 0x0D,
	CC_GE = 0x0D,
	CC_LE = 0x0E,
	CC_NG = 0x0E,
	CC_NLE = 0x0F,
	CC_G = 0x0F,
} CondCode;


typedef enum {
	F_CF = UINT32_C(1) << 0, // Carry
	F_PF = UINT32_C(1) << 2, // Parity
	F_AF = UINT32_C(1) << 4, // Auxiliary Carry
	F_ZF = UINT32_C(1) << 6, // Zero
	F_SF = UINT32_C(1) << 7, // Sign
	F_OF = UINT32_C(1) << 11, // Overflow
} Flags;

typedef enum {
	G1_ADD,
	G1_OR,
	G1_ADC,
	G1_SBB,
	G1_AND,
	G1_SUB,
	G1_XOR,
	G1_CMP,

	G1_IMUL,
	G1_TEST,
} X86Group1;

typedef enum {
	G2_ROL,
	G2_ROR,
	G2_RCL,
	G2_RCR,
	G2_SHL,
	G2_SHR,
	G2_SAL,
	G2_SAR,
} X86Group2;

typedef enum {
	G3_TEST,
	G3_TEST2,
	G3_NOT,
	G3_NEG,
	G3_MUL,
	G3_IMUL,
	G3_DIV,
	G3_IDIV,
} X86Group3;

enum {
	MOV,
	LEA,
};

typedef enum {
	//IK_HEAD, // Machine Function or Machine Basic Block (head of the doubly linked list)
	IK_FUNCTION, // Machine Function (head of the doubly linked list)
	IK_BLOCK, // Machine Basic Block (head of the doubly linked list)
	IK_MOV, // MOV, LEA, ZX8, SX16, ...
	IK_BINALU, // ADD, SUB, ...
	IK_UNALU, // NEG, NOT
	IK_IMUL3,
	IK_SHIFT, // SHR, ROL, ...
	IK_JUMP, // JMP
	IK_CALL, // CALL
	IK_JCC, // JZ, JG, ...
	IK_SETCC, // SETZ, SETG, ...
	IK_CMOVCC, // CMOVZ, CMOVG, ...
	IK_MULDIV, // MUL, DIV, IMUL, IDIV
	IK_RET,
	IK_NOP,
	IK_LEAVE,
	IK_PUSH,
	IK_POP,
	IK_INCDEC, // INC, DEC
	IK_CQO, // sign extend RAX into RDX
	IK_ENTRY,
	IK__MAX,
} InstKind;

void print_reg(FILE *f, Oper reg);
void print_inst(FILE *f, MFunction *mfunction, Inst *inst);
bool mode_has_memory(X86Mode m);
CondCode cc_invert(CondCode cc);

extern Oper rax_rdx[];
extern Oper callee_saved[];
extern Oper saved[5];
extern Oper caller_saved[];
extern Oper argument_regs[7];
extern InsFormat formats[];
