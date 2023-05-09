#define VALUE_KINDS(OT, OP, TERM) \
	OT(UNDEFINED, "undefined") \
	OT(NOP, "nop") \
	OT(IDENTITY, "identity") \
	OT(CONSTANT, "constant") \
	OT(ALLOCA, "alloca") \
	OT(GLOBAL, "global") \
	OT(ARGUMENT, "argument") \
	OT(BLOCK, "block") \
	OT(FUNCTION, "function") \
	\
	OP(ADD, "add", 2) \
	OP(SUB, "sub", 2) \
	OP(MUL, "mul", 2) \
	OP(DIV, "div", 2) \
	OP(MOD, "mod", 2) \
	OP(AND, "and", 2) \
	OP(OR,  "or",  2) \
	OP(SHL, "shl", 2) \
	OP(SHR, "shr", 2) \
	\
	OP(NEG, "neg", 1) \
	OP(NOT, "not", 1) \
	\
	OP(EQ,  "eq",  2)  \
	OP(NEQ, "neq", 2) \
	OP(LT,  "lt",  2) \
	OP(LEQ, "leq", 2) \
	OP(GT,  "gt",  2) \
	OP(GEQ, "geq", 2) \
	\
	OP(LOAD, "load", 1) \
	OP(STORE, "store", 2) \
	OP(GET_INDEX_PTR, "get_index_ptr", 2) \
	OP(GET_MEMBER_PTR, "get_member_ptr", 2) \
	OP(CALL, "call", 0) \
	TERM(JUMP, "jump", 1) \
	TERM(BRANCH, "branch", 3) \
	TERM(RET, "ret", 1) \
	TERM(RETVOID, "retvoid", 0) \

typedef enum {
#define ENUM(kind, ...) VK_##kind,
VALUE_KINDS(ENUM, ENUM, ENUM)
#undef ENUM
} ValueKind;

typedef struct Value Value;

struct Value {
	ValueKind kind;
	u8 visited;
	Type *type;
	size_t index;
	Value *parent;
	Value *prev;
	Value *next;
};

void
value_init(Value *value, ValueKind kind, Type *type, Value *parent)
{
	*value = (Value) { .kind = kind, .type = type, .parent = parent };
}

char *value_kind_repr[] = {
#define REPR(kind, repr, ...) repr,
VALUE_KINDS(REPR, REPR, REPR)
#undef REPR
};

u8 value_kind_param_cnt[] = {
#define OP_PARAM_CNT(kind, repr, param_cnt) param_cnt,
#define NO_PARAM(...) 0,
VALUE_KINDS(NO_PARAM, OP_PARAM_CNT, OP_PARAM_CNT)
#undef OP_PARAM_CNT
#undef NO_PARAM
};

typedef struct {
	Value base;
	int64_t k;
} Constant;

typedef struct {
	Value base;
	size_t size;
} Alloca;

typedef struct {
	Value base;
	Str name;
	Value *init;
} Global;

typedef struct {
	Value base;
	uint64_t index;
} Argument;

typedef struct {
	Value base;
	Value *operands[];
} Operation;

typedef struct Block Block;

struct Block {
	Value base;
	Value *head;
	Value *tail;
	Block **preds;
	size_t pred_cnt;
	Block *succs[2];
	size_t succ_cnt;
};

typedef struct Function Function;
typedef struct MFunction MFunction;

struct Function {
	Value base;
	Str name;
	Block *entry;
	Block **post_order;
	size_t block_cnt;
	MFunction *mfunc;
};

/*
#define INST_KINDS(_) \
	_(ADD) \
	_(OR) \
	_(AND) \
	_(SUB) \
	_(XOR) \
	_(CMP) \
	_(TEST) \
	_(NOT) \
	_(NEG) \
	_(IMUL) \
	_(IDIV) \
	_(SHL) \
	_(SHR) \
	_(CALL) \
	_(JMP) \
	_(RET) \
	_(NOP) \
	_(JZ) \
	_(MOV) \
	_(LABEL)

typedef enum {
#define ENUM(kind, ...) IK_##kind,
INST_KINDS(ENUM)
#undef ENUM
} InstKind;

char *inst_kind_repr[] = {
#define REPR(kind, ...) #kind,
INST_KINDS(REPR)
#undef REPR
};
*/

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

#define INSTRUCTIONS(_) \
	_(BIN_RR, "G1:0 S0, S1", 1, 2, 1, 0) \
	_(BIN_RI, "G1:0 S0, I1", 1, 1, 2, 0) \
	_(SHIFT_RR, "G2:0 D0, S1", 1, 2, 1, 0) \
	_(UNARY_RR, "G3:0 D0, S1", 1, 1, 1, 0) \
	_(TEST, "test S0, S1", 0, 2, 0, 0) \
	_(IMUL, "imul D0, S1", 1, 2, 0, 0) \
	_(IMUL_IMM, "imul D0, S0, I0", 1, 1, 1, 0) \
	_(IDIV, "idiv S2", 2, 3, 0, 0) \
	_(CALL, "call F0", 5, 4, 0, 1) \
	_(JMP, "jmp B0", 0, 0, 0, 1) \
	_(RET, "ret", 0, 2, 0, 0) \
	_(SYSCALL, "syscall", 0, 0, 0, 0) \
	_(NOP, "nop", 0, 0, 0, 0) \
	_(JCC, "jC0 B0", 0, 0, 1, 1) \
	_(MOV, "mov D0, S0", 1, 1, 0, 0) \
	_(MOV_MR, "mov [S0], S1", 0, 2, 0, 0) \
	_(MOV_MI, "mov qword [S0], I0", 0, 1, 1, 0) \
	_(MOV_RM, "mov D0, [S0]", 1, 1, 0, 0) \
	_(LEA_RMC, "lea D0, [S0-I0]", 1, 1, 1, 0) \
	_(LEA_RG, "lea D0, [g0]", 1, 0, 0, 1) \
	_(MOV_RG, "mov D0, [g0]", 1, 0, 0, 1) \
	_(MOV_RMC, "mov D0, [S0-I0]", 1, 1, 1, 0) \
	_(MOV_MCR, "mov [S0-I0], S1", 0, 2, 1, 0) \
	_(MOVIMM, "mov D0, I0", 1, 0, 1, 0) \
	_(SETCC, "setC0 E0", 1, 0, 1, 0) \
	_(PUSH, "push S0", 0, 1, 0, 0) \
	_(POP, "pop D0", 1, 0, 0, 0) \
	_(SUB_IMM, "sub D0, I0", 1, 1, 1, 0) \

typedef struct Inst Inst;
struct Inst {
	Inst *next;
	Inst *prev;
	u8 kind;
	u8 subkind;
	u8 mode;
	bool direction; // true => reg, reg/mem | false => reg/mem, reg
	bool is_first_def; // is reg defined?
	bool is_memory; // is the second reg/mem arg reg or mem?
	bool has_imm; // does the instruction have an immediate operand?
	Oper ops[];
	//Oper reg;
	//union {
	//     Oper base; // or second reg
	//     Oper reg2; // or second reg
	//};
	//Oper index;
	//Oper scale;
	//Oper disp;
	//Oper imm;
};

#define IK(inst) ((inst)->kind)
#define IS(inst) ((inst)->subkind)

#define IREG(inst) ((inst)->ops[0])
#define IREG1(inst) ((inst)->ops[0])
#define IBASE(inst) ((inst)->ops[1])
#define IREG2(inst) ((inst)->ops[1])
#define IINDEX(inst) ((inst)->ops[2])
#define ISCALE(inst) ((inst)->ops[3])
#define IDISP(inst) ((inst)->ops[4])
#define IIMM(inst) ((inst)->ops[5])
#define IARG_CNT(inst) ((inst)->ops[0])
#define IRET_CNT(inst) ((inst)->ops[0])

typedef enum {
	//IK_HEAD, // Machine Function or Machine Basic Block (head of the doubly linked list)
	IK_FUNCTION, // Machine Function (head of the doubly linked list)
	IK_BLOCK, // Machine Basic Block (head of the doubly linked list)
	IK_MOV, // MOV, LEA, ZX8, SX16, ... // 0-1 : 1-3
	IK_BINALU, // ADD, SUB, ... // 0-1 : 1-3
	IK_UNALU, // NEG, NOT // 0-1 : 1-3
	IK_IMUL3,
	IK_SHIFT, // SHR, ROL, ... // 0-1 : 1-3
	IK_JUMP, // JMP
	IK_CALL, // CALL
	IK_JCC, // JZ, JG, ...
	IK_SETCC, // SETZ, SETG, ... // 1 : 0
	IK_CMOVCC, // CMOVZ, CMOVG, ... // 1 : 1-3
	IK_MULDIV, // MUL, DIV, IMUL, IDIV // 0 : 1-3
	IK_RET,
	IK_NOP,
	IK_LEAVE,
	IK_PUSH, // 0 : 1-3
	IK_POP, // 0-1 : 1-3
	IK_INCDEC, // INC, DEC
	IK__MAX,
} InstKind;

enum {
	MOV,
	LEA,
};

// R = RW register
// r = R register
// C = W register ("clobber")
// M = memory (base R, index R, scale, displacement)
// I = immediate
// L = label
// A = RW rax
// D = RW rdx
typedef enum {
	M_Rr,   // direction = true,  is_first_def = true,  is_memory = false, has_imm = false
	M_rr,   // direction = true,  is_frist_def = false, is_memory = false, has_imm = false
	M_Cr,   // direction = true,  is_first_def = true,  is_memory = false, has_imm = false
	M_RM,   // direction = true,  is_first_def = true,  is_memory = true,  has_imm = false
	M_rM,
	M_CM,   // direction = true,  is_first_def = true,  is_memory = true,  has_imm = false
	M_Mr,   // direction = false, is_first_def = false, is_memory = true,  has_imm = false
	M_RI,   // direction = true,  is_frist_def = true,  is_memory = false, has_imm = false
	M_rI,
	M_CI,   // direction = true,  is_first_def = true,  is_memory = false, has_imm = true
	M_MI,
	M_CrI,  // direction = true,  is_first_def = true,  is_memory = false, has_imm = true
	M_CMI,
	M_R,    // direction = true,  is_first_def = true,  is_memory = false, has_imm = false
	M_r,    // direction = true,  is_first_def = false, is_memory = false, has_imm = false
	M_C,    // direction = true,  is_first_def = true,  is_memory = false, has_imm = false
	M_M,
	M_I,
	M_L,    // direction = true,  is_first_def = false, is_memory = false, has_imm = false
	M_N,    // direction = true,  is_first_def = false, is_memory = false, has_imm = false
	M_CALL, // direction = true,  is_first_def = false, is_memory = false, has_imm = false
	M_RET,  // direction = true,  is_first_def = false, is_memory = false, has_imm = false
	M_ADr,  // direction = true,  is_first_def = false, is_memory = false, has_imm = false
	M_ADM,  // direction = true,  is_first_def = false, is_memory = true, has_imm = false
} X86Mode;

typedef struct {
	u8 def_start;
	u8 def_end;
	u8 use_start;
	u8 use_end;
	bool use_cnt_given_by_first;
	Oper *extra_defs;
	Oper *extra_uses;
} InsFormat;


static Oper none[] = { R_NONE };

static Oper rax_rdx[] = { R_RAX, R_RDX, R_NONE };
static Oper callee_saved[] = { R_RBX, R_RBP, R_RSP, R_NONE };
static Oper saved[] = { R_RBX };
static Oper caller_saved[] = { R_RAX, R_RCX, R_RDX, R_RSI, R_RDI, R_NONE };
static Oper argument_regs[] = { R_RDI, R_RSI, R_RDX, R_RCX, R_NONE };
//static Oper return_regs[] = { R_RAX, R_RDX, R_NONE };


InsFormat formats[] = {
	[M_Rr]   = { 0, 1, 0, 2,  0, none, none },
	[M_rr]   = { 0, 0, 0, 2,  0, none, none },
	[M_Cr]   = { 0, 1, 1, 2,  0, none, none },
	[M_RM]   = { 0, 1, 0, 3,  0, none, none },
	[M_rM]   = { 0, 0, 0, 3,  0, none, none },
	[M_CM]   = { 0, 1, 1, 3,  0, none, none },
	[M_Mr]   = { 0, 0, 0, 3,  0, none, none },
	[M_RI]   = { 0, 1, 0, 1,  0, none, none },
	[M_rI]   = { 0, 0, 0, 1,  0, none, none },
	[M_CI]   = { 0, 1, 0, 0,  0, none, none },
	[M_MI]   = { 0, 0, 1, 3,  0, none, none },
	[M_CrI]  = { 0, 1, 1, 2,  0, none, none },
	[M_CMI]  = { 0, 1, 1, 3,  0, none, none },
	[M_R]    = { 0, 1, 0, 1,  0, none, none },
	[M_r]    = { 0, 0, 0, 1,  0, none, none },
	[M_C]    = { 0, 1, 0, 0,  0, none, none },
	[M_M]    = { 0, 0, 1, 3,  0, none, none },
	[M_I]    = { 0, 0, 0, 0,  0, none, none },
	[M_L]    = { 0, 0, 0, 0,  0, none, none },
	[M_N]    = { 0, 0, 0, 0,  0, none, none },
	[M_CALL] = { 0, 0, 0, 0,  1, caller_saved, argument_regs },
	[M_RET]  = { 0, 0, 0, 1,  0, none, callee_saved }, // hack for use of R_RAX (and potentially R_RDX)
	[M_ADr]  = { 0, 0, 0, 1,  0, rax_rdx, rax_rdx },
	[M_ADM]  = { 0, 0, 1, 3,  0, rax_rdx, rax_rdx },
};

typedef struct {
	char *fmt;
	u8 *extra_defs;
	u8 *extra_uses;
	u8 *maybe_uses;
} InsDesc;

//u32 bitmap of defs / saves ?
//u32 bitmap of def / save indices ?
//extra handling of calls?

// Reuse reg for imm? What about 3 operand imul?

// sets_flags
// reads_flags
// reads_regs [RAX, RDX, ...]
// writes_regs [...]

// OP mem64, reg64
// kind = BINARITH
// subkind = ADD / OR / SUB / ...
// first_is_destination = false
// is_memory = true
// is_immediate = false
// reg = reg64
// scale/base/index/disp = mem64
// imm = 0

// OP reg64, mem64
// kind = BINARITH
// subkind = ADD / OR / SUB / ...
// first_is_destination = true
// is_memory = true
// is_immediate = false
// reg = reg64
// scale/base/index/disp = mem64
// imm = 0

// OP reg64A, reg64B
// kind = BINARITH
// subkind = ADD / OR / SUB / ...
// first_is_destination = true
// is_memory = false
// is_immediate = false
// reg = reg64A
// base = reg64B
// imm = 0

// OP reg64, imm
// kind = BINARITH
// subkind = ADD / OR / SUB / ...
// first_is_destination = true
// is_memory = false
// is_immediate = true
// reg = reg64
// imm = imm

// OP mem64, imm
// kind = BINARITH
// subkind = ADD / OR / SUB / ...
// first_is_destination = false
// is_memory = true
// is_immediate = true
// reg = 0
// scale/base/index/disp = mem64
// imm = imm

// CMP mem64, reg64
// kind = BINARITH
// subkind = CMP
// first_is_destination = false
// is_memory = true
// is_immediate = false
// reg = reg64
// scale/base/index/disp = mem64
// imm = 0

// CMP reg64, mem64
// kind = BINARITH
// subkind = CMP
// first_is_destination = false
// is_memory = true
// is_immediate = false
// reg = reg64
// scale/base/index/disp = mem64
// imm = 0

// CMP reg64A, reg64B
// kind = BINARITH
// subkind = CMP
// first_is_destination = false
// is_memory = false
// is_immediate = false
// reg = reg64A
// base = reg64B
// imm = 0

// CMP reg64, imm
// kind = BINARITH
// subkind = CMP
// first_is_destination = false
// is_memory = false
// is_immediate = true
// reg = reg64
// imm = imm

// CMP mem64, imm
// kind = BINARITH
// subkind = CMP
// first_is_destination = false
// is_memory = true
// is_immediate = true
// reg = 0
// scale/base/index/disp = mem64
// imm = imm

// TEST mem64, reg64
// kind = BINARITH
// subkind = TEST
// first_is_destination = false
// is_memory = true
// is_immediate = false
// reg = reg64
// scale/base/index/disp = mem64
// imm = 0

// TEST reg64A, reg64B
// kind = BINARITH
// subkind = TEST
// first_is_destination = false
// is_memory = false
// is_immediate = false
// reg = reg64A
// base = reg64B
// imm = 0

// TEST reg64, imm
// kind = BINARITH
// subkind = TEST
// first_is_destination = false
// is_memory = false
// is_immediate = true
// reg = reg64
// imm = imm

// TEST mem64, imm
// kind = BINARITH
// subkind = TEST
// first_is_destination = false
// is_memory = true
// is_immediate = true
// reg = 0
// scale/base/index/disp = mem64
// imm = imm

// OP mem64
// kind = UNARITH
// subkind = NOT / NEG
// first_is_destination = false
// is_memory = true
// is_immediate = false
// reg = 0
// scale/base/index/disp = mem64
// imm = 0

// OP reg64
// kind = UNARITH
// subkind = NOT / NEG
// first_is_destination = true
// is_memory = false
// is_immediate = false
// reg = reg64
// scale/base/index/disp = 0
// imm = 0

// SHIFT mem64, imm8
// kind = SHL / SHR
// subkind = SHL / SHR / ...
// first_is_destination = false
// is_memory = true
// is_immediate = true
// reg = 0
// scale/base/index/disp = mem64
// imm = imm8

// SHIFT reg64, imm8
// kind = SHL / SHR
// subkind = SHL / SHR / ...
// first_is_destination = true
// is_memory = false
// is_immediate = true
// reg = reg64
// scale/base/index/disp = 0
// imm = imm8

// SHIFT mem64, cl
// kind = SHL / SHR
// subkind = SHL / SHR / ...
// first_is_destination = false
// is_memory = true
// is_immediate = false
// reg = cl
// scale/base/index/disp = mem64
// imm = 0

// SHIFT reg64, cl
// kind = SHL / SHR
// subkind = SHL / SHR / ...
// first_is_destination = true
// is_memory = false
// is_immediate = true
// reg = reg64
// scale/base/index/disp = cl
// imm = 0

// JUMP/CALL label
// kind = ControlFlow
// subkind = JUMP / CALL
// first_is_destination = false
// is_memory = false
// is_immediate = true
// reg = 0
// scale/base/index/disp = 0
// imm = label

// JUMP/CALL reg64
// kind = ControlFlow
// subkind = JUMP / CALL
// first_is_destination = false
// is_memory = false
// is_immediate = false
// reg = reg64
// scale/base/index/disp = 0
// imm = 0

// JUMP/CALL mem64
// kind = ControlFlow
// subkind = JUMP / CALL
// first_is_destination = false
// is_memory = true
// is_immediate = false
// reg = 0
// scale/base/index/disp = mem64
// imm = 0

// JCC label
// kind = ControlFlow
// subkind = O / E / Z / NZE
// first_is_destination = false
// is_memory = false
// is_immediate = true
// reg = 0
// scale/base/index/disp = 0
// imm = label

// RET/LEAVE
// kind = ARGUMENTLESS
// subkind = RET / LEAVE
// first_is_destination = false
// is_memory = false
// is_immediate = false
// reg = 0
// scale/base/index/disp = 0
// imm = 0

// RET/LEAVE
// kind = ARGUMENTLESS
// subkind = RET / LEAVE
// first_is_destination = false
// is_memory = false
// is_immediate = false
// reg = 0
// scale/base/index/disp = 0
// imm = 0

// OP mem8
// kind = SETCC
// subkind = O / E / Z / NE
// first_is_destination = false
// is_memory = true
// is_immediate = false
// reg = 0
// scale/base/index/disp = mem64
// imm = 0

// OP reg8
// kind = SETCC
// subkind = O / E / Z / NE
// first_is_destination = true
// is_memory = false
// is_immediate = false
// reg = reg64
// scale/base/index/disp = 0
// imm = 0

// IMUL reg64A, reg64B, imm
// kind = IMUL3
// subkind = IMUL3
// first_is_destination = true
// is_memory = false
// is_immediate = true
// reg = reg64A
// scale/base/index/disp = reg64B
// imm = imm

// IMUL reg64, mem64, imm
// kind = IMUL3
// subkind = IMUL3
// first_is_destination = true
// is_memory = true
// is_immediate = true
// reg = reg64
// scale/base/index/disp = mem64
// imm = imm

// PUSH imm
// kind = STACK
// subkind = PUSH
// first_is_destination = false
// is_memory = false
// is_immediate = true
// reg = 0
// scale/base/index/disp = 0
// imm = imm

// "%s%s" str[kind], str[subkind]

// Mapping from mnemonic to some kind of flag or whatever, so we can only have
// kind, instead of kind + subkind?

typedef struct {
	Block *block;
	size_t index;
	Inst insts;
} MBlock;

struct MFunction {
	Function *func;
	Inst insts;
	MBlock **mblocks;
	size_t mblock_cnt;
	size_t stack_space;
	size_t vreg_cnt;
	Inst *make_stack_space;
};
