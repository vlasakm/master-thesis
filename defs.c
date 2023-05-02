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

typedef i32 Oper;

typedef struct {
	const char *format;
	size_t dest_cnt;
	size_t src_cnt;
	size_t imm_cnt;
	size_t label_cnt;
} InstDesc;

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

typedef enum {
#define ENUM(kind, ...) OP_##kind,
INSTRUCTIONS(ENUM)
#undef ENUM
} OpCode;

InstDesc inst_desc[] = {
#define DESC(kind, fmt, dest, src, imm, lbl) { .format = fmt, .dest_cnt = dest, .src_cnt = dest + src, .imm_cnt = dest + src + imm, .label_cnt = dest + src + imm + lbl, },
INSTRUCTIONS(DESC)
#undef DESC
};

typedef struct Inst Inst;

struct Inst {
	OpCode op;
	Inst *prev;
	Inst *next;
	Oper ops[];
};

typedef struct {
	Block *block;
	size_t index;
	Inst *first;
	Inst *last;
} MBlock;

struct MFunction {
	Function *func;
	MBlock *mblocks;
	size_t mblock_cnt;
	size_t stack_space;
	size_t vreg_cnt;
	Inst *make_stack_space;
};
