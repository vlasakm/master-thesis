#define VALUE_KINDS(OT, OP, TERM) \
	OT(UNDEFINED, "undefined") \
	OT(NOP, "nop") \
	OT(IDENTITY, "identity") \
	OT(CONSTANT, "constant") \
	OT(ALLOCA, "alloca") \
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
	uint64_t index;
} Argument;

typedef struct {
	Value base;
	Value *operands[];
} Operation;

typedef struct {
	Value base;
	Value *head;
	Value *tail;
} Block;

typedef struct {
	Value base;
	Str name;
	Block *entry;
	size_t block_cnt;
} Function;


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

#define INSTRUCTIONS(_) \
	_(ADD, "add D0 S1", 1, 2, 0, 0) \
	_(OR, "or D0, S1", 1, 2, 0, 0) \
	_(AND, "and D0, S1", 1, 2, 0, 0) \
	_(SUB, "sub D0, S1", 1, 2, 0, 0) \
	_(XOR, "xor D0, S1", 1, 2, 0, 0) \
	_(CMP, "cmp D0, S1", 1, 2, 0, 0) \
	_(TEST, "test D0, S1", 1, 2, 0, 0) \
	_(NOT, "not D0, S0", 1, 1, 0, 0) \
	_(NEG, "neg D0, S0", 1, 1, 0, 0) \
	_(IMUL, "imul D0, S1", 1, 2, 0, 0) \
	_(IDIV, "idiv S2", 2, 3, 0, 0) \
	_(SHL, "shl D0, S1", 1, 2, 0, 0) \
	_(SHR, "shr D0, S1", 1, 2, 0, 0) \
	_(CALL, "call L0", 0, 0, 0, 1) \
	_(JMP, "jmp L0", 0, 0, 0, 1) \
	_(RET, "ret", 0, 0, 0, 0) \
	_(NOP, "nop", 0, 0, 0, 0) \
	_(JZ, "jz L0", 0, 0, 0, 1) \
	_(MOV, "mov D0, S0", 1, 1, 0, 0) \
	_(MOV_MR, "mov [S0], S1", 0, 2, 0, 0) \
	_(MOV_RM, "mov D0, [S0]", 1, 1, 0, 0) \
	_(LEA_RMC, "lea D0, [S0-I0]", 1, 1, 1, 0) \
	_(MOVIMM, "mov D0, I0", 1, 0, 1, 0) \

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
	Oper ops[];
};
