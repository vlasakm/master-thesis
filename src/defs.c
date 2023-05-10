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

typedef struct Inst Inst;
struct Inst {
	Inst *next;
	Inst *prev;
	u8 kind;
	u8 subkind;
	u8 mode;
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
#define IM(inst) ((inst)->mode)

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
	//IK_INCDEC, // INC, DEC
	IK__MAX,
} InstKind;

static const char *ik_repr[] = {
	"",
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
};

static const char *no_repr[] = {
	"",
};

enum {
	MOV,
	LEA,
};

static const char *mov_repr[] = {
	"mov",
	"lea",
};

static const char **is_repr[] = {
	no_repr,
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
	M_Rr,
	M_rr,
	M_Cr,
	M_RM,
	M_rM,
	M_CM,
	M_Mr,
	M_RI,
	M_rI,
	M_CI,
	M_MI,
	M_CrI,
	M_CMI,
	M_R,
	M_r,
	M_C,
	M_M,
	M_I,
	M_L,
	M_NONE,
	M_CALL,
	M_RET,
	M_ADr,
	M_ADM,
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
	[M_NONE] = { 0, 0, 0, 0,  0, none, none },
	[M_CALL] = { 0, 0, 0, 0,  1, caller_saved, argument_regs },
	[M_RET]  = { 0, 0, 0, 1,  0, none, callee_saved }, // hack for use of R_RAX (and potentially R_RDX)
	[M_ADr]  = { 0, 0, 0, 1,  0, rax_rdx, rax_rdx },
	[M_ADM]  = { 0, 0, 1, 3,  0, rax_rdx, rax_rdx },
};

typedef struct {
	Block *block;
	size_t index;
	Inst insts;
	Inst *last;
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