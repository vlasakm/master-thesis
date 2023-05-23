#pragma once

typedef struct Function Function;
typedef struct MFunction MFunction;
typedef struct Block Block;
typedef struct MBlock MBlock;

#include "utils.h"
#include "arena.h"
#include "str.h"
#include "type.h"

#define VALUE_KINDS(OT, OP, TERM) \
	OT(UNDEFINED, "undefined") \
	OT(NOP, "nop") \
	OT(CONSTANT, "constant") \
	OT(ALLOCA, "alloca") \
	OT(GLOBAL, "global") \
	OT(ARGUMENT, "argument") \
	OT(BLOCK, "block") \
	OT(FUNCTION, "function") \
	\
	OP(ADD,  "add",  2) \
	OP(SUB,  "sub",  2) \
	OP(MUL,  "mul",  2) \
	OP(UDIV, "udiv", 2) \
	OP(SDIV, "sdiv", 2) \
	OP(UREM, "urem", 2) \
	OP(SREM, "srem", 2) \
	OP(AND,  "and",  2) \
	OP(OR,   "or",   2) \
	OP(SHL,  "shl",  2) \
	OP(SAR,  "sar",  2) \
	OP(SLR,  "slr",  2) \
	\
	OP(NEG,  "neg",  1) \
	OP(NOT,  "not",  1) \
	\
	OP(EQ,   "eq",   2)  \
	OP(NEQ,  "neq",  2) \
	OP(ULT,  "ult",  2) \
	OP(ULEQ, "uleq", 2) \
	OP(UGT,  "ugt",  2) \
	OP(UGEQ, "ugeq", 2) \
	OP(SLT,  "slt",  2) \
	OP(SLEQ, "sleq", 2) \
	OP(SGT,  "sgt",  2) \
	OP(SGEQ, "sgeq", 2) \
	\
	OP(IDENTITY, "identity", 1) \
	OP(LOAD, "load", 1) \
	OP(STORE, "store", 2) \
	OP(GET_INDEX_PTR, "get_index_ptr", 2) \
	OP(GET_MEMBER_PTR, "get_member_ptr", 2) \
	OP(CALL, "call", 0) \
	OP(PHI, "phi", 0) \
	TERM(JUMP, "jump", 1) \
	TERM(BRANCH, "branch", 3) \
	TERM(RET, "ret", 1) \
	TERM(RETVOID, "retvoid", 0) \

typedef enum {
#define ENUM(kind, ...) VK_##kind,
VALUE_KINDS(ENUM, ENUM, ENUM)
#undef ENUM
} ValueKind;

extern char *value_kind_repr[];

extern u8 value_kind_param_cnt[];

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

typedef struct {
	Value base;
	int64_t k;
} Constant;

typedef struct {
	Value base;
	size_t size;
	bool optimizable;
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

#define VK(v) (((Value *) (v))->kind)
#define VINDEX(v) (((Value *) (v))->index)
#define VTYPE(v) (((Value *) (v))->type)
#define STORE_ADDR(v) (((Operation *) (v))->operands[0])
#define STORE_VALUE(v) (((Operation *) (v))->operands[1])
#define LOAD_ADDR(v) (((Operation *) (v))->operands[0])

void value_init(Value *value, ValueKind kind, Type *type);

bool value_is_terminator(Value *value);

Value ** value_operands(Value *value);
size_t value_operand_cnt(Value *value);

#define FOR_EACH_OPERAND(value, op) \
	for (Value **op = value_operands(value), **last = op + value_operand_cnt(value); op != last; op++)

void print_value(FILE *f, Value *v);

void prepend_value(Value *pos, Value *new);

void remove_value(Value *v);

Operation *create_operation(Arena *arena, Block *block, ValueKind kind, Type *type, size_t operand_cnt);

Value *create_unary(Arena *arena, Block *block, ValueKind kind, Type *type, Value *arg);

Operation *insert_phi(Arena *arena, Block *block, Type *type);


struct Block {
	Value base;
	MBlock *mblock;
	Block **preds_;
	size_t pred_cnt_;
	size_t pred_cap_;
	size_t filled_pred_cnt;
	bool pending;

	GArena incomplete_phis;
};

Block *create_block(Arena *arena, Function *function);

Block ** block_preds(Block *block);
size_t block_pred_cnt(Block *block);

Block ** block_succs(Block *block);
size_t block_succ_cnt(Block *block);

void block_add_pred(Block *block, Block *pred);
void block_add_pred_to_succs(Block *block);
size_t block_index_of_pred(Block *succ, Block *pred);
void append_to_block(Block *block, Value *new);

#define FOR_EACH_IN_BLOCK(block, v) \
	for (Value *v = (block)->base.next; v != &(block)->base; v = v->next)

#define FOR_EACH_IN_BLOCK_REV(block, v) \
	for (Value *v = (block)->base.prev; v != &(block)->base; v = v->prev)

#define FOR_EACH_PHI_IN_BLOCK(block, phi) \
	for (Operation *phi = (Operation *) (block)->base.next; VK(phi) == VK_PHI; phi = (Operation *) phi->base.next)

#define FOR_EACH_BLOCK_PRED(block, pred) \
	for (Block **pred = block_preds(block), **last = pred + block_pred_cnt(block); pred != last; pred++)

#define FOR_EACH_BLOCK_SUCC(block, succ) \
	for (Block **succ = block_succs(block), **last = succ + block_succ_cnt(block); succ != last; succ++)








struct Function {
	Value base;
	Str name;
	Argument *args;
	Block *entry;
	Block **blocks;
	Block **post_order;
	size_t block_cap;
	size_t block_cnt;
	size_t value_cnt;
	MFunction *mfunc;

	GArena *uses; // array of Value * for each Value * (by its index)
};

void compute_preorder(Function *function);

void print_function(FILE *f, Function *function);

void validate_function(Function *function);

size_t number_values(Function *function, size_t start_index);



typedef struct {
	size_t function_cnt;
	Function **functions;
	size_t global_cnt;
	Global **globals;
} Module;

void print_globals(FILE *f, Module *module);

Field * get_member(Value *value);
