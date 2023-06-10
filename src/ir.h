#pragma once

typedef struct Function Function;
typedef struct MFunction MFunction;
typedef struct Block Block;
typedef struct MBlock MBlock;

#include "utils.h"
#include "arena.h"
#include "str.h"
#include "type.h"

#define VALUE_KINDS(_) \
	/* constants */              \
	_(UNDEFINED, "undefined", 0) \
	_(NOP,       "nop",       0) \
	_(CONSTANT,  "constant",  0) \
	_(STRING,    "string",    0) \
	_(ALLOCA,    "alloca",    0) \
	_(GLOBAL,    "global",    0) \
	_(ARGUMENT,  "argument",  0) \
	_(BLOCK,     "block",     0) \
	_(FUNCTION,  "function",  0) \
	\
	_(ADD,  "add",  2) \
	_(SUB,  "sub",  2) \
	_(MUL,  "mul",  2) \
	_(UDIV, "udiv", 2) \
	_(SDIV, "sdiv", 2) \
	_(UREM, "urem", 2) \
	_(SREM, "srem", 2) \
	_(AND,  "and",  2) \
	_(OR,   "or",   2) \
	_(SHL,  "shl",  2) \
	_(SAR,  "sar",  2) \
	_(SLR,  "slr",  2) \
	\
	_(NEG,  "neg",  1) \
	_(NOT,  "not",  1) \
	\
	_(EQ,   "eq",   2) \
	_(NEQ,  "neq",  2) \
	_(ULT,  "ult",  2) \
	_(ULEQ, "uleq", 2) \
	_(UGT,  "ugt",  2) \
	_(UGEQ, "ugeq", 2) \
	_(SLT,  "slt",  2) \
	_(SLEQ, "sleq", 2) \
	_(SGT,  "sgt",  2) \
	_(SGEQ, "sgeq", 2) \
	\
	_(IDENTITY, "identity", 1) \
	_(LOAD, "load", 1) \
	_(STORE, "store", 2) \
	_(GET_INDEX_PTR, "get_index_ptr", 2) \
	_(GET_MEMBER_PTR, "get_member_ptr", 2) \
	_(CALL, "call", 0) \
	_(PHI, "phi", 0) \
	_(JUMP, "jump", 1) \
	_(BRANCH, "branch", 3) \
	_(RET, "ret", 1) \
	_(RETVOID, "retvoid", 0) \

typedef enum {
#define ENUM(kind, ...) VK_##kind,
VALUE_KINDS(ENUM)
#undef ENUM
} ValueKind;

extern char *value_kind_repr[];

extern u8 value_kind_param_cnt[];

typedef struct Value Value;

struct Value {
	ValueKind kind;
	u8 visited;
	u8 operand_cnt;
	Type *type;
	size_t index;
	Value *parent;
	Value *prev;
	Value *next;
};

typedef struct {
	Value base;
	i64 k;
} Constant;

typedef struct {
	Value base;
	Str str;
} StringLiteral;

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

extern Value NOP;

void value_init(Value *value, ValueKind kind, Type *type);

bool value_is_terminator(Value *value);

Value ** value_operands(Value *value);
size_t value_operand_cnt(Value *value);

#define FOR_EACH_OPERAND(value, op) \
	for (Value **op = value_operands(value), **last = op + value_operand_cnt(value); op != last; op++)

void print_operand(FILE *f, Value *operand);
void print_value(FILE *f, Value *v);

void prepend_value(Value *pos, Value *new);

void remove_value(Value *v);

void replace_value(Value *old, Value *new);

void change_to_identity(Operation *operation, Value *source);

Operation *create_operation(Arena *arena, ValueKind kind, Type *type, size_t operand_cnt);

Value *create_unary(Arena *arena, ValueKind kind, Type *type, Value *arg);

Operation *insert_phi(Arena *arena, Block *block, Type *type);


struct Block {
	Value base;
	MBlock *mblock;
	Block **preds_;
	size_t pred_cnt_;
	size_t pred_cap_;
	size_t filled_pred_cnt;
	size_t depth; // loop nesting depth (0 means outside of all loops)

	GArena incomplete_phis;
};

Block *create_block(Arena *arena, Function *function);

Block **block_preds(Block *block);
size_t block_pred_cnt(Block *block);

Block **block_succs(Block *block);
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
	MFunction *mfunction;

	GArena *uses; // array of Value * for each Value * (by its index)
};

Function *create_function(Arena *arena, Str name, Type *type);

bool function_is_fully_defined(Function *function);

void compute_postorder(Function *function);

void print_function(FILE *f, Function *function);

void validate_function(Function *function);

size_t number_values(Function *function, size_t start_index);



typedef struct {
	size_t function_cnt;
	Function **functions;
	size_t global_cnt;
	Global **globals;
	size_t string_cnt;
	StringLiteral **strings;
} Module;

void print_globals(FILE *f, Module *module);

Field *get_member(Value *value);


// IR passes (each in its own file)

// value_numbering.c
void value_numbering(Arena *arena, Function *function);
