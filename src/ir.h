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
	_(UNDEFINED, "undefined") \
	_(NOP,       "nop") \
	_(CONSTANT,  "constant") \
	_(STRING,    "string") \
	_(ALLOCA,    "alloca") \
	_(GLOBAL,    "global") \
	_(ARGUMENT,  "argument") \
	_(BLOCK,     "block") \
	_(FUNCTION,  "function") \
	\
	/* binary arithmetic */ \
	_(ADD,  "add") \
	_(SUB,  "sub") \
	_(MUL,  "mul") \
	_(UDIV, "udiv") \
	_(SDIV, "sdiv") \
	_(UREM, "urem") \
	_(SREM, "srem") \
	_(AND,  "and") \
	_(OR,   "or") \
	_(SHL,  "shl") \
	_(SAR,  "sar") \
	_(SLR,  "slr") \
	\
	/* unary arithmetic */ \
	_(NEG,  "neg") \
	_(NOT,  "not") \
	\
	/* comparisons */  \
	_(EQ,   "eq") \
	_(NEQ,  "neq") \
	_(ULT,  "ult") \
	_(ULEQ, "uleq") \
	_(UGT,  "ugt") \
	_(UGEQ, "ugeq") \
	_(SLT,  "slt") \
	_(SLEQ, "sleq") \
	_(SGT,  "sgt") \
	_(SGEQ, "sgeq") \
	\
	/* special values */ \
	_(IDENTITY, "identity") \
	_(LOAD, "load") \
	_(STORE, "store") \
	_(GET_INDEX_PTR, "get_index_ptr") \
	_(GET_MEMBER_PTR, "get_member_ptr") \
	_(CALL, "call") \
	_(PHI, "phi") \
	_(JUMP, "jump") \
	_(BRANCH, "branch") \
	_(RET, "ret") \

typedef enum {
#define ENUM(kind, ...) VK_##kind,
VALUE_KINDS(ENUM)
#undef ENUM
} ValueKind;

extern char *value_kind_repr[];

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

#define VK(v)      (((Value *) (v))->kind)
#define VINDEX(v)  (((Value *) (v))->index)
#define VTYPE(v)   (((Value *) (v))->type)
#define OPER(v, i) (((Operation *) (v))->operands[i])

#define STORE_ADDR(v)  OPER(v, 0)
#define STORE_VALUE(v) OPER(v, 1)

#define LOAD_ADDR(v) OPER(v, 0)

#define CALL_FUN(v)  OPER(v, 0)
#define CALL_ARGS(v) (&OPER(v, 1))

extern Value NOP;

void value_init(Value *value, ValueKind kind, Type *type);

bool value_is_terminator(Value *value);

Value **value_operands(Value *value);
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
	size_t depth; // loop nesting depth (0 means outside of all loops)
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

// merge_blocks.c
void merge_blocks(Arena *arena, Function *function);

// thread_jumps.c
void thread_jumps(Arena *arena, Function *function);

// split_critical_edges.c
void split_critical_edges(Arena *arena, Function *function);

// single_exit.c
void single_exit(Arena *arena, Function *function);

// deconstruct_ssa.c
void deconstruct_ssa(Arena *arena, Function *function);
