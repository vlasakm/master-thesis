#include <stdio.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdalign.h>
#include <string.h>
#include <setjmp.h>
#include <assert.h>
#include <errno.h>

#include "arena.h"

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef int8_t  i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;

#define garena_array(arena, type) \
	((type *) garena_mem((arena)))

#define garena_array_from(arena, start, type) \
	((type *) garena_from((arena), (start), alignof(type)))

#define container_of(member_ptr, type, member) \
	((type *) ((u8 *)(member_ptr) - offsetof(type, member)))

#define UNREACHABLE() unreachable(__FILE__, __LINE__)
_Noreturn void
unreachable(char *file, size_t line)
{
	fprintf(stderr, "ERROR: unreachable code reached at %s:%zu\n", file, line);
	exit(EXIT_FAILURE);
}

typedef struct {
	const u8 *str;
	size_t len;
} Str;
#define STR(lit) (Str) { .str = (const u8 *) lit, .len = sizeof(lit) - 1 }

bool str_eq(Str a, Str b)
{
	return a.len == b.len && memcmp(a.str, b.str, a.len) == 0;
}

int str_cmp(Str a, Str b)
{
	int cmp = memcmp(a.str, b.str, a.len < b.len ? a.len : b.len);
	return cmp == 0 ? (a.len > b.len) - (b.len > a.len) : cmp;
}

Str
arena_vaprintf(Arena *arena, const char *fmt, va_list ap)
{
	va_list ap_orig;
	// save original va_list (vprintf changes it)
	va_copy(ap_orig, ap);

	size_t available = arena->current->size - arena->current->pos;
	void *mem = ((u8 *) arena->current) + arena->current->pos;
	int len = vsnprintf(mem, available, fmt, ap);
	assert(len >= 0);
	len += 1; // terminating null
	if ((size_t) len <= available) {
		arena->current->pos += (size_t) len;
	} else {
		mem = arena_alloc(arena, (size_t) len);
		vsnprintf(mem, (size_t) len, fmt, ap_orig);
	}
	va_end(ap_orig);
	return (Str) { .str = mem, .len = len - 1 };
}

Str
arena_aprintf(Arena *arena, const char *fmt, ...)
{
	va_list ap;
	va_start(ap, fmt);
	Str str = arena_vaprintf(arena, fmt, ap);
	va_end(ap);
	return str;
}

/*

typedef struct Value Value;

struct Value {
	enum {
		VK_LOADIMM,
		VK_ADD,
		VK_SUB,
		VK_MUL,
		VK_STORE,
		VK_LOAD,
	} kind;
	union {
		int64_t imm;
		struct { Value *arg; };
		struct { Value *left; Value *right; };
	};
};

typedef enum {
	RAX,
	RBX,
	RCX,
} Reg;

typedef int Imm;

typedef struct {
	enum {
		AK_REG,
		AK_IMM,
		AK_INDIR,
	};

} Arg;

typedef struct {
	enum {
		IK_STORE,
		IK_LOAD,
		IK_ADD,
		IK_SUB,
		IK_MUL,
	} kind;
	Arg args[2];
	//union {
	//	struct { Reg dest; Reg src; };
	//}
} Inst;
*/

typedef enum {
	TY_VOID,
	TY_INT,
	TY_POINTER,
	TY_FUNCTION,
} TypeKind;

typedef struct {
	TypeKind kind;
} Type;

typedef struct {
	Type base;
	Type *ret_type;
	size_t param_cnt;
	Type **param_types;
} FunctionType;

typedef struct {
	Type base;
	Type *child;
} PointerType;

Type TYPE_VOID = { .kind = TY_VOID };
Type TYPE_INT = { .kind = TY_INT };

static Type *
type_pointer(Arena *arena, Type *child)
{
	PointerType *ptr_type = arena_alloc(arena, sizeof(*ptr_type));
	ptr_type->base.kind = TY_POINTER;
	ptr_type->child = child;
	return &ptr_type->base;
}

static Type *
type_function(Arena *arena, Type *ret_type, Type **param_types, size_t param_cnt)
{
	FunctionType *fun_type = arena_alloc(arena, sizeof(*fun_type));
	fun_type->base.kind = TY_FUNCTION;
	fun_type->ret_type = ret_type;
	fun_type->param_types = param_types;
	fun_type->param_cnt = param_cnt;
	return &fun_type->base;
}


static size_t
type_size(Type *type)
{
	switch (type->kind) {
	case TY_VOID: return 0;
	case TY_INT:  return 8;
	case TY_POINTER:
	case TY_FUNCTION:
		return 8;
	}
	UNREACHABLE();
}

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

typedef enum {
	R_RAX,
	R_RBX,
	R_RCX,
	R_RBP,
	R_CL,
} Reg;

const char *reg_repr[] = {
	"rax",
	"rbx",
	"rcx",
	"rbp",
	"cl",
};

typedef struct {
	enum {
		OK_NONE,
		OK_REG,
		OK_VREG,
		OK_INDIR_REG,
		OK_INDIR_VREG,
		OK_LABEL,
		OK_CONST,
	} kind;
	union {
		Reg reg;
		Value *vreg;
		Str label;
		i64 constant;
	};
} Operand;

typedef struct Instruction Instruction;
struct Instruction {
	InstKind kind;
	Instruction *prev;
	Instruction *next;
	Operand op[3];
};


// A simple hash table.
// Inspired by: http://www.craftinginterpreters.com/hash-tables.html


// FNV-1a hash
// http://www.isthe.com/chongo/tech/comp/fnv/
u64
str_hash(Str id)
{
    u64 h = UINT64_C(14695981039346656037);
    for (size_t i = 0; i < id.len; i++) {
	// beware of unwanted sign extension!
        h ^= id.str[i];
        h *= UINT64_C(1099511628211);
    }
    return h;
}

typedef struct {
	Str key;
	Value *value;
} Entry;

typedef struct {
	Entry *entries;
	size_t entry_cnt;
	size_t capacity;
} Table;

void
table_init(Table *table, size_t capacity)
{
	table->entry_cnt = 0;
	if (capacity == 0) {
		table->capacity = 0;
		table->entries = NULL;
	} else {
		table->capacity = 1;
		while (table->capacity < capacity) {
			table->capacity *= 2;
		}
		table->entries = calloc(table->capacity, sizeof(*table->entries));
	}
}

void
table_destroy(Table *table)
{
	free(table->entries);
}

Entry *
table_find_entry(Entry *entries, size_t capacity, Str key)
{
	u64 hash = str_hash(key);
	// NOTE: We guarantee that the capacity is a power of two. The modulo
	// operation thus simplifies to simple binary AND.
	size_t mask = capacity - 1;
	for (size_t index = hash & mask;; index = (index + 1) & mask) {
		Entry *entry = &entries[index];
		if (entry->key.str == NULL || str_eq(entry->key, key)) {
			return entry;
		}
	}
}

void
table_grow(Table *table)
{
	size_t capacity = table->capacity ? table->capacity * 2 : 8;
	// TODO: intialize memory if not zero allocated
	Entry *entries = calloc(capacity, sizeof(*entries));
	for (size_t i = 0; i < table->capacity; i++) {
		Entry *old = &table->entries[i];
		if (old->key.str == NULL) {
			continue;
		}
		Entry *new = table_find_entry(entries, capacity, old->key);
		*new = *old;
	}
	free(table->entries);
	table->entries = entries;
	table->capacity = capacity;
}

Value **
table_get(Table *table, Str key)
{
	if (table->entry_cnt == 0) {
		return NULL;
	}
	Entry *entry = table_find_entry(table->entries, table->capacity, key);
	if (entry->key.str == NULL) {
		return NULL;
	}
	return &entry->value;
}

bool
table_insert(Table *table, Str key, Value *value)
{
	if (table->entry_cnt + 1 >= table->capacity / 2) {
		table_grow(table);
	}
	Entry *entry = table_find_entry(table->entries, table->capacity, key);
	bool new = entry->key.str == NULL;
	if (new) {
		table->entry_cnt += 1;
		entry->key = key;
	}
	entry->value = value;
	return new;
}

typedef struct Environment Environment;
struct Environment {
	Environment *prev;
	Table env;
};

void
env_push(Environment **prev)
{
	Environment *env = calloc(sizeof(*env), 1);
	table_init(&env->env, 0);
	env->prev = *prev;
	*prev = env;
}

void
env_pop(Environment **env)
{
	Environment *old = *env;
	(*env) = (*env)->prev;
	table_destroy(&old->env);
	free(old);
}

void
env_define(Environment *env, Str name, Value *value)
{
	table_insert(&env->env, name, value);
}

Value **
env_lookup(Environment *env, Str name)
{
	if (!env) {
		return NULL;
	}
	Value **lvalue = table_get(&env->env, name);
	if (lvalue) {
		return lvalue;
	}
	return env_lookup(env->prev, name);
}


#include "lexer.c"

typedef struct {
	bool lvalue;
	Value *value;
} CValue;

Value NOP = { .kind = VK_NOP };

static CValue
rvalue(Value *value)
{
	return (CValue) { .lvalue = false, .value = value };
}

static CValue
lvalue(Value *value)
{
	return (CValue) { .lvalue = true, .value = value };
}

typedef struct {
	Arena *arena;
	GArena *scratch;
	void *user_data;
	void (*error_callback)(void *user_data, const u8 *err_pos, const char *msg, va_list ap);
	Lexer lexer;
	Token lookahead;
	Token prev;
	bool had_error;
	bool panic_mode;
	Environment *env;
	Value **prev_pos;
	Function *current_function;
	GArena functions;
	Block *current_block;
	Block *continue_block;
	Block *break_block;
} Parser;

static void
parser_error(Parser *parser, Token errtok, bool panic, const char *msg, ...)
{
	va_list ap;
	va_start(ap, msg);
	if (!parser->panic_mode) {
		parser->error_callback(parser->user_data, errtok.str.str, msg, ap);
		parser->had_error = true;
		parser->panic_mode = panic;
	}
	va_end(ap);
}

static TokenKind
peek(const Parser *parser)
{
	return parser->lookahead.kind;
}

static Token
prev_tok(Parser *parser)
{
	return parser->prev;
}

static Token
discard(Parser *parser)
{
	parser->prev = parser->lookahead;
	lex_next(&parser->lexer, &parser->lookahead);
	if (parser->lookahead.kind == TK_ERROR) {
		parser_error(parser, parser->lookahead, true, "Unexpected character");
	}
	return parser->prev;
}

static void
eat(Parser *parser, TokenKind kind)
{
	TokenKind tok = peek(parser);
	if (tok != kind) {
		parser_error(parser, parser->lookahead, true, "Expected %s, found %s", tok_repr[kind], tok_repr[tok]);
		return;
	}
	discard(parser);
}

static bool
try_eat(Parser *parser, TokenKind kind)
{
	if (peek(parser) == kind) {
		discard(parser);
		return true;
	}
	return false;
}

static Str
eat_identifier(Parser *parser)
{
	eat(parser, TK_IDENTIFIER);
	return prev_tok(parser).str;
}

static Block *
add_block(Parser *parser)
{
	Block *block = arena_alloc(parser->arena, sizeof(*block));
	value_init(&block->base, VK_BLOCK, type_pointer(parser->arena, &TYPE_VOID), &parser->current_function->base);
	parser->current_function->block_cnt += 1;
	return block;
}

static void
add_to_block(Parser *parser, Value *value)
{
	if (!parser->current_block) {
		return;
	}
	if (parser->prev_pos != &parser->current_block->head) {
		value->prev = container_of(parser->prev_pos, Value, next);
	} else {
		value->prev = NULL;
	}
	*parser->prev_pos = value;
	value->next = NULL;
	parser->prev_pos = &value->next;
	parser->current_block->tail = value;
}

static Operation *
add_operation(Parser *parser, ValueKind kind, size_t operand_cnt)
{
	Operation *op = arena_alloc(parser->arena, sizeof(*op) + sizeof(op->operands[0]) * operand_cnt);
	value_init(&op->base, kind, &TYPE_INT, &parser->current_block->base);
	add_to_block(parser, &op->base);
	op->base.kind = kind;
	op->base.type = &TYPE_INT;
	return op;
}

static Value *
add_unary(Parser *parser, ValueKind kind, Value *arg)
{
	Operation *op = add_operation(parser, kind, 1);
	op->operands[0] = arg;
	return &op->base;
}

static Value *
add_binary(Parser *parser, ValueKind kind, Value *left, Value *right)
{
	Operation *op = add_operation(parser, kind, 2);
	op->operands[0] = left;
	op->operands[1] = right;
	return &op->base;
}

static void
switch_to_block(Parser *parser, Block *new_block)
{
	parser->current_block = new_block;
	parser->prev_pos = &new_block->head;
}

static void
add_jump(Parser *parser, Block *destination, Block *new_block)
{
	add_unary(parser, VK_JUMP, &destination->base);
	switch_to_block(parser, new_block);
}

static void
add_cond_jump(Parser *parser, Value *cond, Block *true_block, Block *false_block, Block *new_block)
{
	Operation *op = add_operation(parser, VK_BRANCH, 3);
	op->operands[0] = cond;
	op->operands[1] = &true_block->base;
	op->operands[2] = &false_block->base;
	switch_to_block(parser, new_block);
}

static Value *
add_alloca(Parser *parser, Type *type)
{
	Alloca *alloca = arena_alloc(parser->arena, sizeof(*alloca));
	value_init(&alloca->base, VK_ALLOCA, type_pointer(parser->arena, type), &parser->current_block->base);
	add_to_block(parser, &alloca->base);
	alloca->size = type_size(type);
	return &alloca->base;
}

static Value *
add_argument(Parser *parser, Type *type, size_t index)
{
	Argument *arg = arena_alloc(parser->arena, sizeof(*arg));
	value_init(&arg->base, VK_ARGUMENT, type, &parser->current_block->base);
	add_to_block(parser, &arg->base);
	arg->index = index;
	return &arg->base;
}

static Value *
as_rvalue(Parser *parser, CValue cvalue)
{
	if (cvalue.lvalue) {
		return add_unary(parser, VK_LOAD, cvalue.value);
	} else {
		return cvalue.value;
	}
}

static Value *
as_lvalue(Parser *parser, CValue cvalue, char *msg)
{
	if (cvalue.lvalue) {
		return cvalue.value;
	} else {
		parser_error(parser, parser->lookahead, false, msg);
		return &NOP;
	}
}


static Type *
parse_type(Parser *parser, bool allow_void)
{
	Type *type;
	Token token = discard(parser);
	switch (token.kind) {
	case TK_VOID: type = &TYPE_VOID; break;
	case TK_INT:  type = &TYPE_INT;  break;
	case TK_IDENTIFIER:  assert(false);
	default: return NULL;
	}

	while (try_eat(parser, TK_ASTERISK)) {
		type = type_pointer(parser->arena, type);
	}

	if (!allow_void && type == &TYPE_VOID) {
		return NULL;
	}

	return type;
}

static CValue expression_bp(Parser *parser, int bp);

static CValue
expression(Parser *parser)
{
	return expression_bp(parser, 1);
}

static CValue
expression_no_comma(Parser *parser)
{
	return expression_bp(parser, 2);
}

static CValue
expression_no_equal(Parser *parser)
{
	return expression_bp(parser, 3);
}

static Value *
create_const(Parser *parser, i64 value)
{
	Constant *k = arena_alloc(parser->arena, sizeof(*k));
	value_init(&k->base, VK_CONSTANT, &TYPE_INT, &parser->current_block->base);
	k->k = value;
	return &k->base;
}

static CValue
nullerr(Parser *parser)
{
	TokenKind tok = peek(parser);
	parser_error(parser, parser->lookahead, true, "Invalid start of expression %s", tok_repr[tok]);
	return rvalue(&NOP);
}

static CValue
literal(Parser *parser)
{
	Token token = discard(parser);
	switch (token.kind) {
	case TK_NUMBER: {
		const u8 *pos = token.str.str;
		const u8 *end = pos + token.str.len;
		bool negative = 0;
		while (*pos == '-') {
			negative = !negative;
			pos += 1;
		}
		i64 value = 0;
		for (; pos < end; pos++) {
			value = value * 10 + (*pos - '0');
		}
		value = (i32) (negative ? -value : value);
		return rvalue(create_const(parser, value));
	}
	default: assert(false);
	}
}

static CValue
ident(Parser *parser)
{
	eat(parser, TK_IDENTIFIER);
	Str ident = prev_tok(parser).str;
	Value **value = env_lookup(parser->env, ident);
	assert(value);
	if ((*value)->kind == VK_FUNCTION) {
	     return rvalue(*value);
	}
	return lvalue(*value);
}

static CValue
paren(Parser *parser)
{
	eat(parser, TK_LPAREN);
	CValue value = expression(parser);
	eat(parser, TK_RPAREN);
	return value;
}

static CValue
cast(Parser *parser)
{
	UNREACHABLE();
}

static CValue
pre(Parser *parser)
{
	UNREACHABLE();
}

static CValue
empty(Parser *parser)
{
	return rvalue(&NOP);
}

static CValue
unop(Parser *parser)
{
	Token token = discard(parser);
	CValue carg = expression_bp(parser, 14);
	Value *arg = as_rvalue(parser, carg);

	Value *result;
	switch (token.kind) {
	case TK_PLUS:
		result = arg;
		break;
	case TK_MINUS:
		result = add_unary(parser, VK_NEG, arg);
		break;
	default:
		UNREACHABLE();
	}
	return rvalue(result);
}

static CValue
deref(Parser *parser)
{
	eat(parser, TK_ASTERISK);
	CValue carg = expression_bp(parser, 14);
	Value *arg = as_rvalue(parser, carg);
	return lvalue(arg);
}

static CValue
addr(Parser *parser)
{
	eat(parser, TK_AMP);
	CValue carg = expression_bp(parser, 14);
	Value *arg = as_lvalue(parser, carg, "Cannot take address of non-lvalue");
	return rvalue(arg);
}

static CValue
lognot(Parser *parser)
{
	eat(parser, TK_BANG);
	CValue carg = expression_bp(parser, 14);
	Value *arg = as_rvalue(parser, carg);
	Value *zero = create_const(parser, 0);
	return rvalue(add_binary(parser, VK_NEQ, arg, zero));
}

static CValue
bitnot(Parser *parser)
{
	eat(parser, TK_TILDE);
	CValue carg = expression_bp(parser, 14);
	Value *arg = as_rvalue(parser, carg);
	return rvalue(add_unary(parser, VK_NOT, arg));
}

static CValue
cmp(Parser *parser, CValue cleft, int rbp)
{
	TokenKind tok = discard(parser).kind;
	CValue cright = expression_bp(parser, rbp);
	Value *left = as_rvalue(parser, cleft);
	Value *right = as_rvalue(parser, cright);
	ValueKind kind;
	switch (tok) {
	case TK_EQUAL_EQUAL:   kind = VK_EQ;  break;
	case TK_BANG_EQUAL:    kind = VK_NEQ; break;
	case TK_LESS:          kind = VK_LT;  break;
	case TK_LESS_EQUAL:    kind = VK_LEQ; break;
	case TK_GREATER:       kind = VK_GT;  break;
	case TK_GREATER_EQUAL: kind = VK_GEQ; break;
	default: UNREACHABLE();
	}
	return rvalue(add_binary(parser, kind, left, right));
}

static CValue
binop(Parser *parser, CValue cleft, int rbp)
{
	TokenKind tok = discard(parser).kind;
	CValue cright = expression_bp(parser, rbp);
	Value *left = as_rvalue(parser, cleft);
	Value *right = as_rvalue(parser, cright);
	ValueKind kind;
	switch (tok) {
	case TK_PLUS:     kind = VK_ADD; break;
	case TK_MINUS:    kind = VK_SUB; break;
	case TK_ASTERISK: kind = VK_MUL; break;
	case TK_SLASH:    kind = VK_DIV; break;
	case TK_PERCENT:  kind = VK_MOD; break;
	default: UNREACHABLE();
	}
	return rvalue(add_binary(parser, kind, left, right));
}

static CValue
bitbinop(Parser *parser, CValue cleft, int rbp)
{
	TokenKind tok = discard(parser).kind;
	CValue cright = expression_bp(parser, rbp);
	Value *left = as_rvalue(parser, cleft);
	Value *right = as_rvalue(parser, cright);
	ValueKind kind;
	switch (tok) {
	case TK_AMP:             kind = VK_AND; break;
	case TK_BAR:             kind = VK_OR;  break;
	case TK_LESS_LESS:       kind = VK_SHL; break;
	case TK_GREATER_GREATER: kind = VK_SHR; break;
	default: UNREACHABLE();
	}
	return rvalue(add_binary(parser, kind, left, right));
}

static CValue
indexing(Parser *parser, CValue cleft, int rbp)
{
	(void) rbp;
	eat(parser, TK_LBRACKET);
	CValue cright = expression(parser);
	eat(parser, TK_RBRACKET);
	Value *left = as_rvalue(parser, cleft);
	Value *right = as_rvalue(parser, cright);
	return rvalue(add_binary(parser, VK_GET_INDEX_PTR, left, right));
}

static CValue
call(Parser *parser, CValue cleft, int rbp)
{
	(void) rbp;
	eat(parser, TK_LPAREN);
	Value *left = as_rvalue(parser, cleft);
	if (left->type->kind != TY_FUNCTION) {
		parser_error(parser, parser->lookahead, false, "Expected function call target to have function type");
	}
	FunctionType *fun_type = (void*) left->type;
	size_t argument_cnt = fun_type->param_cnt;
	Operation *call = add_operation(parser, VK_CALL, 1 + argument_cnt);

	size_t i = 0;
	call->operands[i++] = left;
	while (!try_eat(parser, TK_RPAREN)) {
		CValue carg = expression_no_comma(parser);
		if (i < argument_cnt) {
			call->operands[i] = as_rvalue(parser, carg);
			if (call->operands[i]->type != fun_type->param_types[i]) {
				parser_error(parser, parser->lookahead, false, "Argument type doesn't equal parameter type");
			}
		}
		i += 1;
		if (!try_eat(parser, TK_COMMA)) {
			eat(parser, TK_RPAREN);
			break;
		}
	}
	if (i - 1 != argument_cnt) {
		parser_error(parser, parser->lookahead, false, "Invalid number of arguments: expected %zu, got %zu", argument_cnt, i);
	}
	return rvalue(&call->base);
}

static CValue
member(Parser *parser, CValue cleft, int rbp)
{
	UNREACHABLE();
}

static CValue
shortcirc(Parser *parser, CValue cleft, int rbp)
{
	UNREACHABLE();
}

static CValue
post(Parser *parser, CValue cleft, int rbp)
{
	UNREACHABLE();
}

static CValue
seq(Parser *parser, CValue cleft, int rbp)
{
	eat(parser, TK_COMMA);
	CValue cright = expression_bp(parser, rbp);
	as_rvalue(parser, cleft);
	return rvalue(as_rvalue(parser, cright));
}

static CValue
assign(Parser *parser, CValue cleft, int rbp)
{
	eat(parser, TK_EQUAL);
	CValue cright = expression_bp(parser, rbp);
	Value *left = as_lvalue(parser, cleft, "Expected lvalue on left hand side of assignment");
	Value *right = as_rvalue(parser, cright);
	add_binary(parser, VK_STORE, left, right);
	return lvalue(left);
}

static void
struct_declaration(Parser *parser)
{
	UNREACHABLE();
}

static void
typedef_declaration(Parser *parser)
{
	UNREACHABLE();
}

static Value *
condition(Parser *parser)
{
	CValue ccond = expression(parser);
	Value *cond = as_rvalue(parser, ccond);
	Value *zero = create_const(parser, 0);
	return add_binary(parser, VK_NEQ, cond, zero);
}

static void statement(Parser *parser);
static void expression_or_variable_declaration(Parser *parser);

static void
statements(Parser *parser)
{
	while (!try_eat(parser, TK_RBRACE)) {
		statement(parser);
	}
}


static void
loop_body(Parser *parser, Block *continue_block, Block *break_block)
{
	Block *saved_break_block = parser->break_block;
	Block *saved_continue_block = parser->continue_block;
	parser->break_block = break_block;
	parser->continue_block = continue_block;
	statement(parser);
	parser->break_block = saved_break_block;
	parser->continue_block = saved_continue_block;
}

static void
statement(Parser *parser)
{
	switch (peek(parser)) {
	case TK_LBRACE:
		eat(parser, TK_LBRACE);
		env_push(&parser->env);
		statements(parser);
		env_pop(&parser->env);
		break;
	case TK_IF: {
		eat(parser, TK_IF);
		Block *cond_block = add_block(parser);
		Block *true_block = add_block(parser);
		Block *false_block = add_block(parser);
		Block *after_block = add_block(parser);

		add_jump(parser, cond_block, cond_block);

		eat(parser, TK_LPAREN);
		Value *cond = condition(parser);
		eat(parser, TK_RPAREN);

		add_cond_jump(parser, cond, true_block, false_block, true_block);

		statement(parser);
		add_jump(parser, after_block, false_block);

		if (try_eat(parser, TK_ELSE)) {
			statement(parser);
		}
		add_jump(parser, after_block, after_block);

		break;
	}
	case TK_SWITCH:
		UNREACHABLE();
		break;
	case TK_WHILE: {
		eat(parser, TK_WHILE);
		Block *cond_block = add_block(parser);
		Block *body_block = add_block(parser);
		Block *after_block = add_block(parser);

		add_jump(parser, cond_block, cond_block);

		eat(parser, TK_LPAREN);
		Value *cond = condition(parser);
		eat(parser, TK_RPAREN);

		add_cond_jump(parser, cond, body_block, after_block, body_block);

		loop_body(parser, cond_block, after_block);

		add_jump(parser, cond_block, after_block);
		break;
	}
	case TK_DO: {
		eat(parser, TK_DO);
		Block *body_block = add_block(parser);
		Block *cond_block = add_block(parser);
		Block *after_block = add_block(parser);

		add_jump(parser, body_block, body_block);

		loop_body(parser, cond_block, after_block);

		add_jump(parser, cond_block, cond_block);

		eat(parser, TK_WHILE);
		eat(parser, TK_LPAREN);
		Value *cond = condition(parser);
		eat(parser, TK_RPAREN);
		eat(parser, TK_SEMICOLON);

		add_cond_jump(parser, cond, body_block, after_block, after_block);
		break;
	}
	case TK_FOR: {
		eat(parser, TK_FOR);
		Block *init_block = add_block(parser);
		Block *cond_block = add_block(parser);
		Block *body_block = add_block(parser);
		Block *incr_block = add_block(parser);
		Block *after_block = add_block(parser);

		add_jump(parser, init_block, init_block);

		if (peek(parser) != TK_SEMICOLON) {
			expression_or_variable_declaration(parser);
		}
		eat(parser, TK_SEMICOLON);

		add_jump(parser, cond_block, cond_block);

		if (peek(parser) != TK_SEMICOLON) {
			Value *cond = condition(parser);
			add_cond_jump(parser, cond, body_block, after_block, incr_block);
		} else {
			add_jump(parser, body_block, incr_block);
		}
		eat(parser, TK_SEMICOLON);

		if (peek(parser) != TK_RPAREN) {
			expression(parser);
		}
		eat(parser, TK_RPAREN);

		add_jump(parser, cond_block, body_block);

		loop_body(parser, incr_block, after_block);

		add_jump(parser, incr_block, after_block);
		break;
	}
	case TK_BREAK: {
		Token tok = discard(parser);
		if (parser->break_block) {
			add_jump(parser, parser->break_block, NULL);
		} else {
			parser_error(parser, tok, true, "'break' outside of loop or switch");
		}
		eat(parser, TK_SEMICOLON);
		break;
	}
	case TK_CONTINUE: {
		Token tok = discard(parser);
		if (parser->continue_block) {
			add_jump(parser, parser->continue_block, NULL);
		} else {
			parser_error(parser, tok, true, "'continue' outside of loop");
		}
		eat(parser, TK_SEMICOLON);
		break;
	}
	case TK_RETURN: {
		Token tok = discard(parser);
		Type *return_type = ((FunctionType *) parser->current_function->base.type)->ret_type;
		if (peek(parser) != TK_SEMICOLON) {
			Value *value = as_rvalue(parser, expression(parser));
			if (value->type != return_type) {
				parser_error(parser, tok, false, "Type of 'return'ed value does not match nominal type");
			}
			add_unary(parser, VK_RET, value);
		} else if (return_type == &TYPE_VOID) {
			add_operation(parser, VK_RETVOID, 0);
		} else {
			parser_error(parser, tok, false, "Expected some value to be 'return'ed");
		}
		eat(parser, TK_SEMICOLON);
		break;
	}
	default:
		expression_or_variable_declaration(parser);
		eat(parser, TK_SEMICOLON);
		break;
	}
}

static void
function_declaration(Parser *parser)
{
	Type *ret_type = parse_type(parser, true);
	Str function_name = eat_identifier(parser);
	eat(parser, TK_LPAREN);
	typedef struct {
		Type *type;
		Str name;
	} TypedName;
	size_t start = garena_save(parser->scratch);
	while (!try_eat(parser, TK_RPAREN)) {
		Type *param_type = parse_type(parser, false);
		Str param_name = eat_identifier(parser);
		garena_push_value(parser->scratch, TypedName, ((TypedName) { .type = param_type, .name = param_name }));
		if (!try_eat(parser, TK_COMMA)) {
			eat(parser, TK_RPAREN);
			break;
		}
	}
	size_t param_cnt = garena_cnt_from(parser->scratch, start, TypedName);
	TypedName *params = garena_array_from(parser->scratch, start, TypedName);
	Type **param_types = arena_alloc(parser->arena, param_cnt * sizeof(*param_types));
	Type *fun_type = type_function(parser->arena, ret_type, param_types, param_cnt);
	Function *function = arena_alloc(parser->arena, sizeof(*function));
	function->name = function_name;
	value_init(&function->base, VK_FUNCTION, fun_type, NULL);
	env_define(parser->env, function_name, &function->base);
	eat(parser, TK_LBRACE);
	parser->current_function = function;
	function->block_cnt = 0;
	function->entry = add_block(parser);
	switch_to_block(parser, function->entry);
	env_push(&parser->env);
	for (size_t i = 0; i < param_cnt; i++) {
		param_types[i] = params[i].type;
		Value *arg = add_argument(parser, param_types[i], i);
		Value *addr = add_alloca(parser, param_types[i]);
		add_binary(parser, VK_STORE, addr, arg);
		env_define(parser->env, params[i].name, arg);
	}
	statements(parser);
	garena_restore(parser->scratch, start);
	garena_push_value(&parser->functions, Function *, function);
	env_pop(&parser->env);
}

static void
external_declaration(Parser *parser)
{
	switch (peek(parser)) {
	case TK_STRUCT:
		return struct_declaration(parser);
	case TK_TYPEDEF:
		return typedef_declaration(parser);
	default:
		return function_declaration(parser);
	}
}

static void
variable_declaration(Parser *parser)
{
	Type *type = parse_type(parser, false);
	eat(parser, TK_IDENTIFIER);
	Str name = prev_tok(parser).str;
	Value *addr = add_alloca(parser, type);
	assign(parser, lvalue(addr), 2);
	//eat(parser, TK_SEMICOLON);
	env_define(parser->env, name, addr);
}

static void
variable_declarations(Parser *parser)
{
	for (;;) {
		variable_declaration(parser);
		if (!try_eat(parser, TK_COMMA)) {
			break;
		}
	}
}

static void
expression_or_variable_declaration(Parser *parser)
{
	switch (peek(parser)) {
	case TK_INT:
		variable_declarations(parser);
		break;
	default:
		expression(parser);
	}
}

static void
parse_program(Parser *parser)
{
	while (peek(parser) != TK_EOF) {
		function_declaration(parser);
		//external_declaration(parser);
		//switch (peek(parser)) {
		//case TK_INT:
		//	variable_declarations(parser);
		//	break;
		//default:
		//	expression(parser);
		//	eat(parser, TK_SEMICOLON);
		//}
	}
}

static CValue
stop(Parser *parser, CValue left, int rbp)
{
	(void) parser;
	(void) left;
	(void) rbp;
	UNREACHABLE();
}

static CValue
lefterr(Parser *parser, CValue left, int rbp)
{
	(void) left;
	(void) rbp;
	TokenKind tok = peek(parser);
	parser_error(parser, parser->lookahead, true, "Invalid expression continuing/ending token %s", tok_repr[tok]);
	// Set the current token to something with low binding power to not get
	// into infinite loop of `lefterr`s on the same token.
	parser->lookahead.kind = TK_EOF;
	return rvalue(&NOP);
}

typedef struct {
	CValue (*nud)(Parser *);
	int rbp;
} NullInfo;

static NullInfo null_info[] = {
	#define TOK_NULL(tok, str, nud, rbp, ...) { nud, rbp },
	TOKENS(TOK_NULL, TOK_NULL, TOK_NULL)
	#undef TOK_STR
};

static bool
at_synchronization_point(Parser *parser)
{
	if (parser->prev.kind == TK_EOF) {
		// nothing to synchronize
		return true;
	}
	if (parser->prev.kind == TK_SEMICOLON && null_info[parser->lookahead.kind].nud != nullerr) {
		// an expression separator and a token that starts an expression
		return true;
	}
	return false;
}

typedef struct {
	CValue (*led)(Parser *, CValue left, int rbp);
	int lbp;
	int rbp;
} LeftInfo;

static LeftInfo left_info[] = {
	#define TOK_LEFT(tok, str, nud, nrbp, led, lbp, assoc) { led, lbp, lbp + (ASSOC_##assoc == ASSOC_LEFT) },
	TOKENS(TOK_LEFT, TOK_LEFT, TOK_LEFT)
	#undef TOK_STR
};

static CValue
expression_bp(Parser *parser, int bp)
{
	NullInfo ni = null_info[peek(parser)];
	CValue left = ni.nud(parser);

	for (;;) {
		LeftInfo li = left_info[peek(parser)];
		if (li.lbp < bp) {
			break;
		}
		left = li.led(parser, left, li.rbp);
	}

	return left;
}

size_t
instruction_arg_cnt(Value *value)
{
	switch (value->kind) {
	case VK_CALL: {
		Operation *op = (void *) value;
		return 1 + ((FunctionType *) op->operands[0]->type)->param_cnt;
	}
	default:
		return value_kind_param_cnt[value->kind];
	}
	UNREACHABLE();
}

void
for_each_operand(Value *value, void (*fun)(void *user_data, Value *operand), void *user_data)
{
	size_t operand_cnt = instruction_arg_cnt(value);
	if (operand_cnt == 0) {
	     return;
	}
	Operation *op = (void *) value;
	for (size_t i = 0; i < operand_cnt; i++) {
		fun(user_data, op->operands[i]);
	}
}

void
print_index(void *user_data, Value *operand)
{
	bool *first = user_data;
	if (!*first) {
		printf(", ");
	}
	*first = false;
	switch (operand->kind) {
	case VK_BLOCK:
		printf("block");
		printf("%zu", operand->index);
		break;
	case VK_FUNCTION:
		printf("function");
		printf("%zu", operand->index);
		break;
	case VK_CONSTANT: {
		Constant *k = (void*) operand;
		printf("%"PRIi64, k->k);
		break;
	}
	default:
		printf("v");
		printf("%zu", operand->index);
		break;
	}
}

static void
dfs(Block *block, size_t *index, Block **post_order)
{
	if (block->base.visited > 0) {
		return;
	}
	block->base.visited = 1;
	switch (block->tail->kind) {
	case VK_JUMP: {
		Operation *op = (void *) block->tail;
		assert(op->operands[0]->kind == VK_BLOCK);
		dfs((Block *) op->operands[0], index, post_order);
		break;
	}
	case VK_BRANCH: {
		Operation *op = (void *) block->tail;
		assert(op->operands[1]->kind == VK_BLOCK);
		assert(op->operands[2]->kind == VK_BLOCK);
		dfs((Block *) op->operands[1], index, post_order);
		dfs((Block *) op->operands[2], index, post_order);
		break;
	}
	case VK_RET:
	case VK_RETVOID:
		break;
	default:
	     break;
	     UNREACHABLE();
	}
	block->base.visited = 2;
	block->base.index = (*index)++;
	post_order[block->base.index] = block;
}

typedef struct {
	GArena insts;
} TranslationState;

static Operand
op_vreg(Value *v)
{
	return (Operand) { .kind = OK_VREG, .vreg = v };
}

static Operand
op_ivreg(Value *v)
{
	return (Operand) { .kind = OK_INDIR_VREG, .vreg = v };
}

static Operand
op_const(i64 c)
{
	return (Operand) { .kind = OK_CONST, .constant = c };
}

static Operand
op_label(Str label)
{
	return (Operand) { .kind = OK_LABEL, .label = label };
}

static Operand
op_reg(Reg r)
{
	return (Operand) { .kind = OK_REG, .reg = r };
}

static Operand
op_none(void)
{
	return (Operand) { .kind = OK_NONE };
}

static void
add_inst3(TranslationState *ts, InstKind kind, Operand op1, Operand op2, Operand op3)
{
	Instruction *ins = garena_push(&ts->insts, Instruction);
	ins->kind = kind;
	ins->op[0] = op1;
	ins->op[1] = op2;
	ins->op[2] = op3;
}

static void
add_inst0(TranslationState *ts, InstKind kind)
{
	add_inst3(ts, kind, op_none(), op_none(), op_none());
}

static void
add_inst1(TranslationState *ts, InstKind kind, Operand op1)
{
	add_inst3(ts, kind, op1, op_none(), op_none());
}

static void
add_inst2(TranslationState *ts, InstKind kind, Operand op1, Operand op2)
{
	add_inst3(ts, kind, op1, op2, op_none());
}

static void
add_mov_const(TranslationState *ts, Value *target, i64 k)
{
	add_inst2(ts, IK_MOV, op_vreg(target), op_const(k));
}

static void
add_copy(TranslationState *ts, Value *target, Value *source)
{
	add_inst2(ts, IK_MOV, op_vreg(target), op_vreg(source));
}

static void
add_load(TranslationState *ts, Value *target, Value *source)
{
	add_inst2(ts, IK_MOV, op_vreg(target), op_ivreg(source));
}

static void
add_store(TranslationState *ts, Value *target, Value *source)
{
	add_inst2(ts, IK_MOV, op_ivreg(target), op_vreg(source));
}

static void
add_binop(TranslationState *ts, InstKind kind, Value *left, Value *right)
{
	add_inst2(ts, kind, op_vreg(left), op_vreg(right));
}

static void
add_unop(TranslationState *ts, InstKind kind, Value *arg)
{
	add_inst1(ts, kind, op_vreg(arg));
}

void
translate_operand(void *user_data, Value *operand)
{
	TranslationState *ts = user_data;
	switch (operand->kind) {
	case VK_BLOCK:
		//printf(".L%zu:", operand->index);
		break;
	case VK_FUNCTION: {
		//Function *function = (void *) operand;
		//printf("%.*s", (int) function->name.len, function->name.str);
		break;
	}
	case VK_CONSTANT: {
		Constant *k = (void*) operand;
		add_mov_const(ts, operand, k->k);
		break;
	}
	default:
		//printf("v");
		//printf("%zu", operand->index);
		break;
	}
}
		  /*
typedef struct Instruction Instruction;
struct Instruction {
	InstKind kind;
	Instruction *prev;
	Instruction *next;
	Operand op[3];
};
*/

void
print_arg(Operand *op)
{
	switch (op->kind) {
	case OK_NONE:
		UNREACHABLE();
		break;
	case OK_VREG:
		printf("t%zu", op->vreg->index);
		break;
	case OK_INDIR_VREG:
		printf("[t%zu]", op->vreg->index);
		break;
	case OK_REG:
		printf("%s", reg_repr[op->reg]);
		break;
	case OK_INDIR_REG:
		printf("[%s]", reg_repr[op->reg]);
		break;
	case OK_LABEL:
		printf("%.*s", (int) (op->label.len), op->label.str);
		break;
	case OK_CONST:
		printf("%"PRIi64, op->constant);
	}
}

void
print_inst(Instruction *inst)
{
	printf("%s", inst_kind_repr[inst->kind]);
	for (size_t i = 0; i < 3 && inst->op[i].kind != OK_NONE; i++) {
		printf(" ");
		print_arg(&inst->op[i]);
	}
}

void
parse(Arena *arena, GArena *scratch, Str source, void (*error_callback)(void *user_data, const u8 *err_pos, const char *msg, va_list ap), void *user_data)
{
	Parser parser = {
		.arena = arena,
		.scratch = scratch,
		.user_data = user_data,
		.error_callback = error_callback,
		.lexer = lex_create(source),
		.had_error = false,
		.panic_mode = false,
		.env = NULL,
	};
	discard(&parser);

	env_push(&parser.env);
	parse_program(&parser);
	env_pop(&parser.env);

	size_t function_cnt = garena_cnt(&parser.functions, Function *);
	Function **functions = garena_array(&parser.functions, Function *);
	Block ***post_orders = arena_alloc(parser.arena, sizeof(*post_orders) * function_cnt);
	for (size_t f = 0; f < function_cnt; f++) {
		Function *function = functions[f];
		Block *block = function->entry;
		Block **post_order = arena_alloc(parser.arena, sizeof(*post_order) * function->block_cnt);
		post_orders[f] = post_order;
		size_t i = 0;
		dfs(block, &i, post_order);

		//for (size_t i = function->block_cnt; i--;) {
		for (size_t j = function->block_cnt; j--;) {
		//for (size_t j = 0; j < function->block_cnt; j++) {
			Block *block = post_order[j];
			printf("block%zu:\n", function->block_cnt - j - 1);
			//printf("block%zu:\n", block->base.index);

			for (Value *v = block->head; v; v = v->next, i++) {
				v->index = i;
			}

			for (Value *v = block->head; v; v = v->next) {
				printf("\tv%zu = ", v->index);
				switch (v->kind) {
#define CASE_OP(kind, ...) case VK_##kind:
#define OTHER(...)
		VALUE_KINDS(OTHER, CASE_OP, CASE_OP)
#undef CASE_OP
#undef OTHER
				{
					printf("%s ", value_kind_repr[v->kind]);
					bool first = true;
					for_each_operand(v, print_index, &first);
					printf("\n");
					break;
				}
				case VK_ALLOCA: {
					Alloca *a = (void*) v;
					printf("alloca %zu\n", a->size);
					break;
				}
				case VK_ARGUMENT: {
					Argument *a = (void*) v;
					printf("argument %zu\n", a->index);
					break;
				}
				default: UNREACHABLE();
				}
			}
		}

	}


	Function *function = parser.current_function;
	Block **post_order = post_orders[1];

	TranslationState ts_;
	TranslationState *ts = &ts_;

	add_inst1(ts, IK_LABEL, op_label(function->name));
	for (size_t b = function->block_cnt; b--;) {
	//for (size_t j = 0; j < function->block_cnt; j++) {
		Block *block = post_order[b];
		//printf(".L%zu:\n", function->block_cnt - b - 1);
		add_inst1(ts, IK_LABEL, op_label(arena_aprintf(parser.arena, ".L%zu", function->block_cnt - b - 1)));
		for (Value *v = block->head; v; v = v->next) {
			for_each_operand(v, translate_operand, ts);
			Value **ops = ((Operation *) v)->operands;
			switch (v->kind) {
			case VK_CONSTANT:
				break;
			case VK_ALLOCA:
				break;
			case VK_ARGUMENT:
				break;
			case VK_BLOCK:
				break;
			case VK_FUNCTION:
				break;

			case VK_ADD:
				add_copy(ts, v, ops[0]);
				add_binop(ts, IK_ADD, ops[0], ops[1]);
				break;
			case VK_SUB:
				add_copy(ts, v, ops[0]);
				add_binop(ts, IK_SUB, ops[0], ops[1]);
				break;
			case VK_MUL:
				add_copy(ts, v, ops[0]);
				add_binop(ts, IK_IMUL, ops[0], ops[1]);
				break;
			case VK_DIV:
			case VK_MOD:
				UNREACHABLE();
				UNREACHABLE();
				break;
			case VK_AND:
				add_copy(ts, v, ops[0]);
				add_binop(ts, IK_AND, ops[0], ops[1]);
				break;
			case VK_OR:
				add_copy(ts, v, ops[0]);
				add_binop(ts, IK_OR, ops[0], ops[1]);
				break;
			case VK_SHL:
				add_copy(ts, v, ops[0]);
				add_binop(ts, IK_SHL, ops[0], ops[1]);
				break;
			case VK_SHR:
				add_copy(ts, v, ops[0]);
				add_binop(ts, IK_SHR, ops[0], ops[1]);
				break;

			case VK_NEG:
				add_copy(ts, v, ops[0]);
				add_unop(ts, IK_NEG, ops[0]);
				break;
			case VK_NOT:
				add_copy(ts, v, ops[0]);
				add_unop(ts, IK_NOT, ops[0]);
				break;

			case VK_EQ:
				break;
			case VK_NEQ:
				break;
			case VK_LT:
				break;
			case VK_LEQ:
				break;
			case VK_GT:
				break;
			case VK_GEQ:
				break;

			case VK_LOAD:
				add_load(ts, v, ops[0]);
				break;
			case VK_STORE:
				add_store(ts, ops[0], ops[1]);
				break;
			case VK_GET_INDEX_PTR:
				break;
			case VK_CALL:
				add_inst1(ts, IK_CALL, op_label(((Function*)ops[0])->name));
				break;
			case VK_JUMP:
				add_inst1(ts, IK_JMP, op_label(arena_aprintf(parser.arena, ".L%zu", ops[0]->index)));
				break;
			case VK_BRANCH:
				add_binop(ts, IK_TEST, ops[0], ops[0]);
				add_inst1(ts, IK_JZ, op_label(arena_aprintf(parser.arena, ".L%zu", ops[2]->index)));
				add_inst1(ts, IK_JMP, op_label(arena_aprintf(parser.arena, ".L%zu", ops[1]->index)));
				break;
			case VK_RET:
				add_inst2(ts, IK_MOV, op_reg(R_RAX), op_vreg(ops[0]));
				add_inst0(ts, IK_RET);
				break;
			case VK_RETVOID:
				add_inst0(ts, IK_RET);
				break;
			default: UNREACHABLE();
			}
		}
	}

	size_t inst_cnt = garena_cnt(&ts->insts, Instruction);
	Instruction *insts = garena_array(&ts->insts, Instruction);
	for (size_t i = 0; i < inst_cnt; i++) {
		if (insts[i].kind == IK_LABEL) {
			printf("\n%.*s:\n", (int) (insts[i].op[0].label.len), insts[i].op[0].label.str);
			continue;
		}
		printf("\t");
		print_inst(&insts[i]);
		printf("\n");
	}

	if (parser.had_error) {
		//return NULL;
	}
	//return ast;
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
	error->msg = (u8 *) arena_vaprintf(&ec->arena, fmt, ap).str;
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

void
parse_source(ErrorContext *ec, Arena *arena, Str source)
{
	//size_t arena_start = arena_save(arena);
	GArena scratch;
	garena_init(&scratch);
	ec->source = source;
	parse(arena, &scratch, source, parser_verror, ec);
	garena_destroy(&scratch);
	/*
	if (!ast) {
		arena_restore(arena, arena_start);
		longjmp(ec->loc, 1);
	}
	return ast;
	*/
}

static void
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

	if (argc < 2) {
		goto end;
	}

	Str source = read_file(&ec, arena, argv[1]);
	parse_source(&ec, arena, source);

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
	arena_destroy(&ec.arena);
	arena_destroy(arena);
	return ec.error_head ? EXIT_FAILURE : EXIT_SUCCESS;
}
