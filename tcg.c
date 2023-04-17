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

#define garena_for_each(arena, type, name) \
	for (type *name = garena_array((arena), (type)), *end_ = garena_array((arena), (type)) + garena_cnt((arena), (type)); name != end_; name++)

#define container_of(member_ptr, type, member) \
	((type *) ((u8 *)(1 ? (member_ptr) : &((type *) 0)->member) - offsetof(type, member)))

#define GROW_ARRAY(array, new_count) \
	do { \
		(array) = realloc((array), (new_count) * sizeof((array)[0])); \
	} while(0)

#define ZERO_ARRAY(array, count) \
	do { \
		memset((array), 0, (count) * sizeof((array)[0])); \
	} while(0)

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

void print_str(FILE *f, Str s)
{
	fwrite(s.str, 1, s.len, f);
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

#include "defs.c"

typedef enum {
	R_NONE = 0,
	R_RAX,
	R_RBX,
	R_RCX,
	R_RDX,
	R_RSI,
	R_RDI,

	R_RSP,
	R_RBP,

	R__MAX,
} Reg;

static const char *reg_repr[] = {
	"NONE",
	"rax",
	"rbx",
	"rcx",
	"rdx",
	"rsi",
	"rdi",

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

	"spl",
	"bpl",
};

typedef enum {
	CC_Z = 0x04,
	CC_NZ = 0x05,
	CC_L = 0x0C,
	CC_GE = 0x0D,
	CC_LE = 0x0E,
	CC_G = 0x0F,
} CondCode;

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
	GArena functions; // array of Function *
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
	block->preds = NULL;
	block->pred_cnt = 0;
	block->succ_cnt = 0;
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
		if (i - 1 < argument_cnt) {
			call->operands[i] = as_rvalue(parser, carg);
			if (call->operands[i]->type != fun_type->param_types[i - 1]) {
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
	return cond;
	//Value *zero = create_const(parser, 0);
	//return add_binary(parser, VK_NEQ, cond, zero);
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

static void dfs(Block *block, size_t *index, Block **post_order);

void
function_finalize(Arena *arena, Function *function)
{
	function->post_order = arena_alloc(arena, sizeof(*function->post_order) * function->block_cnt);
	function->block_cnt = 0;
	dfs(function->entry, &function->block_cnt, function->post_order);
	for (size_t b = function->block_cnt, i = 0; b--; i++) {
		// Number the blocks in RPO
		function->post_order[b]->base.index = i;
		// Allocate storage for predecessors
		function->post_order[b]->preds = arena_alloc(arena, function->post_order[b]->pred_cnt * sizeof(function->post_order[b]->preds[0]));
		function->post_order[b]->base.visited = 0;
		function->post_order[b]->pred_cnt = 0;
		function->post_order[b]->succ_cnt = 0;
	}
	function->block_cnt = 0;
	dfs(function->entry, &function->block_cnt, function->post_order);
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
	Value **args = calloc(param_cnt, sizeof(args[0]));
	for (size_t i = 0; i < param_cnt; i++) {
		param_types[i] = params[i].type;
		args[i] = add_argument(parser, param_types[i], i);
	}
	for (size_t i = 0; i < param_cnt; i++) {
		Value *arg = args[i];
		Value *addr = add_alloca(parser, param_types[i]);
		add_binary(parser, VK_STORE, addr, arg);
		env_define(parser->env, params[i].name, addr);
	}
	free(args);
	statements(parser);
	garena_restore(parser->scratch, start);
	function_finalize(parser->arena, function);
	function->base.index = garena_cnt(&parser->functions, Function *);
	garena_push_value(&parser->functions, Function *, function);
	env_pop(&parser->env);
}

static void
external_declaration(Parser *parser)
{
	switch (peek(parser)) {
	case TK_STRUCT:
		struct_declaration(parser);
		break;
	case TK_TYPEDEF:
		typedef_declaration(parser);
		break;
	default:
		function_declaration(parser);
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
for_each_operand(Value *value, void (*fun)(void *user_data, size_t i, Value *operand), void *user_data)
{
	size_t operand_cnt = instruction_arg_cnt(value);
	if (operand_cnt == 0) {
	     return;
	}
	Operation *op = (void *) value;
	for (size_t i = 0; i < operand_cnt; i++) {
		fun(user_data, i, op->operands[i]);
	}
}

void
print_index(void *user_data, size_t i, Value *operand)
{
	FILE *f = user_data;
	if (i != 0) {
		fprintf(f, ", ");
	}
	switch (operand->kind) {
	case VK_BLOCK:
		fprintf(f, "block");
		fprintf(f, "%zu", operand->index);
		break;
	case VK_FUNCTION:
		fprintf(f, "function");
		fprintf(f, "%zu", operand->index);
		break;
	case VK_CONSTANT: {
		Constant *k = (void*) operand;
		fprintf(f, "%"PRIi64, k->k);
		break;
	}
	default:
		fprintf(f, "v");
		fprintf(f, "%zu", operand->index);
		break;
	}
}

static void
block_add_edge(Block *pred, Block *succ)
{
	assert(pred->base.kind == VK_BLOCK);
	assert(succ->base.kind == VK_BLOCK);
	// succs is static array of 2, so no need to worry about allocation
	pred->succs[pred->succ_cnt++] = succ;
	// only add to preds if someone allocated storage (second pass)
	if (succ->preds) {
		succ->preds[succ->pred_cnt++] = pred;
	} else {
		succ->pred_cnt++;
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
		block_add_edge(block, (Block *) op->operands[0]);
		dfs((Block *) op->operands[0], index, post_order);
		break;
	}
	case VK_BRANCH: {
		Operation *op = (void *) block->tail;
		assert(op->operands[1]->kind == VK_BLOCK);
		assert(op->operands[2]->kind == VK_BLOCK);
		block_add_edge(block, (Block *) op->operands[1]);
		block_add_edge(block, (Block *) op->operands[2]);
		dfs((Block *) op->operands[1], index, post_order);
		dfs((Block *) op->operands[2], index, post_order);
		break;
	}
	case VK_RET:
	case VK_RETVOID:
		block->succ_cnt = 0;
		break;
	default:
	     break;
	     UNREACHABLE();
	}
	block->base.visited = 2;
	post_order[(*index)++] = block;
}



void
print_reg(FILE *f, Oper reg)
{
	//if (reg <= 0) {
		//reg = -reg;
	if (reg < R__MAX) {
		fprintf(f, "%s", reg_repr[reg]);
	} else {
		fprintf(f, "t%"PRIi32, reg);
	}
}

void
print_reg8(FILE *f, Oper reg)
{
	//if (reg <= 0) {
		//reg = -reg;
	if (reg < R__MAX) {
		fprintf(f, "%s", reg_repr8[reg]);
	} else {
		fprintf(f, "t%"PRIi32, reg);
	}
}

void
print_inst_d(FILE *f, Inst *inst)
{
	InstDesc *desc = &inst_desc[inst->op];
	//printf("%s", desc->mnemonic);
	size_t i = 0;
	for (; i < desc->src_cnt; i++) {
		fprintf(f, " ");
		print_reg(f, inst->ops[i]);
	}
	for (; i < desc->imm_cnt; i++) {
		fprintf(f, " ");
		fprintf(f, "%"PRIi32, inst->ops[i]);
	}
	for (; i < desc->label_cnt; i++) {
		fprintf(f, " ");
		fprintf(f, ".BB%"PRIi32, inst->ops[i]);
	}
}

void
print_inst(FILE *f, Inst *inst)
{
	InstDesc *desc = &inst_desc[inst->op];
	const char *in = desc->format;
	while (*in) {
		char c = *in++;
		size_t i = (*in) - '0';
		switch (c) {
		case 'D':
			print_reg(f, inst->ops[i]);
			in++;
			break;
		case 'E':
			print_reg8(f, inst->ops[i]);
			in++;
			break;
		case 'S':
			print_reg(f, inst->ops[desc->dest_cnt + i]);
			in++;
			break;
		case 'I':
			fprintf(f, "%"PRIi32, inst->ops[desc->src_cnt + i]);
			in++;
			break;
		case 'C': {
			const char *cc;
			switch (inst->ops[desc->src_cnt + i]) {
			case CC_Z: cc = "z"; break;
			case CC_NZ: cc = "nz"; break;
			case CC_L: cc = "l"; break;
			case CC_GE: cc = "ge"; break;
			case CC_LE: cc = "le"; break;
			case CC_G: cc = "g"; break;
			default: UNREACHABLE();
			}
			fprintf(f, "%s", cc);
			in++;
			break;
		}
		case 'B':
			fprintf(f, ".BB%"PRIi32, inst->ops[desc->imm_cnt + i]);
			in++;
			break;
		case 'F':
			fprintf(f, "function%"PRIi32, inst->ops[desc->imm_cnt + i]);
			in++;
			break;
		default:
			fputc(c, f);
		}
	}
}


typedef struct {
	Arena *arena;
	MBlock *block;
	Inst **prev_pos;
	size_t stack_space;
	Oper index;
	size_t block_cnt;
	size_t callee_saved_reg_start;
	Inst *make_stack_space;
} TranslationState;

Inst *
create_inst(Arena *arena, OpCode op, va_list ap)
{
	InstDesc *desc = &inst_desc[op];
	size_t operand_cnt = desc->label_cnt;
	Inst *inst = arena_alloc(arena, sizeof(*inst) + operand_cnt * sizeof(inst->ops[0]));
	inst->op = op;
	for (size_t i = 0; i < operand_cnt; i++) {
		inst->ops[i] = va_arg(ap, Oper);
	}
	return inst;
}

Inst *
make_inst(Arena *arena, OpCode op, ...)
{
	va_list ap;
	va_start(ap, op);
	Inst *inst = create_inst(arena, op, ap);
	va_end(ap);
	return inst;
}

static Inst *
add_inst(TranslationState *ts, OpCode op, ...)
{
	va_list ap;
	va_start(ap, op);
	Inst *inst = create_inst(ts->arena, op, ap);
	va_end(ap);
	inst->next = NULL;
	inst->prev = ts->prev_pos == &ts->block->first ? NULL : container_of(ts->prev_pos, Inst, next);
	*ts->prev_pos = inst;
	ts->prev_pos = &inst->next;
	return inst;
}

static void
add_copy(TranslationState *ts, Oper dest, Oper src)
{
	add_inst(ts, OP_MOV, dest, src);
}

static void
add_set_zero(TranslationState *ts, Oper oper)
{
	// Set zero with `mov` so that we don't introduce additional constraints
	// on the register through XOR register uses.
	add_inst(ts, OP_MOVIMM, oper, 0);
	//add_inst(ts, OP_XOR, oper, oper, oper);
}

static void
add_unop(TranslationState *ts, OpCode op, Oper op1)
{
	add_inst(ts, op, op1, op1);
}

static void
add_binop(TranslationState *ts, OpCode op, Oper op1, Oper op2)
{
	add_inst(ts, op, op1, op1, op2);
}

static void
add_push(TranslationState *ts, Oper oper)
{
	add_inst(ts, OP_PUSH, oper);
}

static void
add_pop(TranslationState *ts, Oper oper)
{
	add_inst(ts, OP_POP, oper);
}

static Oper arg_regs[4] = { R_RDI, R_RSI, R_RDX, R_RCX };
#define ARRAY_LEN(arr) (sizeof((arr)) / sizeof((arr)[0]))

static void
add_call(TranslationState *ts, Oper res, Oper fun, Oper *args, size_t arg_cnt)
{
	Oper opers[ARRAY_LEN(arg_regs)] = {0};
	assert(arg_cnt <= ARRAY_LEN(arg_regs));
	for (size_t i = 0; i < arg_cnt; i++) {
		add_copy(ts, arg_regs[i], args[0]);
		opers[i] = arg_regs[i];
	}
	add_inst(ts, OP_CALL, R_RAX, R_RCX, R_RDX, R_RSI, R_RDI,
		opers[0],
		opers[1],
		opers[2],
		opers[3],
		fun
	);
	add_copy(ts, res, R_RAX);
}

static void
add_return(TranslationState *ts, Oper *ret_val)
{
	if (ret_val) {
		add_copy(ts, R_RAX, *ret_val);
	}
	size_t callee_saved_reg = ts->callee_saved_reg_start;
	add_copy(ts, R_RBX, callee_saved_reg++);
	add_copy(ts, R_RSP, R_RBP);
	add_pop(ts, R_RBP);
	// ret "reads" return value callee saved registers
	add_inst(ts, OP_RET, R_RAX, R_RBX);
}

static void
translate_unop(TranslationState *ts, OpCode op, Oper res, Oper *ops)
{
	add_copy(ts, res, ops[0]);
	add_unop(ts, op, res);
}

static void
translate_binop(TranslationState *ts, OpCode op, Oper res, Oper *ops)
{
	add_copy(ts, res, ops[0]);
	add_binop(ts, op, res, ops[1]);
}

static void
translate_shift(TranslationState *ts, OpCode op, Oper res, Oper *ops)
{
	add_copy(ts, res, ops[0]);
	add_copy(ts, R_RCX, ops[1]);
	add_inst(ts, op, res, R_RCX);
}

static void
translate_div(TranslationState *ts, Oper res, Oper *ops, bool modulo)
{
	add_set_zero(ts, R_RDX);
	add_copy(ts, R_RAX, ops[0]);
	add_inst(ts, OP_IDIV, R_RDX, R_RAX, R_RDX, R_RAX, ops[1]);
	Oper result = modulo ? R_RDX : R_RAX;
	add_copy(ts, res, result);
}

static void
translate_cmpop(TranslationState *ts, CondCode cc, Oper res, Oper *ops)
{
	add_set_zero(ts, res);
	add_inst(ts, OP_CMP, ops[0], ops[1]);
	add_inst(ts, OP_SETCC, res, cc);
}

typedef struct {
	TranslationState *ts;
	Oper opers[10];
} TranslateOperandState;

void
translate_operand(void *user_data, size_t i, Value *operand)
{
	TranslateOperandState *tos = user_data;
	Oper res;
	switch (operand->kind) {
	case VK_BLOCK:
		//printf(".L%zu:", operand->index);
		res = operand->index;
		break;
	case VK_FUNCTION: {
		//Function *function = (void *) operand;
		//printf("%.*s", (int) function->name.len, function->name.str);
		// TODO: this is really ugly, we return the index of function as
		// operand, even though it has nothing to do with operands
		res = operand->index;
		break;
	}
	case VK_CONSTANT: {
		Constant *k = (void*) operand;
		res = tos->ts->index++;
		add_inst(tos->ts, OP_MOVIMM, res, k->k);
		break;
	}
	case VK_ALLOCA: {
		Alloca *alloca = (Alloca *) operand;
		res = tos->ts->index++;
		add_inst(tos->ts, OP_LEA_RMC, res, R_RBP, 8 + alloca->size);
		break;
	}
	default:
		//printf("v");
		//printf("%zu", operand->index);
		res = operand->index;
		break;
	}
	tos->opers[i] = res;
}

void
translate_value(TranslationState *ts, Value *v)
{
	TranslateOperandState tos_;
	TranslateOperandState *tos = &tos_;
	tos->ts = ts;
	for_each_operand(v, translate_operand, tos);
	Oper *ops = &tos->opers[0];
	//Oper res = ts->index++;
	Oper res = v->index;
	switch (v->kind) {
	case VK_CONSTANT:
		break;
	case VK_ALLOCA: {
		Alloca *alloca = (Alloca *) v;
		size_t size = alloca->size;
		alloca->size = ts->stack_space;
		ts->stack_space += size;
		break;
	}
	case VK_ARGUMENT: {
		Argument *argument = (Argument *) v;
		Oper src = 0;
		switch (argument->index) {
		case 0: src = R_RDI; break;
		case 1: src = R_RSI; break;
		case 2: src = R_RDX; break;
		case 3: src = R_RCX; break;
		default: UNREACHABLE();
		}
		add_copy(ts, res, src);
		break;
	}
	case VK_BLOCK:
		UNREACHABLE();
		break;
	case VK_FUNCTION:
		UNREACHABLE();
		break;

	case VK_ADD:
		translate_binop(ts, OP_ADD, res, ops);
		break;
	case VK_SUB:
		translate_binop(ts, OP_SUB, res, ops);
		break;
	case VK_MUL:
		translate_binop(ts, OP_IMUL, res, ops);
		break;
	case VK_DIV:
		translate_div(ts, res, ops, false);
		break;
	case VK_MOD:
		translate_div(ts, res, ops, true);
		break;
	case VK_AND:
		translate_binop(ts, OP_AND, res, ops);
		break;
	case VK_OR:
		translate_binop(ts, OP_OR, res, ops);
		break;
	case VK_SHL:
		translate_shift(ts, OP_SHL, res, ops);
		break;
	case VK_SHR:
		translate_shift(ts, OP_SHR, res, ops);
		break;
	case VK_NEG:
		translate_unop(ts, OP_NEG, res, ops);
		break;
	case VK_NOT:
		translate_unop(ts, OP_NOT, res, ops);
		break;
	case VK_EQ:
		translate_cmpop(ts, CC_Z, res, ops);
		break;
	case VK_NEQ:
		translate_cmpop(ts, CC_NZ, res, ops);
		break;
	case VK_LT:
		translate_cmpop(ts, CC_L, res, ops);
		break;
	case VK_LEQ:
		translate_cmpop(ts, CC_LE, res, ops);
		break;
	case VK_GT:
		translate_cmpop(ts, CC_G, res, ops);
		break;
	case VK_GEQ:
		translate_cmpop(ts, CC_GE, res, ops);
		break;

	case VK_LOAD:
		add_inst(ts, OP_MOV_RM, res, ops[0]);
		break;
	case VK_STORE:
		add_inst(ts, OP_MOV_MR, ops[0], ops[1]);
		break;
	case VK_GET_INDEX_PTR:
		break;
	case VK_CALL: {
		Operation *call = (void *) v;
		Function *function = (Function *) call->operands[0];
		FunctionType *fun_type = (FunctionType *) function->base.type;
		add_call(ts, res, ops[0], &ops[1], fun_type->param_cnt);
		break;
	}
	case VK_JUMP:
		add_inst(ts, OP_JMP, ops[0]);
		break;
	case VK_BRANCH:
		add_inst(ts, OP_TEST, ops[0], ops[0]);
		add_inst(ts, OP_JCC, CC_Z, ops[2]);
		add_inst(ts, OP_JMP, ops[1]);
		break;
	case VK_RET:
		add_return(ts, &ops[0]);
		break;
	case VK_RETVOID:
		add_return(ts, NULL);
		break;
	default: UNREACHABLE();
	}
}

void
number_operand(void *user_data, size_t i, Value *operand)
{
	size_t *idx = user_data;
	switch (operand->kind) {
	case VK_CONSTANT:
		operand->index = (*idx)++;
		break;
	default:;
	}
}


typedef struct RegAllocState RegAllocState;

typedef struct {
	size_t n;
	size_t N;
	u8 *matrix;

	GArena *adj_list;
} InterferenceGraph;

void
ig_grow(InterferenceGraph *ig, size_t old_capacity, size_t new_capacity)
{
	if (old_capacity >= new_capacity) {
		return;
	}
	GROW_ARRAY(ig->matrix, new_capacity * new_capacity);
	GROW_ARRAY(ig->adj_list, new_capacity);
	ZERO_ARRAY(&ig->adj_list[old_capacity], new_capacity - old_capacity);
}

void
ig_reset(InterferenceGraph *ig, size_t size)
{
	ig->n = size;
	ig->N = size * size;
	ZERO_ARRAY(ig->matrix, ig->N);
	for (size_t i = 0; i < size; i++) {
		garena_restore(&ig->adj_list[i], 0);
	}
}

void
ig_destroy(InterferenceGraph *ig)
{
	free(ig->matrix);
	for (size_t i = 0; i < ig->n; i++) {
		garena_destroy(&ig->adj_list[i]);
	}
	free(ig->adj_list);
}

bool
ig_interfere(InterferenceGraph *ig, Oper op1, Oper op2)
{
	if (op1 == R_NONE || op2 == R_NONE) {
		return true;
	}
	u8 one = ig->matrix[op1 * ig->n + op2];
	u8 two = ig->matrix[op2 * ig->n + op1];
	assert(one == two);
	return one;
}


typedef struct {
	size_t head;
	size_t tail;
	size_t capacity;
	Oper *sparse;
	Oper *dense;
} WorkList;

void
wl_grow(WorkList *wl, size_t new_capacity)
{
	wl->capacity = new_capacity;
	GROW_ARRAY(wl->dense, new_capacity);
	GROW_ARRAY(wl->sparse, new_capacity);
}

void
wl_init_all(WorkList *wl, Oper op)
{
	assert(op < wl->capacity);
	wl->tail = op;
	for (size_t i = 0; i < op; i++) {
		wl->dense[i] = i;
		wl->sparse[i] = i;
	}
	for (size_t i = wl->head; i < wl->tail; i++) {
		assert(wl->sparse[wl->dense[i]] == (Oper) i);
	}
}

void
wl_init_all_reverse(WorkList *wl, Oper op)
{
	assert(op < wl->capacity);
	wl->tail = op;
	for (size_t i = 0; i < op; i++) {
		wl->dense[i] = op - i - 1;
		wl->sparse[op - i - 1] = i;
	}
	for (size_t i = wl->head; i < wl->tail; i++) {
		assert(wl->sparse[wl->dense[i]] == (Oper) i);
	}
}

bool
wl_add(WorkList *wl, Oper op)
{
	assert(op < wl->capacity);
	if (wl->sparse[op] < wl->head || wl->sparse[op] >= wl->tail || wl->dense[wl->sparse[op]] != op) {
		wl->sparse[op] = wl->tail;
		wl->dense[wl->tail] = op;
		wl->tail += 1;
		for (size_t i = wl->head; i < wl->tail; i++) {
			assert(wl->sparse[wl->dense[i]] == (Oper) i);
		}
		return true;
	}
	return false;
}

void
wl_union(WorkList *wl, WorkList *other)
{
	for (size_t i = other->head; i < other->tail; i++) {
		wl_add(wl, other->dense[i]);
	}
}

bool
wl_has(WorkList *wl, Oper op)
{
	return wl->sparse[op] >= wl->head && wl->sparse[op] < wl->tail && wl->dense[wl->sparse[op]] == op;
}

bool
wl_remove(WorkList *wl, Oper op)
{
	assert(op < wl->capacity);
	if (wl_has(wl, op)) {
		wl->tail -= 1;
		Oper last = wl->dense[wl->tail];
		wl->dense[wl->sparse[op]] = last;
		wl->sparse[last] = wl->sparse[op];
		wl->dense[wl->tail] = op;
		for (size_t i = wl->head; i < wl->tail; i++) {
			assert(wl->sparse[wl->dense[i]] == (Oper) i);
		}
		return true;
	}
	return false;
}

bool
wl_take(WorkList *wl, Oper *taken)
{
	assert(wl->head <= wl->tail);
	if (wl->head == wl->tail) {
		return false;
	}
	*taken = wl->dense[wl->head++];
	return true;
}

bool
wl_take_back(WorkList *wl, Oper *taken)
{
	assert(wl->head <= wl->tail);
	if (wl->head == wl->tail) {
		return false;
	}
	*taken = wl->dense[--wl->tail];
	return true;
}

Oper
wl_cnt(WorkList *wl)
{
	assert(wl->head <= wl->tail);
	return wl->tail - wl->head;
}

void
wl_reset(WorkList *wl)
{
	wl->head = wl->tail = 0;
}

bool
wl_eq(WorkList *wl, WorkList *other)
{
	assert(wl->capacity == other->capacity);
	if (wl->tail - wl->head != other->tail - other->head) {
		return false;
	}
	for (size_t i = wl->head; i < wl->tail; i++) {
		if (!wl_has(other, wl->dense[i])) {
			return false;
		}
	}
	return true;
}

void
wl_destroy(WorkList *wl)
{
	free(wl->sparse);
	free(wl->dense);
	*wl = (WorkList) {0};
}


void
print_mfunction(FILE *f, MFunction *mfunction)
{
	fprintf(f, "function%zu:\n", mfunction->func->base.index);
	print_str(f, mfunction->func->name);
	fprintf(f, ":\n");
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = &mfunction->mblocks[b];
		fprintf(f, ".BB%zu:\n", mblock->index);
		//for (Inst *inst = mblock->first; inst; inst = inst->next) {
		for (Inst *inst = mblock->first; inst; inst = inst->next) {
			fprintf(f, "\t");
			print_inst(f, inst);
			fprintf(f, "\n");
		}
	}
}

struct RegAllocState {
	Arena *arena;
	MFunction *mfunction;
	size_t vreg_capacity;
	size_t block_capacity;
	size_t move_capacity;

	// Parameters
	size_t reg_avail;

	// Final register allocation
	Oper *reg_assignment;

	u8 *to_spill;
	Oper *alias;

	// Spill cost related
	u8 *def_counts;
	u8 *use_counts;

	// Degrees of nodes.
	u32 *degree;

	InterferenceGraph ig;
	WorkList live_set;
	WorkList block_work_list;
	WorkList *live_in;

	// Worklists for the different register allocation phases
	WorkList spill_wl;
	WorkList freeze_wl;
	WorkList simplify_wl;
	WorkList moves_wl;
	WorkList active_moves_wl;
	WorkList stack;

	GArena gmoves; // Array of Inst *
	GArena *move_list; // Array of GArena of Oper
};

void
reg_alloc_state_init(RegAllocState *ras, Arena *arena)
{
	*ras = (RegAllocState) {
		.arena = arena,
		.reg_avail = 6,
	};
}

void
reg_alloc_state_reset(RegAllocState *ras)
{
	assert(ras->mfunction->vreg_cnt > 0);
	size_t old_vreg_capacity = ras->vreg_capacity;
	if (ras->vreg_capacity == 0) {
		ras->vreg_capacity = 64;
	}
	while (ras->vreg_capacity < ras->mfunction->vreg_cnt) {
		ras->vreg_capacity += ras->vreg_capacity;
	}
	size_t old_block_capacity = ras->block_capacity;
	if (ras->block_capacity == 0) {
		ras->block_capacity = 16;
	}
	while (ras->block_capacity < ras->mfunction->mblock_cnt) {
		ras->block_capacity += ras->block_capacity;
	}

	if (old_block_capacity < ras->block_capacity) {
		GROW_ARRAY(ras->live_in, ras->block_capacity);
		wl_grow(&ras->block_work_list, ras->block_capacity);
		ZERO_ARRAY(&ras->live_in[old_block_capacity], ras->block_capacity - old_block_capacity);
		for (size_t i = old_block_capacity; i < ras->block_capacity; i++) {
			wl_grow(&ras->live_in[i], ras->vreg_capacity);
		}
	}

	if (old_vreg_capacity < ras->vreg_capacity) {
		GROW_ARRAY(ras->reg_assignment, ras->vreg_capacity);
		GROW_ARRAY(ras->to_spill, ras->vreg_capacity);
		GROW_ARRAY(ras->alias, ras->vreg_capacity);
		GROW_ARRAY(ras->def_counts, ras->vreg_capacity);
		GROW_ARRAY(ras->use_counts, ras->vreg_capacity);
		GROW_ARRAY(ras->degree, ras->vreg_capacity);
		ig_grow(&ras->ig, old_vreg_capacity, ras->vreg_capacity);
		wl_grow(&ras->live_set, ras->vreg_capacity);
		for (size_t i = 0; i < old_block_capacity; i++) {
			wl_grow(&ras->live_in[i], ras->vreg_capacity);
		}
		wl_grow(&ras->spill_wl, ras->vreg_capacity);
		wl_grow(&ras->freeze_wl, ras->vreg_capacity);
		wl_grow(&ras->simplify_wl, ras->vreg_capacity);
		//wl_grow(&ras->moves_wl, ras->vreg_capacity);
		//wl_grow(&ras->active_moves_wl, ras->vreg_capacity);
		wl_grow(&ras->stack, ras->vreg_capacity);
		// gmoves doesn't need to grow
		GROW_ARRAY(ras->move_list, ras->vreg_capacity);
	}

	ZERO_ARRAY(ras->reg_assignment, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->to_spill, ras->mfunction->vreg_cnt);
	for (size_t i = 0; i < ras->mfunction->vreg_cnt; i++) {
		ras->alias[i] = i;
	}
	ZERO_ARRAY(ras->def_counts, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->use_counts, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->degree, ras->mfunction->vreg_cnt);
	ig_reset(&ras->ig, ras->mfunction->vreg_cnt);
	wl_reset(&ras->live_set);
	wl_reset(&ras->block_work_list);
	for (size_t i = 0; i < ras->mfunction->mblock_cnt; i++) {
		wl_reset(&ras->live_in[i]);
	}
	wl_reset(&ras->spill_wl);
	wl_reset(&ras->freeze_wl);
	wl_reset(&ras->simplify_wl);
	//wl_reset(&ras->moves_wl);
	//wl_reset(&ras->active_moves_wl);
	wl_reset(&ras->stack);
	garena_restore(&ras->gmoves, 0);
	for (size_t i = 0; i < ras->mfunction->vreg_cnt; i++) {
		garena_restore(&ras->move_list[i], 0);
	}
}

void
reg_alloc_state_destroy(RegAllocState *ras)
{
	free(ras->reg_assignment);
	free(ras->to_spill);
	free(ras->def_counts);
	free(ras->use_counts);
	ig_destroy(&ras->ig);
	wl_destroy(&ras->live_set);
	for (size_t i = 0; i < ras->block_capacity; i++) {
		wl_destroy(&ras->live_in[i]);
	}
	free(ras->live_in);
	wl_destroy(&ras->spill_wl);
	wl_destroy(&ras->freeze_wl);
	wl_destroy(&ras->simplify_wl);
	wl_destroy(&ras->stack);
}

void
reg_alloc_state_init_for_function(RegAllocState *ras, MFunction *mfunction)
{
	ras->mfunction = mfunction;
	//reg_alloc_state_reset(ras);
}


void
ig_add(InterferenceGraph *ig, Oper op1, Oper op2)
{
	if (op1 == op2 || ig_interfere(ig, op1, op2)) {
		return;
	}
	fprintf(stderr, "Adding interference ");
	print_reg(stderr, op1);
	fprintf(stderr, " ");
	print_reg(stderr, op2);
	fprintf(stderr, "\n");
	assert(ig->matrix[op1 * ig->n + op2] == 0);
	assert(ig->matrix[op2 * ig->n + op1] == 0);
	ig->matrix[op1 * ig->n + op2] = 1;
	ig->matrix[op2 * ig->n + op1] = 1;
	garena_push_value(&ig->adj_list[op1], Oper, op2);
	garena_push_value(&ig->adj_list[op2], Oper, op1);
	// TODO: Restructure Interefrence graph and Register allocation state.
	RegAllocState *ras = container_of(ig, RegAllocState, ig);
	ras->degree[op1]++;
	ras->degree[op2]++;
}


void
get_live_out(RegAllocState *ras, Block *block, WorkList *live_set)
{
	// live-out of this block is the union of live-ins of all
	// successors
	wl_reset(live_set);
	for (size_t i = 0; i < block->succ_cnt; i++) {
		size_t succ = block->succs[i]->base.index;
		wl_union(live_set, &ras->live_in[succ]);
	}
}

void
live_step(WorkList *live_set, Inst *inst)
{
	InstDesc *desc = &inst_desc[inst->op];

	// Remove definitions from live.
	for (size_t i = 0; i < desc->dest_cnt; i++) {
		wl_remove(live_set, inst->ops[i]);
	}
	// Add uses to live.
	for (size_t i = desc->dest_cnt; i < desc->src_cnt; i++) {
		wl_add(live_set, inst->ops[i]);
	}
}

void
interference_step(RegAllocState *ras, WorkList *live_set, Inst *inst)
{
	InterferenceGraph *ig = &ras->ig;
	InstDesc *desc = &inst_desc[inst->op];

	// Special handling of moves:
	// 1) We don't want to introduce interference between move source and
	//    destination.
	// 2) We want to note all moves and for all nodes the moves they are
	//    contained in, because we want to try to coalesce the moves later.
	if (inst->op == OP_MOV) {
		// Remove uses from live to prevent interference between move
		// destination and source.
		for (size_t i = desc->dest_cnt; i < desc->src_cnt; i++) {
			wl_remove(live_set, inst->ops[i]);
		}

		// Accumulate moves.
		size_t index = garena_cnt(&ras->gmoves, Inst *);
		garena_push_value(&ras->gmoves, Inst *, inst);
		garena_push_value(&ras->move_list[inst->ops[0]], Oper, index);
		garena_push_value(&ras->move_list[inst->ops[1]], Oper, index);
	}


        // Add all definitions to live. Because the next step adds
        // interferences between all definitions and all live, we will thus also
        // make all the definitions interfere with each other. Since the
	// liveness step (run after us) removes all definitions, this is OK and
	// local to the current instruction.
        for (size_t i = 0; i < desc->dest_cnt; i++) {
		wl_add(live_set, inst->ops[i]);
	}

	// Add interferences of all definitions with all live.
	for (size_t j = live_set->head; j < live_set->tail; j++) {
		size_t live = live_set->dense[j];
		for (size_t i = 0; i < desc->dest_cnt; i++) {
			ig_add(ig, inst->ops[i], live);
		}
	}
}

void
spill(RegAllocState *ras)
{
	// TODO: Infinite spill costs for uses immediately following
	// definitions.

	// NOTE: Beware, we can't naively renumber loads and stores with
	// temporaries, since we can have multiple assignments:
	//
	// mov t17, [rbp-16] // should use the same t17
	// add t18, t9       // should use the same t17
	print_mfunction(stderr, ras->mfunction);
	for (size_t b = 0; b < ras->mfunction->mblock_cnt; b++) {
		MBlock *mblock = &ras->mfunction->mblocks[b];
		for (Inst *inst = mblock->first; inst; inst = inst->next) {
			fprintf(stderr, "\n");
			print_inst(stderr, inst);
			fprintf(stderr, "\n");
			InstDesc *desc = &inst_desc[inst->op];
			// Add loads for all spilled uses.
			for (size_t i = desc->dest_cnt; i < desc->src_cnt; i++) {
				if (!ras->to_spill[inst->ops[i]]) {
					continue;
				}
				fprintf(stderr, "load ");
				print_reg(stderr, inst->ops[i]);
				fprintf(stderr, "\n");
				//Oper temp = mfunction->vreg_cnt++;
				Oper temp = inst->ops[i];
				Inst *load = make_inst(ras->arena, OP_MOV_RMC, temp, R_RBP, 8 + ras->to_spill[inst->ops[i]]);
				load->prev = inst->prev;
				load->next = inst;
				inst->prev->next = load;
				inst->prev = load;
				inst->ops[i] = temp;
			}
			// Add stores for all spilled defs.
			for (size_t i = 0; i < desc->dest_cnt; i++) {
				if (!ras->to_spill[inst->ops[i]]) {
					continue;
				}
				fprintf(stderr, "store ");
				print_reg(stderr, inst->ops[i]);
				fprintf(stderr, "\n");
				//Oper temp = mfunction->vreg_cnt++;
				Oper temp = inst->ops[i];
				Inst *store = make_inst(ras->arena, OP_MOV_MCR, R_RBP, temp, 8 + ras->to_spill[inst->ops[i]]);
				store->prev = inst;
				store->next = inst->next;
				inst->next->prev = store;
				inst->next = store;
				inst->ops[i] = temp;
				inst = inst->next;
		}
		}
	}
	print_mfunction(stderr, ras->mfunction);
}

void
apply_reg_assignment(RegAllocState *ras)
{
	for (size_t b = 0; b < ras->mfunction->mblock_cnt; b++) {
		MBlock *mblock = &ras->mfunction->mblocks[b];
		for (Inst *inst = mblock->first; inst; inst = inst->next) {
			InstDesc *desc = &inst_desc[inst->op];
			size_t i = 0;
			for (; i < desc->src_cnt; i++) {
				assert(inst->ops[i] >= 0);
				inst->ops[i] = ras->reg_assignment[ras->alias[inst->ops[i]]];
			}
		}
	}
}

size_t
number_values(Function *function, size_t start_index)
{
	size_t i = start_index;
	for (size_t b = function->block_cnt; b--;) {
		Block *block = function->post_order[b];
		for (Value *v = block->head; v; v = v->next) {
			//for_each_operand(v, number_operand, &i);
			v->index = i++;
		}
	}
	return i;
}

void
print_function(FILE *f, Function *function)
{
	print_str(f, function->name);
	fprintf(f, ":\n");
	//for (size_t i = function->block_cnt; i--;) {
	for (size_t j = function->block_cnt; j--;) {
		Block *block = function->post_order[j];
		fprintf(f, "block%zu: ", block->base.index);
		if (block->preds) {
			for (size_t p = 0; p < block->pred_cnt; p++) {
				if (p != 0) {
					fprintf(f, ", ");
				}
				Block *pred = block->preds[p];
				fprintf(f, "block%zu", pred->base.index);
			}
		}
		fprintf(f, "\n");

		for (Value *v = block->head; v; v = v->next) {
			fprintf(f, "\tv%zu = ", v->index);
			switch (v->kind) {
#define CASE_OP(kind, ...) case VK_##kind:
#define OTHER(...)
	VALUE_KINDS(OTHER, CASE_OP, CASE_OP)
#undef CASE_OP
#undef OTHER
			{
				fprintf(f, "%s ", value_kind_repr[v->kind]);
				for_each_operand(v, print_index, f);
				fprintf(f, "\n");
				break;
			}
			case VK_ALLOCA: {
				Alloca *a = (void*) v;
				fprintf(f, "alloca %zu\n", a->size);
				break;
			}
			case VK_ARGUMENT: {
				Argument *a = (void*) v;
				fprintf(f, "argument %zu\n", a->index);
				break;
			}
			default: UNREACHABLE();
			}
		}
	}
}

typedef struct {
	size_t function_cnt;
	Function **functions;
} Module;

Module *
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

	//Block ***post_orders = arena_alloc(parser.arena, sizeof(*post_orders) * function_cnt);

	//	Block *block = function->entry;
	//	Block **post_order = arena_alloc(parser.arena, sizeof(*post_order) * function->block_cnt);
	//	post_orders[f] = post_order;
	//	size_t i = 0;
	//	dfs(block, &i, post_order);

	if (parser.had_error) {
		return NULL;
	}
	Module *module = arena_alloc(arena, sizeof(*module));
	module->function_cnt = garena_cnt(&parser.functions, Function *);
	module->functions = move_to_arena(arena, &parser.functions, 0, Function *);
	for (size_t f = 0; f < module->function_cnt; f++) {
		//Function *function = module->functions[f];
		//print_function(function);
	}
	return module;
}

void
calculate_spill_cost(MFunction *mfunction, u8 *def_counts, u8 *use_counts)
{
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = &mfunction->mblocks[b];
		for (Inst *inst = mblock->first; inst; inst = inst->next) {
			//print_inst(stderr, inst);
			//fprintf(stderr, "\n");
			InstDesc *desc = &inst_desc[inst->op];
			size_t j = 0;
			for (; j < desc->dest_cnt; j++) {
				def_counts[inst->ops[j]]++;
				//fprintf(stderr, "adding def of ");
				//print_reg(stderr, inst->ops[j]);
				//fprintf(stderr, "\n");
			}
			for (; j < desc->src_cnt; j++) {
				use_counts[inst->ops[j]]++;
				//fprintf(stderr, "adding use of ");
				//print_reg(stderr, inst->ops[j]);
				//fprintf(stderr, "\n");
			}
		}
	}
}

MFunction *
translate_function(Arena *arena, Function *function, size_t start_index)
{
	Block **post_order = function->post_order;

	TranslationState ts_ = {
		.arena = arena,
		.index = start_index,
		.stack_space = 8,
		.prev_pos = NULL,
		.block = NULL,
	};
	TranslationState *ts = &ts_;
	GArena gmblocks = {0};

	for (size_t b = function->block_cnt; b--;) {
	//for (size_t j = 0; j < function->block_cnt; j++) {
		Block *block = post_order[b];
		//printf(".L%zu:\n", function->block_cnt - b - 1);
		MBlock *mblock = garena_push(&gmblocks, MBlock);
		mblock->block = block;
		mblock->index = block->base.index;
		mblock->first = NULL;
		ts->prev_pos = &mblock->first;
		ts->block = mblock;
		if (b == function->block_cnt - 1) {
			ts->callee_saved_reg_start = ts->index;
			add_push(ts, R_RBP);
			add_copy(ts, R_RBP, R_RSP);
			// Add instruction to make stack space, since we may
			// spill we don't know how much stack space to reserve
			// yet, we will replace the dummy '0' with proper stack
			// space requirement after register allocation.
			ts->make_stack_space = add_inst(ts, OP_SUB_IMM, R_RSP, R_RSP, 0);
			// rbx, r12, r13, r14, r15
			add_copy(ts, ts->index++, R_RBX);
		}
		for (Value *v = block->head; v; v = v->next) {
			translate_value(ts, v);
		}
		mblock->last = ts->prev_pos == &mblock->first ? NULL : container_of(ts->prev_pos, Inst, next);
	}

	MFunction *mfunction = arena_alloc(arena, sizeof(*mfunction));
	*mfunction = (MFunction) {
		.func = function,
		.mblocks = garena_array(&gmblocks, MBlock),
		.mblock_cnt = garena_cnt(&gmblocks, MBlock),
		.vreg_cnt = ts->index,
		.stack_space = ts->stack_space,
		.make_stack_space = ts->make_stack_space,
	};
	function->mfunc= mfunction;
	return mfunction;
}

void
build_interference_graph(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	WorkList *live_set = &ras->live_set;

	wl_init_all_reverse(&ras->block_work_list, mfunction->mblock_cnt);
	Oper b;
	while (wl_take(&ras->block_work_list, &b)) {
		MBlock *mblock = &mfunction->mblocks[b];
		Block *block = mblock->block;
		get_live_out(ras, block, live_set);
		// process the block back to front, updating live_set in the
		// process
		for (Inst *inst = mblock->last; inst; inst = inst->prev) {
			live_step(live_set, inst);
		}
		if (!wl_eq(live_set, &ras->live_in[b])) {
			WorkList tmp = ras->live_in[b];
			ras->live_in[b] = *live_set;
			*live_set = tmp;
			for (size_t i = 0; i < block->pred_cnt; i++) {
				size_t pred = block->preds[i]->base.index;
				wl_add(&ras->block_work_list, pred);
			}
		}
	}

	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = &mfunction->mblocks[b];
		Block *block = mblock->block;
		get_live_out(ras, block, live_set);
		for (Inst *inst = mblock->last; inst; inst = inst->prev) {
			interference_step(ras, live_set, inst);
			live_step(live_set, inst);
		}

	}

	// Physical registers are initialized with infinite degree. This makes
	// sure that simplification doesn't ever see tham transition to
	// non-significant degree and thus pushing them on the stack.
	for (size_t i = 0; i < R__MAX; i++) {
		ras->degree[i] = ras->mfunction->vreg_cnt + ras->reg_avail;
	}
}

bool
is_move_related(RegAllocState *ras, Oper i)
{
	fprintf(stderr, "Is move related ");
	print_reg(stderr, i);
	fprintf(stderr, "\n");
	Inst **moves = garena_array(&ras->gmoves, Inst *);
	GArena *gmove_list = &ras->move_list[i];
	Oper *move_list = garena_array(gmove_list, Oper);
	size_t move_cnt = garena_cnt(gmove_list, Oper);
	for (size_t i = 0; i < move_cnt; i++) {
		Oper move_index = move_list[i];
		Inst *move = moves[move_index];
		fprintf(stderr, "Moved in \t");
		print_inst(stderr, move);
		fprintf(stderr, "\n");
		if (wl_has(&ras->active_moves_wl, move_index) || wl_has(&ras->moves_wl, move_index)) {
			return true;
		}
	}
	fprintf(stderr, "Not move related\n");
	return false;
}


void
for_each_adjacent(RegAllocState *ras, Oper op, void (*fun)(RegAllocState *ras, Oper neighbour))
{
	GArena *gadj_list = &ras->ig.adj_list[op];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t i = 0; i < adj_cnt; i++) {
		Oper neighbour = adj_list[i];
		if (wl_has(&ras->stack, neighbour) || ras->alias[neighbour] != neighbour) {
			continue;
		}
		fun(ras, neighbour);
	}
}

void
initialize_worklists(RegAllocState *ras)
{
	size_t move_cnt = garena_cnt(&ras->gmoves, Inst *);
	size_t old_move_capacity = ras->move_capacity;
	if (ras->move_capacity == 0) {
		ras->move_capacity = 16;
	}
	while (ras->move_capacity < move_cnt) {
		ras->move_capacity += ras->move_capacity;
	}
	if (old_move_capacity < ras->move_capacity) {
		wl_grow(&ras->moves_wl, ras->move_capacity);
		wl_grow(&ras->active_moves_wl, ras->move_capacity);
	}
	wl_reset(&ras->moves_wl);
	wl_init_all(&ras->moves_wl, move_cnt);
	wl_reset(&ras->active_moves_wl);

	size_t vreg_cnt = ras->mfunction->vreg_cnt;
	for (size_t i = R__MAX; i < vreg_cnt; i++) {
		GArena *gadj_list = &ras->ig.adj_list[i];
		size_t adj_cnt = garena_cnt(gadj_list, Oper);
		assert(adj_cnt == ras->degree[i]);
		if (ras->degree[i] >= ras->reg_avail) {
			wl_add(&ras->spill_wl, i);
			fprintf(stderr, "Starting in spill ");
			print_reg(stderr, i);
			fprintf(stderr, " (%zu)\n", (size_t) ras->degree[i]);
		} else if (is_move_related(ras, i)) {
			fprintf(stderr, "Starting in freeze ");
			print_reg(stderr, i);
			wl_add(&ras->freeze_wl, i);
			fprintf(stderr, " (%zu)\n", (size_t) ras->degree[i]);
		} else {
			wl_add(&ras->simplify_wl, i);
			fprintf(stderr, "Starting in simplify ");
			print_reg(stderr, i);
			fprintf(stderr, " (%zu)\n", (size_t) ras->degree[i]);
		}
	}
}

double
spill_metric(RegAllocState *ras, Oper i)
{
	fprintf(stderr, "Spill cost for ");
	print_reg(stderr, i);
	fprintf(stderr, " degree: %"PRIu32", defs: %zu, uses: %zu\n", ras->degree[i], (size_t) ras->def_counts[i], (size_t) ras->use_counts[i]);
	return (double) ras->degree[i] / (ras->def_counts[i] + ras->use_counts[i]);
}

void
enable_moves_for_one(RegAllocState *ras, Oper op)
{
	Inst **moves = garena_array(&ras->gmoves, Inst *);
	Oper *node_moves = garena_array(&ras->move_list[op], Oper);
	size_t node_move_cnt = garena_cnt(&ras->move_list[op], Oper);
	for (size_t k = 0; k < node_move_cnt; k++) {
		Oper m = node_moves[k];
		if (wl_remove(&ras->active_moves_wl, m)) {
			Inst *move = moves[m];
			fprintf(stderr, "Enabling move: \t");
			print_inst(stderr, move);
			fprintf(stderr, "\n");
			wl_add(&ras->moves_wl, m);
		}
	}
}

void
enable_moves_for_node_and_neighbours(RegAllocState *ras, Oper op)
{
	enable_moves_for_one(ras, op);
	for_each_adjacent(ras, op, enable_moves_for_one);
	//GArena *gadj_list = &ras->ig.adj_list[op];
	//Oper *adj_list = garena_array(gadj_list, Oper);
	//size_t adj_cnt = garena_cnt(gadj_list, Oper);
	//for (size_t i = 0; i < adj_cnt; i++) {
	//	Oper neighbour = adj_list[i];
	//	enable_moves_for_one(ras, neighbour);
	//}
}

void
decrement_degree(RegAllocState *ras, Oper op)
{
	fprintf(stderr, "Removing interference with ");
	print_reg(stderr, op);
	fprintf(stderr, "\n");
	assert(ras->degree[op] > 0);
	u32 old_degree = ras->degree[op]--;
	if (old_degree == ras->reg_avail) {
		fprintf(stderr, "%zu %zu\n", (size_t) op, (size_t) R__MAX);
		assert(op >= R__MAX);
		fprintf(stderr, "Move from spill to %s ", is_move_related(ras, op) ? "freeze" : "simplify");
		print_reg(stderr, op);
		fprintf(stderr, "\n");
		enable_moves_for_node_and_neighbours(ras, op);
		wl_remove(&ras->spill_wl, op);
		if (is_move_related(ras, op)) {
			wl_add(&ras->freeze_wl, op);
		} else {
			wl_add(&ras->simplify_wl, op);
		}
	}
}

void
freeze_moves(RegAllocState *ras, Oper u)
{
	fprintf(stderr, "Freezing moves of ");
	print_reg(stderr, u);
	fprintf(stderr, "\n");
	Inst **moves = garena_array(&ras->gmoves, Inst *);
	Oper *node_moves = garena_array(&ras->move_list[u], Oper);
	size_t node_move_cnt = garena_cnt(&ras->move_list[u], Oper);
	for (size_t k = 0; k < node_move_cnt; k++) {
		Oper m = node_moves[k];
		Inst *move = moves[m];
		fprintf(stderr, "freezing in: \t");
		print_inst(stderr, move);
		fprintf(stderr, "\n");
		if (!wl_remove(&ras->active_moves_wl, m)) {
			wl_remove(&ras->moves_wl, m);
		}
		Oper v = move->ops[0] != u ? move->ops[0] : move->ops[1];
		if (!is_move_related(ras, v) && ras->degree[v] < ras->reg_avail) {
			fprintf(stderr, "Move from freeze to simplify in freeze ");
			print_reg(stderr, v);
			fprintf(stderr, "\n");
			wl_remove(&ras->freeze_wl, v);
			wl_add(&ras->simplify_wl, v);
		}
	}
}

void
freeze(RegAllocState *ras)
{
	Oper i;
	if (wl_take_back(&ras->freeze_wl, &i)) {
		fprintf(stderr, "Freezing node ");
		print_reg(stderr, i);
		fprintf(stderr, "\n");
		wl_add(&ras->simplify_wl, i);
		freeze_moves(ras, i);
	}
}


void
simplify(RegAllocState *ras)
{
	Oper i;
	while (wl_take_back(&ras->simplify_wl, &i)) {
		wl_add(&ras->stack, i);
		fprintf(stderr, "Pushing ");
		print_reg(stderr, i);
		fprintf(stderr, "\n");
		for_each_adjacent(ras, i, decrement_degree);
		//GArena *gadj_list = &ras->ig.adj_list[i];
		//Oper *adj_list = garena_array(gadj_list, Oper);
		//size_t adj_cnt = garena_cnt(gadj_list, Oper);
		//for (size_t j = 0; j < adj_cnt; j++) {
		//	Oper neighbour = adj_list[j];
		//	decrement_degree(ras, neighbour);
		//}
	}
}

void
select_potential_spill_if_needed(RegAllocState *ras)
{
	if (wl_cnt(&ras->spill_wl) != 0) {
		fprintf(stderr, "Potential spill\n");
		Oper candidate = ras->spill_wl.dense[ras->spill_wl.head];
		size_t max = spill_metric(ras, candidate);
		for (size_t j = ras->spill_wl.head; j < ras->spill_wl.tail; j++) {
			Oper i = ras->spill_wl.dense[j];
			size_t curr = spill_metric(ras, i);
			if (curr > max) {
				max = curr;
				candidate = i;
			}
		}
		fprintf(stderr, "Choosing for spill ");
		print_reg(stderr, candidate);
		fprintf(stderr, "\n");
		wl_remove(&ras->spill_wl, candidate);
		wl_add(&ras->simplify_wl, candidate);
		freeze_moves(ras, candidate);
	}
}

void
add_to_worklist(RegAllocState *ras, Oper op)
{
	if (op >= R__MAX && !is_move_related(ras, op) && ras->degree[op] < ras->reg_avail) {
		fprintf(stderr, "Move from freeze to simplify ");
		print_reg(stderr, op);
		fprintf(stderr, "\n");
		wl_remove(&ras->freeze_wl, op);
		wl_add(&ras->simplify_wl, op);
	}
}

size_t
significant_neighbour_cnt(RegAllocState *ras, Oper op)
{
	size_t n = 0;
	GArena *gadj_list = &ras->ig.adj_list[op];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t j = 0; j < adj_cnt; j++) {
		Oper t = adj_list[j];
		if (wl_has(&ras->stack, t) || ras->alias[t] != t) {
			continue;
		}
		n += ras->degree[t] >= ras->reg_avail;
	}
	return n;
}

bool
ok(RegAllocState *ras, Oper t, Oper r)
{
	return ras->degree[t] < ras->reg_avail || t < R__MAX || ig_interfere(&ras->ig, t, r);
}

bool
precolored_coalesce_heuristic(RegAllocState *ras, Oper u, Oper v)
{
	GArena *gadj_list = &ras->ig.adj_list[v];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t j = 0; j < adj_cnt; j++) {
		Oper t = adj_list[j];
		if (wl_has(&ras->stack, t) || ras->alias[t] != t) {
			continue;
		}
		if (!ok(ras, t, u)) {
			return false;
		}
	}
	return true;
}

bool
conservative_coalesce_heuristic(RegAllocState *ras, Oper u, Oper v)
{
	size_t n = significant_neighbour_cnt(ras, u) + significant_neighbour_cnt(ras, v);
	return n < ras->reg_avail;
}

bool
are_coalesceble(RegAllocState *ras, Oper u, Oper v)
{
	if (u < R__MAX) {
		// TODO: Why is the precolored heuristic causing spills?
		if (precolored_coalesce_heuristic(ras, u, v) > conservative_coalesce_heuristic(ras, u, v)) {
			precolored_coalesce_heuristic(ras, u, v);
			conservative_coalesce_heuristic(ras, u, v);
			return false;
		}
		return precolored_coalesce_heuristic(ras, u, v);
	} else {
		return conservative_coalesce_heuristic(ras, u, v);
	}
}

void
combine(RegAllocState *ras, Oper u, Oper v)
{
	fprintf(stderr, "Combining " );
	print_reg(stderr, u);
	fprintf(stderr, " and " );
	print_reg(stderr, v);
	fprintf(stderr, "\n");
	if (!wl_remove(&ras->freeze_wl, v)) {
		// TODO assert this?
		wl_remove(&ras->spill_wl, v);
	}
	ras->alias[v] = u;
	// merge node moves
	Oper *other_moves = garena_array(&ras->move_list[v], Oper);
	size_t other_move_cnt = garena_cnt(&ras->move_list[v], Oper);
	for (size_t i = 0; i < other_move_cnt; i++) {
		// TODO: deduplicate?
		garena_push_value(&ras->move_list[u], Oper, other_moves[i]);
	}
	// add edges
	GArena *gadj_list = &ras->ig.adj_list[v];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t i = 0; i < adj_cnt; i++) {
		Oper t = adj_list[i];
		if (wl_has(&ras->stack, t) || ras->alias[t] != t) {
			continue;
		}
		ig_add(&ras->ig, u, t);
		decrement_degree(ras, t);
	}
	if (ras->degree[u] > ras->reg_avail && wl_remove(&ras->freeze_wl, u)) {
		wl_add(&ras->simplify_wl, u);
	}
}

void
coalesce(RegAllocState *ras)
{
	Inst **moves = garena_array(&ras->gmoves, Inst *);
	Oper m;
	if (wl_take(&ras->moves_wl, &m)) {
		Inst *move = moves[m];
		fprintf(stderr, "Coalescing: \t");
		print_inst(stderr, move);
		fprintf(stderr, "\n");
		Oper u = ras->alias[move->ops[0]];
		Oper v = ras->alias[move->ops[1]];
		if (v < R__MAX) {
			Oper tmp = u;
			u = v;
			v = tmp;
		}
		if (u == v) {
			// already coalesced
			add_to_worklist(ras, u);
		} else if (v < R__MAX || ig_interfere(&ras->ig, u, v)) {
			// constrained
			add_to_worklist(ras, u);
			add_to_worklist(ras, v);
		} else if (are_coalesceble(ras, u, v)) {
			// coalesce
			combine(ras, u, v);
			add_to_worklist(ras, u);
		} else {
			wl_add(&ras->active_moves_wl, m);
		}
	}
}

bool
assign_registers(RegAllocState *ras)
{
	bool have_spill = false;
	MFunction *mfunction = ras->mfunction;

	// Physical registers are assigned themselves.
	for (size_t i = 0; i < R__MAX; i++) {
		ras->reg_assignment[i] = i;
	}

	Oper i;
	while (wl_take_back(&ras->stack, &i)) {
		fprintf(stderr, "Popping ");
		print_reg(stderr, i);
		fprintf(stderr, "\n");
		Oper used = 0;
		// If this one neighbours with some node that
		// has already color allocated (i.e. not on the
		// the stack) and it is not spilled (i.e. not R_NONE), make sure we
		// don't use the same register.
		GArena *gadj_list = &ras->ig.adj_list[i];
		Oper *adj_list = garena_array(gadj_list, Oper);
		size_t adj_cnt = garena_cnt(gadj_list, Oper);
		for (size_t j = 0; j < adj_cnt; j++) {
			size_t neighbour = ras->alias[adj_list[j]];
			if (!wl_has(&ras->stack, neighbour) && ras->reg_assignment[neighbour] != R_NONE) {
				used |= 1 << (ras->reg_assignment[neighbour] - 1);
			}
		}
		Oper reg = 0;
		for (size_t ri = 1; ri <= ras->reg_avail; ri++) {
			size_t mask = 1 << (ri - 1);
			if ((used & mask) == 0) {
				reg = ri;
				break;
			}
		}
		if (reg == 0) {
			fprintf(stderr, "Out of registers at ");
			print_reg(stderr, i);
			fprintf(stderr, "\n");
			ras->to_spill[i] = mfunction->stack_space;
			assert(mfunction->stack_space < 240);
			mfunction->stack_space += 8;
			have_spill = true;
		}
		ras->reg_assignment[i] = reg;
		fprintf(stderr, "allocated ");
		print_reg(stderr, i);
		fprintf(stderr, " to ");
		print_reg(stderr, reg);
		fprintf(stderr, "\n");
	}
	for (size_t i = 0; i < mfunction->vreg_cnt; i++) {
		if (ras->alias[i] != i) {
			fprintf(stderr, "Coalesced ");
			print_reg(stderr, i);
			fprintf(stderr, " to ");
			print_reg(stderr, ras->alias[i]);
			fprintf(stderr, "\n");
		}
	}
	return !have_spill;
}

// Move all arguments and callee saved registers to temporaries at the
// start of the function. Then restore callee saved registers at the end
// of the function.

// Make all caller saved registers interfere with calls.


void
reg_alloc_function(RegAllocState *ras, MFunction *mfunction)
{
	print_mfunction(stderr, mfunction);

	reg_alloc_state_init_for_function(ras, mfunction);

	for (;;) {
		reg_alloc_state_reset(ras);
		calculate_spill_cost(mfunction, ras->def_counts, ras->use_counts);
		build_interference_graph(ras);
		initialize_worklists(ras);
		for (;;) {
			simplify(ras);
			coalesce(ras);
			freeze(ras);
			select_potential_spill_if_needed(ras);

			if (wl_cnt(&ras->simplify_wl) == 0 && wl_cnt(&ras->spill_wl) == 0 && wl_cnt(&ras->freeze_wl) == 0) {
				break;
			}
		}

		if (assign_registers(ras)) {
			break;
		}
		spill(ras);
	}

	// Fixup stack space amount reserved at the start of the function
	mfunction->make_stack_space->ops[2] = mfunction->stack_space;
	apply_reg_assignment(ras);
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

Module *
parse_source(ErrorContext *ec, Arena *arena, Str source)
{
	size_t arena_start = arena_save(arena);
	GArena scratch;
	garena_init(&scratch);
	ec->source = source;
	Module *module = parse(arena, &scratch, source, parser_verror, ec);
	garena_destroy(&scratch);

	if (!module) {
		arena_restore(arena, arena_start);
		longjmp(ec->loc, 1);
	}
	return module;
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
	Module *module = parse_source(&ec, arena, source);
	Function **functions = module->functions;
	size_t function_cnt = module->function_cnt;

	RegAllocState ras;
	reg_alloc_state_init(&ras, arena);

	for (size_t i = 0; i < function_cnt; i++) {
		size_t index = number_values(functions[i], R__MAX);
		print_function(stderr, functions[i]);
		translate_function(arena, functions[i], index);
		reg_alloc_function(&ras, functions[i]->mfunc);
	}

	printf("section .text\n");
	printf("\tglobal _start\n");
	printf("\n");
	printf("_start:\n");
	printf("\txor rbp, rbp\n");
	printf("\tand rsp, -8\n");
	printf("\tcall main\n");
	printf("\tmov rdi, rax\n");
	printf("\tmov rax, 60\n");
	printf("\tsyscall\n");
	for (size_t i = 0; i < function_cnt; i++) {
		printf("\n");
		print_mfunction(stdout, functions[i]->mfunc);
	}

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
