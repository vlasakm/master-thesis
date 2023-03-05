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
	size_t parameter_cnt;
	Type **parameter_types;
} FunctionType;

typedef struct {
	Type base;
	Type *child;
} PointerType;

Type TYPE_VOID = { .kind = TY_VOID };
Type TYPE_INT = { .kind = TY_INT };

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


typedef enum {
	VK_CONST,
	VK_ARG,
	VK_INST,
	VK_ALLOCA,
} ValueKind;

typedef struct Value Value;

struct Value {
	ValueKind kind;
	Type *type;
	size_t index;
	Value *prev;
	Value *next;
};

#define INST_KINDS(_) \
	_(UNDEFINED, "undefined", 0) \
	_(NOP, "nop", 0) \
	_(IDENTITY, "identity", 0) \
	_(CONSTANT, "constant", 0) \
	_(ARGUMENT, "argument", 0) \
	\
	_(ADD, "add", 2) \
	_(SUB, "sub", 2) \
	_(MUL, "mul", 2) \
	_(DIV, "div", 2) \
	_(MOD, "mod", 2) \
	_(AND, "and", 2) \
	_(OR,  "or",  2) \
	_(SHL, "shl", 2) \
	_(SHR, "shr", 2) \
	\
	_(NEG, "neg", 1) \
	_(NOT, "not", 1) \
	\
	_(EQ,  "eq",  2)  \
	_(NEQ, "neq", 2) \
	_(LT,  "lt",  2) \
	_(LEQ, "leq", 2) \
	_(GT,  "gt",  2) \
	_(GEQ, "geq", 2) \
	\
	_(LOAD, "load", 1) \
	_(STORE, "store", 2) \
	_(GET_INDEX_PTR, "get_index_ptr", 2) \
	_(CALL, "call", 0) \
	_(JUMP, "jump", 1) \
	_(BRANCH, "branch", 2) \

typedef enum {
#define INST_ENUM(kind, ...) IK_##kind,
INST_KINDS(INST_ENUM)
#undef INST_ENUM
} InstructionKind;

char *inst_kind_repr[] = {
#define INST_REPR(_, repr, ...) repr,
INST_KINDS(INST_REPR)
#undef INST_REPR
};

u8 inst_kind_param_cnt[] = {
#define INST_PARAM_CNT(_a, _b, param_cnt) param_cnt,
INST_KINDS(INST_PARAM_CNT)
#undef INST_PARAM_CNT
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


typedef struct Block Block;
typedef struct Function Function;

typedef struct {
	Value base;
	InstructionKind kind;
	Block *block;
	Value *operands[];
} Instruction;

struct Block {
	Value base;
	Function *function;
	Value *head;
	Value *tail;
};

struct Function {
	Value base;
	Type *type;
	Block *blocks;
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

static Block *
add_block(Parser *parser)
{
	Block *block = arena_alloc(parser->arena, sizeof(*block));
	return block;
}

static void
add_to_block(Parser *parser, Value *value)
{
	if (parser->prev_pos != &parser->current_block->head) {
		value->prev = container_of(parser->prev_pos, Value, next);
	} else {
		value->prev = NULL;
	}
	*parser->prev_pos = value;
	parser->prev_pos = &value->next;
	parser->current_block->tail = value;
}

static Instruction *
add_instruction(Parser *parser, InstructionKind kind, size_t operand_cnt)
{
	Instruction *inst = arena_alloc(parser->arena, sizeof(*inst) + sizeof(inst->operands[0]) * operand_cnt);
	add_to_block(parser, &inst->base);
	inst->base.kind = VK_INST;
	inst->kind = kind;
	return inst;
}

static Value *
add_unary(Parser *parser, InstructionKind kind, Value *arg)
{
	Instruction *inst = add_instruction(parser, kind, 1);
	inst->operands[0] = arg;
	return &inst->base;
}

static Value *
add_binary(Parser *parser, InstructionKind kind, Value *left, Value *right)
{
	Instruction *inst = add_instruction(parser, kind, 2);
	inst->operands[0] = left;
	inst->operands[1] = right;
	return &inst->base;
}

static Type *
create_pointer(Arena *arena, Type *child)
{
	PointerType *ptr_type = arena_alloc(arena, sizeof(*ptr_type));
	ptr_type->base.kind = TY_POINTER;
	ptr_type->child = child;
	return &ptr_type->base;
}

static Value *
add_alloca(Parser *parser, Type *type)
{
	Alloca *alloca = arena_alloc(parser->arena, sizeof(*alloca));
	add_to_block(parser, &alloca->base);
	alloca->base.kind = VK_ALLOCA;
	alloca->base.type = create_pointer(parser->arena, type);
	alloca->size = type_size(type);
	return &alloca->base;
}


static Value *
as_rvalue(Parser *parser, CValue cvalue)
{
	if (cvalue.lvalue) {
		return add_unary(parser, IK_LOAD, cvalue.value);
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
		return NULL;
	}
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
add_const(Parser *parser, i64 value)
{
	Constant *k = arena_alloc(parser->arena, sizeof(*k));
	add_to_block(parser, &k->base);
	k->base.kind = VK_CONST;
	k->base.type = &TYPE_INT;
	k->k = value;
	return &k->base;
}

static CValue
nullerr(Parser *parser)
{
	TokenKind tok = peek(parser);
	parser_error(parser, parser->lookahead, true, "Invalid start of expression %s", tok_repr[tok]);
	return rvalue(NULL);
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
		return rvalue(add_const(parser, value));
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
	// TODO: ?
	return rvalue(NULL);
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
		result = add_unary(parser, IK_NEG, arg);
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
	Value *zero = add_const(parser, 0);
	return rvalue(add_binary(parser, IK_NEQ, arg, zero));
}

static CValue
bitnot(Parser *parser)
{
	eat(parser, TK_TILDE);
	CValue carg = expression_bp(parser, 14);
	Value *arg = as_rvalue(parser, carg);
	return rvalue(add_unary(parser, IK_NOT, arg));
}

static CValue
cmp(Parser *parser, CValue cleft, int rbp)
{
	TokenKind tok = discard(parser).kind;
	CValue cright = expression_bp(parser, rbp);
	Value *left = as_rvalue(parser, cleft);
	Value *right = as_rvalue(parser, cright);
	InstructionKind kind;
	switch (tok) {
	case TK_EQUAL_EQUAL:   kind = IK_EQ;  break;
	case TK_BANG_EQUAL:    kind = IK_NEQ; break;
	case TK_LESS:          kind = IK_LT;  break;
	case TK_LESS_EQUAL:    kind = IK_LEQ; break;
	case TK_GREATER:       kind = IK_GT;  break;
	case TK_GREATER_EQUAL: kind = IK_GEQ; break;
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
	InstructionKind kind;
	switch (tok) {
	case TK_PLUS:     kind = IK_ADD; break;
	case TK_MINUS:    kind = IK_SUB; break;
	case TK_ASTERISK: kind = IK_MUL; break;
	case TK_SLASH:    kind = IK_DIV; break;
	case TK_PERCENT:  kind = IK_MOD; break;
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
	InstructionKind kind;
	switch (tok) {
	case TK_AMP:             kind = IK_AND; break;
	case TK_BAR:             kind = IK_OR;  break;
	case TK_LESS_LESS:       kind = IK_SHL; break;
	case TK_GREATER_GREATER: kind = IK_SHR; break;
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
	return rvalue(add_binary(parser, IK_GET_INDEX_PTR, left, right));
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
	size_t argument_cnt = fun_type->parameter_cnt;
	Instruction *call = add_instruction(parser, IK_CALL, argument_cnt);

	size_t i = 0;
	while (!try_eat(parser, TK_RPAREN)) {
		CValue carg = expression_no_comma(parser);
		if (i < argument_cnt) {
			call->operands[i] = as_rvalue(parser, carg);
			if (call->operands[i]->type != fun_type->parameter_types[i]) {
				parser_error(parser, parser->lookahead, false, "Argument type doesn't equal parameter type");
			}
		}
		i += 1;
		if (!try_eat(parser, TK_COMMA)) {
			eat(parser, TK_RPAREN);
			break;
		}
	}
	if (i != argument_cnt) {
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
	add_binary(parser, IK_STORE, left, right);
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

static void
function_declaration(Parser *parser)
{
	UNREACHABLE();
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
		type = create_pointer(parser->arena, type);
	}

	if (!allow_void && type == &TYPE_VOID) {
		return NULL;
	}

	return type;
}

static void
variable_declaration(Parser *parser)
{
	Type *type = parse_type(parser, false);
	eat(parser, TK_IDENTIFIER);
	Str name = prev_tok(parser).str;
	Value *addr = add_alloca(parser, type);
	assign(parser, lvalue(addr), 2);
	eat(parser, TK_SEMICOLON);
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
parse_program(Parser *parser)
{
	while (peek(parser) != TK_EOF) {
		//external_declaration(parser);
		switch (peek(parser)) {
		case TK_INT:
			variable_declarations(parser);
			break;
		default:
			expression(parser);
			eat(parser, TK_SEMICOLON);
		}
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
	return rvalue(NULL);
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
instruction_arg_cnt(Instruction *inst)
{
	switch (inst->kind) {
	case IK_CALL:
		return ((FunctionType *) inst->operands[0]->type)->parameter_cnt;
	default:
		return inst_kind_param_cnt[inst->kind];
	}
}

void
for_each_operand(Value *value, void (*fun)(void *user_data, Value *operand), void *user_data)
{
	if (value->kind != VK_INST) {
		return;
	}
	Instruction *inst = (void *) value;
	size_t operand_cnt = instruction_arg_cnt(inst);
	for (size_t i = 0; i < operand_cnt; i++) {
		fun(user_data, inst->operands[i]);
	}
}

void
print_index(void *user_data, Value *operand)
{
	bool *first = user_data;
	printf("%sv%zu", *first ? "" : ", ", operand->index);
	*first = false;
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

	Block *block = add_block(&parser);
	parser.current_block = block;
	parser.prev_pos = &block->head;

	env_push(&parser.env);
	parse_program(&parser);
	env_pop(&parser.env);

	size_t i = 0;
	for (Value *v = block->head; v; v = v->next, i++) {
		v->index = i;
	}
	for (Value *v = block->tail; v; v = v->prev) {
		printf("v%zu = ", v->index);
		switch (v->kind) {
		case VK_CONST: {
			Constant *k = (void*) v;
			printf("loadimm %"PRIi64"\n", k->k);
			break;
		}
		case VK_INST: {
			Instruction *i = (void*) v;
			printf("%s ", inst_kind_repr[i->kind]);
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
		default: UNREACHABLE();
		}
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

u8 *
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
	return mem;
}


static void
verror(ErrorContext *ec, const u8 *pos, char *kind, bool fatal, const char *fmt, va_list ap)
{
	Error *error = arena_alloc(&ec->arena, sizeof(*error));
	error->msg = arena_vaprintf(&ec->arena, fmt, ap);
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
