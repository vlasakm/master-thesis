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

#include "utils.h"
#include "arena.h"
#include "worklist.h"

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef int8_t  i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;

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

Str PRINTF_LIKE(2)
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
	TY_STRUCT,
} TypeKind;

typedef struct {
	TypeKind kind;
} Type;

typedef struct {
	Type base;
	Type *child;
} PointerType;

typedef struct {
	Str name;
	Type *type;
} Parameter;

typedef struct {
	Type base;
	Type *ret_type;
	size_t param_cnt;
	Parameter *params;
} FunctionType;

typedef struct {
	Str name;
	Type *type;
	size_t offset;
} Field;

typedef struct {
	Type base;
	size_t size;
	size_t field_cnt;
	Field *fields;
} StructType;

Type TYPE_VOID = { .kind = TY_VOID };
Type TYPE_INT = { .kind = TY_INT };

static size_t
type_size(Type *type)
{
	switch (type->kind) {
	case TY_VOID: return 0;
	case TY_INT:  return 8;
	case TY_POINTER:
		return 8;
	case TY_FUNCTION:
		UNREACHABLE();
		break;
	case TY_STRUCT:
		return ((StructType *) type)->size;
	}
	UNREACHABLE();
}

static Type *
type_pointer(Arena *arena, Type *child)
{
	PointerType *ptr_type = arena_alloc(arena, sizeof(*ptr_type));
	ptr_type->base.kind = TY_POINTER;
	ptr_type->child = child;
	return &ptr_type->base;
}

static bool
type_is_pointer(Type *pointer_type)
{
	return pointer_type->kind == TY_POINTER;
}

static Type *
pointer_child(Type *pointer_type)
{
	assert(type_is_pointer(pointer_type));
	return ((PointerType *) pointer_type)->child;
}

static Type *
type_function(Arena *arena, Type *ret_type, Parameter *parameters, size_t param_cnt)
{
	FunctionType *fun_type = arena_alloc(arena, sizeof(*fun_type));
	fun_type->base.kind = TY_FUNCTION;
	fun_type->ret_type = ret_type;
	fun_type->params = parameters;
	fun_type->param_cnt = param_cnt;
	return &fun_type->base;
}

static Type *
type_struct(Arena *arena, Field *fields, size_t field_cnt)
{
	StructType *struct_type = arena_alloc(arena, sizeof(*struct_type));
	struct_type->base.kind = TY_STRUCT;
	struct_type->fields = fields;
	struct_type->field_cnt = field_cnt;

	// TODO: alignment
	size_t offset = 0;

	for (size_t i = 0; i < field_cnt; i++) {
		// TODO: align
		fields[i].offset = offset;
		offset += type_size(fields[i].type);
	}

	struct_type->size = offset;

	return &struct_type->base;
}

static bool
types_compatible(Type *a, Type *b)
{
	if (a == b) {
		return true;
	} else if (type_is_pointer(a) && type_is_pointer(b)) {
		return types_compatible(pointer_child(a), pointer_child(b));
	}
	return false;
}

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

	R__RIP,
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
	CC_O = 0x00,
	CC_NO = 0x01,
	CC_B = 0x02,
	CC_NAE = 0x02,
	CC_C = 0x02,
	CC_NB = 0x03,
	CC_AE = 0x03,
	CC_NC = 0x03,
	CC_Z = 0x04,
	CC_E = 0x04,
	CC_NZ = 0x05,
	CC_NE = 0x05,
	CC_BE = 0x06,
	CC_NA = 0x06,
	CC_NBE = 0x07,
	CC_A = 0x07,
	CC_S = 0x08,
	CC_NS = 0x09,
	CC_P = 0x0A,
	CC_PE = 0x0A,
	CC_NP = 0x0B,
	CC_PO = 0x0B,
	CC_L = 0x0C,
	CC_NGE = 0x0C,
	CC_NL = 0x0D,
	CC_GE = 0x0D,
	CC_LE = 0x0E,
	CC_NG = 0x0E,
	CC_NLE = 0x0F,
	CC_G = 0x0F,
} CondCode;

static const char *cc_repr[] = {
	"o",
	"no",
	"b",
	"ae",
	"z",
	"nz",
	"be",
	"a",
	"s",
	"ns",
	"p",
	"np",
	"l",
	"ge",
	"le",
	"g",
};

#include "defs.c"

CondCode
cc_invert(CondCode cc)
{
	// Flip the least significant bit.
	return cc ^ 1;
}

bool
g1_is_commutative(X86Group1 g1)
{
	switch (g1) {
	case G1_ADD:
	case G1_IMUL:
	case G1_AND:
	case G1_OR:
	case G1_TEST:
		return true;
	default:
		return false;
	}
}

size_t instruction_arg_cnt(Value *value);

bool
value_is_terminator(Value *value)
{
	switch (VK(value)) {
	case VK_JUMP:
	case VK_BRANCH:
	case VK_RET:
	case VK_RETVOID:
		return true;
	case VK_BLOCK:
		UNREACHABLE();
	default:
		return false;
	}
}

size_t
block_pred_cnt(Block *block)
{
	return block->pred_cnt_;
}

Block **
block_preds(Block *block)
{
	return block->preds_;
}

size_t
block_succ_cnt(Block *block)
{
	Value *last = block->base.prev;
	switch (VK(last)) {
	case VK_JUMP:
		return 1;
	case VK_BRANCH:
		return 2;
	case VK_RET:
	case VK_RETVOID:
		return 0;
	default:
		UNREACHABLE();
	}
}

Block **
block_succs(Block *block)
{
	Value *last = block->base.prev;
	switch (VK(last)) {
	case VK_JUMP:
		return (Block **) &((Operation *) last)->operands[0];
	case VK_BRANCH:
		return (Block **) &((Operation *) last)->operands[1];
	default:
		assert(block_succ_cnt(block) == 0);
		return NULL;
	}
}

#define FOR_EACH_BLOCK_PRED(block, pred) \
	for (Block **pred = block_preds(block), **last = pred + block_pred_cnt(block); pred != last; pred++)

#define FOR_EACH_BLOCK_SUCC(block, succ) \
	for (Block **succ = block_succs(block), **last = succ + block_succ_cnt(block); succ != last; succ++)

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
	void *value;
} Entry;

typedef struct {
	Entry *entries;
	size_t entry_cnt;
	size_t capacity;
} Table;

void
table_init(Table *table)
{
	table->entry_cnt = 0;
	table->capacity = 0;
	table->entries = NULL;
}

void
table_destroy(Table *table)
{
	FREE_ARRAY(table->entries, table->capacity);
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
	FREE_ARRAY(table->entries, table->capacity);
	table->entries = entries;
	table->capacity = capacity;
}

bool
table_get(Table *table, Str key, void **value)
{
	if (table->entry_cnt == 0) {
		return false;
	}
	Entry *entry = table_find_entry(table->entries, table->capacity, key);
	if (entry->key.str == NULL) {
		return false;
	}
	*value = entry->value;
	return true;
}

bool
table_insert(Table *table, Str key, void *value)
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

typedef struct {
	Table *scopes;
	size_t scope_cnt;
	size_t scope_cap;
} Environment;

void
env_push(Environment *env)
{
	if (env->scope_cnt == env->scope_cap) {
		env->scope_cap = env->scope_cap ? env->scope_cap * 2 : 8;
		GROW_ARRAY(env->scopes, env->scope_cap);
	}
	table_init(&env->scopes[env->scope_cnt++]);
}

void
env_pop(Environment *env)
{
	assert(env->scope_cnt > 0);
	table_destroy(&env->scopes[--env->scope_cnt]);
}

void
env_define(Environment *env, Str name, Value *value)
{
	assert(env->scope_cnt > 0);
	table_insert(&env->scopes[env->scope_cnt - 1], name, value);
}

bool
env_lookup(Environment *env, Str name, void **value)
{
	for (size_t i = env->scope_cnt; i--;) {
		if (table_get(&env->scopes[i], name, value)) {
			return true;
		}
	}
	return false;
}

void
env_free(Environment *env)
{
	for (size_t i = 0; i < env->scope_cnt; i++) {
		table_destroy(&env->scopes[--env->scope_cnt]);
	}
	FREE_ARRAY(env->scopes, env->scope_cnt);
}


#include "lexer.c"

typedef struct {
	bool lvalue;
	Value *value;
} CValue;

Value NOP = { .type = &TYPE_VOID, .kind = VK_NOP };

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
	Environment env;
	Table type_env;
	Function *current_function;
	GArena functions; // array of Function *
	GArena globals; // array of Global *
	Block *current_block;
	Block *continue_block;
	Block *break_block;
} Parser;

typedef struct {
	Type *type;
	Str name;
} TypedName;

static void PRINTF_LIKE(4)
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
curr_tok(Parser *parser)
{
	return parser->lookahead;
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

static Token
eat(Parser *parser, TokenKind kind)
{
	TokenKind tok = peek(parser);
	if (tok != kind) {
		parser_error(parser, parser->lookahead, true, "Expected %s, found %s", tok_repr[kind], tok_repr[tok]);
		// TODO: don't discard when error?
	}
	return discard(parser);
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
create_block(Arena *arena, Function *function)
{
	Block *block = arena_alloc(arena, sizeof(*block));
	*block = (Block) {0};
	value_init(&block->base, VK_BLOCK, type_pointer(arena, &TYPE_VOID));
	block->base.next = &block->base;
	block->base.prev = &block->base;
	block->base.parent = &function->base;
	block->preds_ = NULL;
	block->pred_cnt_ = 0;
	block->pred_cap_ = 0;
	block->base.index = function->block_cap++;
	return block;
}

static Block *
add_block(Parser *parser)
{
	return create_block(parser->arena, parser->current_function);
}

void prepend_value(Value *pos, Value *new);

static void
append_to_block(Block *block, Value *new)
{
	if (!block) {
		return;
	}
	prepend_value(&block->base, new);
	new->parent = &block->base;
}

static Operation *
create_operation(Arena *arena, Block *block, ValueKind kind, Type *type, size_t operand_cnt)
{
	Operation *op = arena_alloc(arena, sizeof(*op) + sizeof(op->operands[0]) * operand_cnt);
	value_init(&op->base, kind, &TYPE_INT);
	op->base.kind = kind;
	op->base.type = type;
	return op;
}

static Value *
create_unary(Arena *arena, Block *block, ValueKind kind, Type *type, Value *arg)
{
	Operation *op = create_operation(arena, block, kind, type, 1);
	op->operands[0] = arg;
	return &op->base;
}

static Operation *
add_operation(Parser *parser, ValueKind kind, Type *type, size_t operand_cnt)
{
	Operation *op = create_operation(parser->arena, parser->current_block, kind, type, operand_cnt);
	append_to_block(parser->current_block, &op->base);
	return op;
}

static Value *
add_unary(Parser *parser, ValueKind kind, Type *type, Value *arg)
{
	Operation *op = add_operation(parser, kind, type, 1);
	op->operands[0] = arg;
	return &op->base;
}

static Value *
add_binary(Parser *parser, ValueKind kind, Type *type, Value *left, Value *right)
{
	Operation *op = add_operation(parser, kind, type, 2);
	op->operands[0] = left;
	op->operands[1] = right;
	return &op->base;
}

static void
block_add_pred(Block *block, Block *pred)
{
	assert(VK(block) == VK_BLOCK);
	assert(VK(pred) == VK_BLOCK);
	if (block->pred_cnt_ == block->pred_cap_) {
		block->pred_cap_ = block->pred_cap_ ? block->pred_cap_ * 2 : 4;
		GROW_ARRAY(block->preds_, block->pred_cap_);
	}
	block->preds_[block->pred_cnt_++] = pred;
}

static void
block_add_pred_to_succs(Block *block)
{
	FOR_EACH_BLOCK_SUCC(block, succ) {
		block_add_pred(*succ, block);
	}
}

static void
switch_to_block(Parser *parser, Block *new_block)
{
	if (parser->current_block) {
		assert(value_is_terminator(parser->current_block->base.prev));
		block_add_pred_to_succs(parser->current_block);
	}
	parser->current_block = new_block;
}

static void
add_jump(Parser *parser, Block *destination, Block *new_block)
{
	add_unary(parser, VK_JUMP, &TYPE_VOID, &destination->base);
	switch_to_block(parser, new_block);
}

static void
add_cond_jump(Parser *parser, Value *cond, Block *true_block, Block *false_block, Block *new_block)
{
	Operation *op = add_operation(parser, VK_BRANCH, &TYPE_VOID, 3);
	op->operands[0] = cond;
	op->operands[1] = &true_block->base;
	op->operands[2] = &false_block->base;
	switch_to_block(parser, new_block);
}

static Value *
add_alloca(Parser *parser, Type *type)
{
	Alloca *alloca = arena_alloc(parser->arena, sizeof(*alloca));
	value_init(&alloca->base, VK_ALLOCA, type_pointer(parser->arena, type));
	append_to_block(parser->current_block, &alloca->base);
	alloca->size = type_size(type);
	alloca->optimizable = true;
	return &alloca->base;
}

static Value *
create_global(Parser *parser, Str name, Type *type)
{
	Global *global = arena_alloc(parser->arena, sizeof(*global));
	value_init(&global->base, VK_GLOBAL, type_pointer(parser->arena, type));
	global->name = name;
	global->init = NULL;

	global->base.index = garena_cnt(&parser->globals, Global *);
	garena_push_value(&parser->globals, Global *, global);

	return &global->base;
}

static Value *
add_argument(Parser *parser, Type *type, size_t index)
{
	Argument *arg = arena_alloc(parser->arena, sizeof(*arg));
	value_init(&arg->base, VK_ARGUMENT, type);
	append_to_block(parser->current_block, &arg->base);
	arg->index = index;
	return &arg->base;
}

static Value *
as_rvalue(Parser *parser, CValue cvalue)
{
	if (cvalue.lvalue) {
		Value *lvalue = cvalue.value;
		assert(lvalue->type->kind == TY_POINTER);
		Type *type = ((PointerType *) lvalue->type)->child;
		return add_unary(parser, VK_LOAD, type, lvalue);
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
		parser_error(parser, parser->lookahead, false, "%s", msg);
		return &NOP;
	}
}

static Type *struct_body(Parser *parser);

static Type *
type_specifier(Parser *parser)
{
	Type *type;
	Token token = discard(parser);
	switch (token.kind) {
	case TK_VOID: type = &TYPE_VOID; break;
	case TK_INT:  type = &TYPE_INT;  break;
	case TK_IDENTIFIER: {
		Str ident = prev_tok(parser).str;
		if (!table_get(&parser->type_env, ident, (void **) &type)) {
			parser_error(parser, token, false, "Type name '%.*s' not found", (int) ident.len, ident.str);
		}
		break;
	}
	case TK_STRUCT: {
		if (peek(parser) == TK_IDENTIFIER) {
			Str name = eat_identifier(parser);
			if (peek(parser) == TK_LBRACE) {
				type = struct_body(parser);
				Type *prev;
				if (table_get(&parser->type_env, name, (void **) &prev)) {
					// TODO: type compatible?
					UNREACHABLE();
				} else {
					table_insert(&parser->type_env, name, type);
				}
			} else {
				if (!table_get(&parser->type_env, name, (void **) &type) || type->kind != TY_STRUCT) {
					parser_error(parser, token, false, "Expected name to be defined as struct");
				}
			}
		} else {
			type = struct_body(parser);
		}
		break;
	}
	default:
		type = &TYPE_VOID;
		parser_error(parser, token, false, "Unexpected token %s in type specifier", tok_repr[token.kind]);
	}

	return type;
}

typedef enum {
	DECLARATOR_ORDINARY,
	DECLARATOR_ABSTRACT,
	DECLARATOR_MAYBE_ABSTRACT,
} DeclaratorKind;

// `name` is output parameter
static Type *
declarator(Parser *parser, Str *name, Type *type, DeclaratorKind kind)
{
	while (try_eat(parser, TK_ASTERISK)) {
		type = type_pointer(parser->arena, type);
	}

	switch (peek(parser)) {
	case TK_IDENTIFIER: {
		Str ident = eat_identifier(parser);
		if (kind == DECLARATOR_ABSTRACT) {
			parser_error(parser, parser->lookahead, false, "Abstract declarator has identifier");
		}
		if (name) {
			*name = ident;
		}
		break;
	}
	case TK_LPAREN:
		eat(parser, TK_LPAREN);
		if (kind != DECLARATOR_ORDINARY) {
			switch (peek(parser)) {
			case TK_ASTERISK:
			case TK_LPAREN:
			case TK_IDENTIFIER:
				break;
			default:
				goto function_declarator;
			}
		}
		declarator(parser, name, type, kind);
		eat(parser, TK_RPAREN);
		break;
	default:
		if (kind != DECLARATOR_ORDINARY) {
			parser_error(parser, parser->lookahead, true, "Unexpected token %s in declarator", tok_repr[parser->lookahead.kind]);
		}
	}

	for (;;) {
		switch (peek(parser)) {
		case TK_LBRACKET: {
			eat(parser, TK_LBRACKET);
			// TODO
			UNREACHABLE();
			eat(parser, TK_RBRACKET);
			break;
		function_declarator:
		case TK_LPAREN: {
			eat(parser, TK_LPAREN);
			size_t start = garena_save(parser->scratch);
			while (!try_eat(parser, TK_RPAREN)) {
				Type *type_spec = type_specifier(parser);
				Str param_name;
				Type *param_type = declarator(parser, &param_name, type_spec, DECLARATOR_MAYBE_ABSTRACT);
				Parameter param = { param_name, param_type };
				garena_push_value(parser->scratch, Parameter, param);
				if (!try_eat(parser, TK_COMMA)) {
					eat(parser, TK_RPAREN);
					break;
				}
			}
			size_t param_cnt = garena_cnt_from(parser->scratch, start, Parameter);
			Parameter *params = move_to_arena(parser->arena, parser->scratch, start, Parameter);
			type = type_function(parser->arena, type, params, param_cnt);
			break;
		}
		default:
			return type;
		}
		}
	}
}

static Type *
struct_body(Parser *parser)
{
	eat(parser, TK_LBRACE);
	size_t start = garena_save(parser->scratch);
	while (!try_eat(parser, TK_RBRACE)) {
		Type *type_spec = type_specifier(parser);
		Str field_name;
		Type *field_type = declarator(parser, &field_name, type_spec, DECLARATOR_ORDINARY);

		Field field = {
			.name = field_name,
			.type = field_type,
		};
		garena_push_value(parser->scratch, Field, field);
		eat(parser, TK_SEMICOLON);
	}
	size_t field_cnt = garena_cnt_from(parser->scratch, start, Field);
	Field *fields = move_to_arena(parser->arena, parser->scratch, start, Field);
	Type *struct_type = type_struct(parser->arena, fields, field_cnt);
	return struct_type;
}

static Type *
type_name(Parser *parser)
{
	Type *type = type_specifier(parser);
	return declarator(parser, NULL, type, DECLARATOR_ABSTRACT);
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
	// TODO: can parent really be NULL?
	value_init(&k->base, VK_CONSTANT, &TYPE_INT);
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
	Str ident = eat_identifier(parser);
	Value *value = NULL;
	if (!env_lookup(&parser->env, ident, (void **) &value)) {
		parser_error(parser, prev_tok(parser), false, "Name '%.*s' not found", (int) ident.len, ident.str);
		return rvalue(&NOP);
	}
	assert(value);
	if (value->kind == VK_FUNCTION) {
	     return rvalue(value);
	}
	return lvalue(value);
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
	eat(parser, TK_CAST);
	eat(parser, TK_LESS);
	Type *new_type = type_name(parser);
	eat(parser, TK_GREATER);
	eat(parser, TK_LPAREN);
	CValue cvalue = expression(parser);
	Value *value = as_rvalue(parser, cvalue);
	eat(parser, TK_RPAREN);
	if (new_type == &TYPE_VOID) {
		// TODO
		UNREACHABLE();
	}
	if (new_type->kind == TY_POINTER && value->type->kind == TY_POINTER) {
		value->type = new_type;
	}
	return rvalue(value);
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
		result = add_unary(parser, VK_NEG, &TYPE_INT, arg);
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
	return rvalue(add_binary(parser, VK_NEQ, &TYPE_INT, arg, zero));
}

static CValue
bitnot(Parser *parser)
{
	eat(parser, TK_TILDE);
	CValue carg = expression_bp(parser, 14);
	Value *arg = as_rvalue(parser, carg);
	return rvalue(add_unary(parser, VK_NOT, &TYPE_INT, arg));
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
	return rvalue(add_binary(parser, kind, &TYPE_INT, left, right));
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
	return rvalue(add_binary(parser, kind, &TYPE_INT, left, right));
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
	return rvalue(add_binary(parser, kind, &TYPE_INT, left, right));
}

static CValue
indexing(Parser *parser, CValue cleft, int rbp)
{
	(void) rbp;
	eat(parser, TK_LBRACKET);
	CValue cright = expression(parser);
	eat(parser, TK_RBRACKET);
	Value *left = as_rvalue(parser, cleft);
	if (left->type->kind != TY_POINTER) {
		parser_error(parser, parser->lookahead, false, "Expected indexing to subscript a pointer");
	}
	Value *right = as_rvalue(parser, cright);
	return lvalue(add_binary(parser, VK_GET_INDEX_PTR, left->type, left, right));
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
	Operation *call = add_operation(parser, VK_CALL, fun_type->ret_type, 1 + argument_cnt);

	size_t i = 0;
	call->operands[i++] = left;
	while (!try_eat(parser, TK_RPAREN)) {
		CValue carg = expression_no_comma(parser);
		if (i - 1 < argument_cnt) {
			call->operands[i] = as_rvalue(parser, carg);
			if (call->operands[i]->type != fun_type->params[i - 1].type) {
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
	(void) rbp;
	bool direct = discard(parser).kind == TK_DOT;
	Str name = eat_identifier(parser);
	Value *left;
	if (direct) {
		left = as_lvalue(parser, cleft, "TODO: '.' on non-lvalues");
	} else {
		left = as_rvalue(parser, cleft);
	}
	Type *struct_type = left->type;
	if (struct_type->kind != TY_POINTER) {
		parser_error(parser, parser->lookahead, false, "Member access with '->' on non-pointer");
		return lvalue(&NOP);
	}
	struct_type = ((PointerType *) struct_type)->child;
	if (struct_type->kind != TY_STRUCT) {
		parser_error(parser, parser->lookahead, false, "Member access on non-struct");
	}
	StructType *type = (void *) struct_type;
	Type *field_type;
	size_t i;
	for (i = 0; i < type->field_cnt; i++) {
		if (str_eq(name, type->fields[i].name)) {
			field_type = type->fields[i].type;
			goto found;
		}
	}
	parser_error(parser, parser->lookahead, false, "Field %.*s not found", (int) name.len, name.str);
found:;
	field_type = type_pointer(parser->arena, field_type);
	Value *member_index = create_const(parser, i);
	Value *member_access = add_binary(parser, VK_GET_MEMBER_PTR, field_type, left, member_index);
	return lvalue(member_access);
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
	Token equal = eat(parser, TK_EQUAL);
	CValue cright = expression_bp(parser, rbp);
	Value *left = as_lvalue(parser, cleft, "Expected lvalue on left hand side of assignment");
	Value *right = as_rvalue(parser, cright);
	if (!types_compatible(pointer_child(left->type), right->type)) {
		parser_error(parser, equal, false, "Assigned value has incorrect type");
	}
	add_binary(parser, VK_STORE, right->type, left, right);
	return lvalue(left);
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
	case TK_LBRACE: {
		eat(parser, TK_LBRACE);
		env_push(&parser->env);
		statements(parser);
		env_pop(&parser->env);
		break;
	}
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
	case TK_SWITCH: {
		UNREACHABLE();
		break;
	}
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
		eat(parser, TK_LPAREN);
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
			add_unary(parser, VK_RET, return_type, value);
		} else if (return_type == &TYPE_VOID) {
			add_operation(parser, VK_RETVOID, &TYPE_VOID, 0);
		} else {
			parser_error(parser, tok, false, "Expected some value to be 'return'ed");
		}
		// Following code is unreachable. Let's add it by unsetting
		// the current block.
		switch_to_block(parser, NULL);
		eat(parser, TK_SEMICOLON);
		break;
	}
	case TK_SEMICOLON: {
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
compute_preorder(Function *function)
{
	GROW_ARRAY(function->post_order, function->block_cap);
	function->block_cnt = 0;
	dfs(function->entry, &function->block_cnt, function->post_order);
	for (size_t b = function->block_cnt, i = 0; b--; i++) {
		function->post_order[b]->base.visited = 0;
	}
}

static void
function_declaration(Parser *parser, Str fun_name, FunctionType *fun_type)
{
	Parameter *params = fun_type->params;
	size_t param_cnt = fun_type->param_cnt;

	Function *function = arena_alloc(parser->arena, sizeof(*function));
	*function = (Function) {0};
	function->name = fun_name;
	value_init(&function->base, VK_FUNCTION, (Type *) fun_type);
	env_define(&parser->env, fun_name, &function->base);
	eat(parser, TK_LBRACE);
	parser->current_function = function;
	function->block_cnt = 0;
	function->entry = add_block(parser);
	// Can't use `switch_to_block` here, because this is the first block and
	// we have to get the thing going somehow.
	parser->current_block = function->entry;
	env_push(&parser->env);
	Value **args = calloc(param_cnt, sizeof(args[0]));
	for (size_t i = 0; i < param_cnt; i++) {
		args[i] = add_argument(parser, params[i].type, i);
	}
	for (size_t i = 0; i < param_cnt; i++) {
		Value *arg = args[i];
		Value *addr = add_alloca(parser, params[i].type);
		add_binary(parser, VK_STORE, params[i].type, addr, arg);
		env_define(&parser->env, params[i].name, addr);
	}
	free(args);
	statements(parser);
	compute_preorder(function);
	function->base.index = garena_cnt(&parser->functions, Function *);
	garena_push_value(&parser->functions, Function *, function);
	env_pop(&parser->env);
	parser->current_function = NULL;
}

static void
global_declaration(Parser *parser, Str name, Type *type)
{
	Value *addr = create_global(parser, name, type);
	Global *global = (Global *) addr;
	if (try_eat(parser, TK_EQUAL)) {
		global->init = as_rvalue(parser, literal(parser));
	}
	env_define(&parser->env, name, addr);
}

static void
variable_declaration(Parser *parser)
{
	Type *type_spec = type_specifier(parser);
	Str name;
	Type *type = declarator(parser, &name, type_spec, DECLARATOR_ORDINARY);
	assert(parser->current_function);
	Value *addr = add_alloca(parser, type);
	if (peek(parser) == TK_EQUAL) {
		assign(parser, lvalue(addr), 2);
	}
	env_define(&parser->env, name, addr);
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
	case TK_IDENTIFIER: {
		Str ident = curr_tok(parser).str;
		Type *type;
		if (!table_get(&parser->type_env, ident, (void **) &type)) {
			goto expression;
		}
	}
	// fallthrough
	case TK_VOID:
	case TK_INT:
	case TK_STRUCT:
		variable_declarations(parser);
		break;
	expression:
	default:
		expression(parser);
	}
}

static void
parse_program(Parser *parser)
{
	for (;;) {
		if (peek(parser) == TK_EOF) {
			break;
		}
		bool had_typedef = try_eat(parser, TK_TYPEDEF);
		Type *type_spec = type_specifier(parser);
		Str name;
		Type *type = declarator(parser, &name, type_spec, DECLARATOR_ORDINARY);
		if (had_typedef) {
			table_insert(&parser->type_env, name, type);
			eat(parser, TK_SEMICOLON);
		} else if (type->kind == TY_FUNCTION) {
			function_declaration(parser, name, (FunctionType *) type);
		} else {
			global_declaration(parser, name, type);
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

static Field *
get_member(Value *value)
{
	assert(value->kind == VK_GET_MEMBER_PTR);
	Operation *operation = (void*) value;
	PointerType *pointer_type = (void *) operation->operands[0]->type;
	assert(pointer_type->base.kind == TY_POINTER);
	StructType *struct_type = (void *) pointer_type->child;
	assert(struct_type->base.kind == TY_STRUCT);
	assert(operation->operands[1]->kind == VK_CONSTANT);
	size_t member_index = ((Constant *)operation->operands[1])->k;
	return &struct_type->fields[member_index];
}

size_t
instruction_arg_cnt(Value *value)
{
	switch (value->kind) {
	case VK_CALL: {
		Operation *op = (void *) value;
		return 1 + ((FunctionType *) op->operands[0]->type)->param_cnt;
	}
	case VK_PHI: {
		return block_pred_cnt(((Block *) value->parent));
	}
	default:
		return value_kind_param_cnt[value->kind];
	}
	UNREACHABLE();
}

void
for_each_operand(Value *value, void (*fun)(void *user_data, size_t i, Value **operand), void *user_data)
{
	size_t operand_cnt = instruction_arg_cnt(value);
	if (operand_cnt == 0) {
	     return;
	}
	Operation *op = (void *) value;
	for (size_t i = 0; i < operand_cnt; i++) {
		fun(user_data, i, &op->operands[i]);
	}
}

void
print_index(void *user_data, size_t i, Value **operand_)
{
	FILE *f = user_data;
	Value *operand = *operand_;
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
	case VK_GLOBAL: {
		Global *global = (void*) operand;
		print_str(f, global->name);
		break;
	}
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

void print_function(FILE *f, Function *function);
static void print_value(FILE *f, Value *v);

static void
dfs(Block *block, size_t *index, Block **post_order)
{
	//fprintf(stderr, "DFS at\n");
	////print_function(stderr, (Function *) block->base.parent);
	//for (Value *v = block->base.next; v != &block->base; v = v->next) {
	//	fprintf(stderr, "\tv%zu = ", v->index);
	//	print_value(stderr, v);
	//}
	assert(block->base.kind == VK_BLOCK);
	if (block->base.visited > 0) {
		return;
	}
	block->base.visited = 1;
	FOR_EACH_BLOCK_SUCC(block, succ) {
		dfs(*succ, index, post_order);
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
	/*
	InstDesc *desc = &inst_desc[inst->op];
	fprintf(f, "%s", desc->format);
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
	*/
}

void
print_mem(FILE *f, Inst *inst)
{
	fprintf(f, "[");
	if (IBASE(inst) == R_NONE) {
		fprintf(f, "global%"PRIi32, IDISP(inst));
	} else {
		print_reg(f, IBASE(inst));
		if (IINDEX(inst)) {
			fprintf(f, "+");
			if (ISCALE(inst) != 0) {
				fprintf(f, "%d*", 1 << ISCALE(inst));
			}
			print_reg(f, IINDEX(inst));
		}
		if (IDISP(inst)) {
			fprintf(f, "%+"PRIi32, IDISP(inst));
		}
	}
	fprintf(f, "]");
}

void
print_inst(FILE *f, Inst *inst)
{
	fprintf(f, "%s%s", ik_repr[IK(inst)], is_repr[IK(inst)][IS(inst)]);
	switch (inst->mode) {
	case M_Rr:
	case M_rr:
	case M_Cr:
		fprintf(f, " ");
		print_reg(f, IREG1(inst));
		fprintf(f, ", ");
		print_reg(f, IREG2(inst));
		break;
	case M_RM:
	case M_rM:
	case M_CM:
		fprintf(f, " ");
		print_reg(f, IREG(inst));
		fprintf(f, ", ");
		print_mem(f, inst);
		break;
	case M_Mr:
		fprintf(f, " ");
		print_mem(f, inst);
		fprintf(f, ", ");
		print_reg(f, IREG(inst));
		break;
	case M_RI:
	case M_rI:
	case M_CI:
		fprintf(f, " ");
		print_reg(f, IREG(inst));
		fprintf(f, ", ");
		fprintf(f, "%"PRIi32, IIMM(inst));
		break;
	case M_MI:
		fprintf(f, " ");
		fprintf(f, "qword ");
		print_mem(f, inst);
		fprintf(f, ", ");
		fprintf(f, "%"PRIi32, IIMM(inst));
		break;
	case M_CrI:
		fprintf(f, " ");
		print_reg(f, IREG1(inst));
		fprintf(f, ", ");
		print_reg(f, IREG2(inst));
		fprintf(f, "%"PRIi32, IIMM(inst));
		break;
	case M_CMI:
		fprintf(f, " ");
		print_reg(f, IREG(inst));
		fprintf(f, ", ");
		print_mem(f, inst);
		fprintf(f, "%"PRIi32, IIMM(inst));
		break;
	case M_R:
	case M_r:
	case M_C:
	case M_ADr:
		fprintf(f, " ");
		if (IK(inst) == IK_SETCC) {
			print_reg8(f, IREG(inst));
		} else {
			print_reg(f, IREG(inst));
		}
		break;
	case M_ADM:
	case M_M:
		fprintf(f, " ");
		print_mem(f, inst);
		break;
	case M_I:
		fprintf(f, " ");
		fprintf(f, "%"PRIi32, IIMM(inst));
		break;
	case M_L:
		fprintf(f, " ");
		fprintf(f, ".BB%"PRIi32, IIMM(inst));
		break;
	case M_NONE:
	case M_RET:
		switch (inst->kind) {
		case IK_FUNCTION: {
			fprintf(f, "function:");
			break;
		}
		case IK_BLOCK: {
			MBlock *block = container_of(inst, MBlock, insts);
			fprintf(f, ".BB%zu:", block->block->base.index);
			break;
		}
		default: break;
		}
		break;
	case M_CALL:
		fprintf(f, " ");
		fprintf(f, "function%"PRIi32, IIMM(inst));
		break;
	}
}


typedef struct {
	Arena *arena;
	MFunction *function;
	MBlock *block;
	size_t stack_space;
	Oper index;
	size_t block_cnt;
	size_t callee_saved_reg_start;
	Inst *make_stack_space;
} TranslationState;

Inst *
create_inst(Arena *arena, InstKind kind, int subkind)
{
	//InstDesc *desc = &inst_desc[op];
	//size_t operand_cnt = desc->label_cnt;
	//Inst *inst = arena_alloc(arena, sizeof(*inst) + operand_cnt * sizeof(inst->ops[0]));
	Inst *inst = arena_alloc(arena, sizeof(*inst) + 6 * sizeof(inst->ops[0]));
	inst->kind = kind;
	inst->subkind = subkind;
	memset(&inst->ops[0], 0, 6 * sizeof(inst->ops[0]));
	//for (size_t i = 0; i < 6; i++) {
	//	inst->ops[i] = va_arg(ap, Oper);
	//}
	return inst;
}

static void
add_inst_(TranslationState *ts, Inst *new)
{
	Inst *head = &ts->block->insts;
	Inst *last = head->prev;
	new->prev = last;
	new->next = head;
	last->next = new;
	head->prev = new;
}


static Inst *
add_inst(TranslationState *ts, InstKind kind, int subkind)
{
	Inst *new = create_inst(ts->arena, kind, subkind);
	add_inst_(ts, new);
	return new;
}

static void
add_copy(TranslationState *ts, Oper dest, Oper src)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV);
	inst->mode = M_Cr;
	IREG1(inst) = dest;
	IREG2(inst) = src;
}

static void
add_load(TranslationState *ts, Oper dest, Oper addr)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV);
	inst->mode = M_CM;
	IREG(inst) = dest;
	IBASE(inst) = addr;
}

static void
add_store(TranslationState *ts, Oper addr, Oper value)
{
	Inst *inst = add_inst(ts, IK_MOV, MOV);
	inst->mode = M_Mr;
	IREG(inst) = value;
	IBASE(inst) = addr;
}

static void
add_lea(TranslationState *ts, Oper dest, Oper base, Oper disp)
{
	Inst *inst = add_inst(ts, IK_MOV, LEA);
	inst->mode = M_CM;
	IREG(inst) = dest;
	IBASE(inst) = base;
	IDISP(inst) = disp;
}

static void
add_mov_imm(TranslationState *ts, Oper dest, u64 imm)
{
	// TODO: 64 bit immediates
	Inst *inst = add_inst(ts, IK_MOV, MOV);
	inst->mode = M_CI;
	IREG(inst) = dest;
	// truncated to bottom 32 bits
	IIMM(inst) = imm;
}

static void
add_set_zero(TranslationState *ts, Oper oper)
{
	// Set zero with `mov` so that we don't introduce additional constraints
	// on the register through XOR register uses.
	// TODO: xor oper, oper
	Inst *inst = add_inst(ts, IK_MOV, MOV);
	inst->mode = M_CI;
	IREG(inst) = oper;
	IIMM(inst) = 0;
}

static void
add_unop(TranslationState *ts, X86Group3 op, Oper op1)
{
	Inst *inst = add_inst(ts, IK_UNALU, op);
	inst->mode = M_R;
	IREG(inst) = op1;
}

static void
add_binop(TranslationState *ts, X86Group1 op, Oper op1, Oper op2)
{
	Inst *inst = add_inst(ts, IK_BINALU, op);
	inst->mode = M_Rr;
	IREG1(inst) = op1;
	IREG2(inst) = op2;
}

static void
add_cmp(TranslationState *ts, X86Group1 op, Oper op1, Oper op2)
{
	Inst *inst = add_inst(ts, IK_BINALU, op);
	inst->mode = M_rr;
	IREG1(inst) = op1;
	IREG2(inst) = op2;
}

static void
add_shift(TranslationState *ts, X86Group2 op, Oper op1, Oper op2)
{
	Inst *inst = add_inst(ts, IK_SHIFT, op);
	inst->mode = M_Rr;
	IREG1(inst) = op1;
	IREG2(inst) = op2;
	assert(op2 == R_RCX);
}

static void
add_push(TranslationState *ts, Oper oper)
{
	Inst *inst = add_inst(ts, IK_PUSH, 0);
	inst->mode = M_r;
	IREG(inst) = oper;
}

static void
add_pop(TranslationState *ts, Oper oper)
{
	Inst *inst = add_inst(ts, IK_POP, 0);
	inst->mode = M_C;
	IREG(inst) = oper;
}

static void
add_setcc(TranslationState *ts, CondCode cc, Oper oper)
{
	Inst *inst = add_inst(ts, IK_SETCC, cc);
	inst->mode = M_R; // partial register read
	IREG(inst) = oper;
}

static void
add_imul3(TranslationState *ts, Oper dest, Oper arg, Oper imm)
{
	Inst *inst = add_inst(ts, IK_IMUL3, 0);
	inst->mode = M_CrI;
	IREG(inst) = dest;
	IREG2(inst) = dest;
	IIMM(inst) = imm;
}

static void
add_jmp(TranslationState *ts, Oper block_index)
{
	Inst *inst = add_inst(ts, IK_JUMP, 0);
	inst->mode = M_L;
	IIMM(inst) = block_index;
}

static void
add_jcc(TranslationState *ts, CondCode cc, Oper block_index)
{
	Inst *inst = add_inst(ts, IK_JCC, cc);
	inst->mode = M_L;
	IIMM(inst) = block_index;
}

static void
add_call(TranslationState *ts, Oper function_index, Oper arg_cnt)
{
	Inst *inst = add_inst(ts, IK_CALL, 0);
	inst->mode = M_CALL;
	IIMM(inst) = function_index;
	IARG_CNT(inst) = arg_cnt;
}

static void
translate_call(TranslationState *ts, Oper res, Oper fun, Oper *args, size_t arg_cnt)
{
	assert(arg_cnt < ARRAY_LEN(argument_regs));
	for (size_t i = 0; i < arg_cnt; i++) {
		add_copy(ts, argument_regs[i], args[0]);
	}
	add_call(ts, fun, arg_cnt);
	add_copy(ts, res, R_RAX);
}

static void
translate_return(TranslationState *ts, Oper *ret_val)
{
	if (ret_val) {
		add_copy(ts, R_RAX, *ret_val);
	}
	// Restore callee saved registers. See prologue for more details.
	size_t callee_saved_reg = ts->callee_saved_reg_start;
	for (size_t i = 0; i < ARRAY_LEN(saved); i++) {
		add_copy(ts, saved[i], callee_saved_reg++);
	}
	add_copy(ts, R_RSP, R_RBP);
	add_pop(ts, R_RBP);
	// TODO: ret "reads" return value callee saved registers
	Inst *ret = add_inst(ts, IK_RET, 0); // TODO: subkind = calling convention?
	ret->mode = M_RET;
	if (ret_val) {
		// Make return instruction read the returned value.
		// NOTE: This has to be updated when multiple return registers
		// are needed.
		IREG(ret) = R_RAX;
	}

}

static void
translate_unop(TranslationState *ts, X86Group3 op, Oper res, Oper arg)
{
	add_copy(ts, res, op);
	add_unop(ts, op, res);
}

static void
translate_binop(TranslationState *ts, X86Group1 op, Oper res, Oper arg1, Oper arg2)
{
	add_copy(ts, res, arg1);
	add_binop(ts, op, res, arg2);
}

static void
translate_shift(TranslationState *ts, X86Group2 op, Oper res, Oper arg1, Oper arg2)
{
	add_copy(ts, res, arg1);
	add_copy(ts, R_RCX, arg2);
	add_shift(ts, op, res, R_RCX);
}

static void
translate_div(TranslationState *ts, Oper res, Oper arg1, Oper arg2, bool modulo)
{
	// TODO: cdq = sign extend RAX into RDX
	add_set_zero(ts, R_RDX);
	add_copy(ts, R_RAX, arg1);

	Inst *inst = add_inst(ts, IK_MULDIV, G3_IDIV);
	inst->mode = M_ADr;
	IREG(inst) = arg2;

	Oper result = modulo ? R_RDX : R_RAX;
	add_copy(ts, res, result);
}

static void
translate_cmpop(TranslationState *ts, CondCode cc, Oper res, Oper arg1, Oper arg2)
{
	// Zero out register first, so we don't change the flags before setcc.
	add_set_zero(ts, res);
	add_cmp(ts, G1_CMP, arg1, arg2);
	add_setcc(ts, cc, res);
}

typedef struct {
	TranslationState *ts;
	Oper opers[10];
} TranslateOperandState;

void
translate_operand(void *user_data, size_t i, Value **operand_)
{
	TranslateOperandState *tos = user_data;
	Oper res;
	Value *operand = *operand_;
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
	case VK_GLOBAL: {
		Global *global = (void*) operand;
		res = tos->ts->index++;
		add_lea(tos->ts, res, R_NONE, global->base.index);
		break;
	}
	case VK_CONSTANT: {
		Constant *k = (void*) operand;
		res = tos->ts->index++;
		add_mov_imm(tos->ts, res, k->k);
		break;
	}
	case VK_ALLOCA: {
		Alloca *alloca = (Alloca *) operand;
		res = tos->ts->index++;
		add_lea(tos->ts, res, R_RBP, - 8 - alloca->size);
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

static void print_value(FILE *f, Value *v);

void
translate_value(TranslationState *ts, Value *v)
{
	TranslateOperandState tos_;
	TranslateOperandState *tos = &tos_;
	tos->ts = ts;
	if (v->kind == VK_PHI) {
		// Don't translate phi nor its operands -- they are handled in
		// the predecessors.
		return;
	}
	for_each_operand(v, translate_operand, tos);
	Oper *ops = &tos->opers[0];
	//Oper res = ts->index++;
	Oper res = v->index;
	fprintf(stderr, "Translating: ");
	print_value(stderr, v);
	switch (v->kind) {
	case VK_NOP:
	case VK_UNDEFINED:
		break;
	case VK_IDENTITY:
		add_copy(ts, res, ops[0]);
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
		assert(argument->index < ARRAY_LEN(argument_regs));
		add_copy(ts, res, argument_regs[argument->index]);
		break;
	}
	case VK_CONSTANT:
	case VK_BLOCK:
	case VK_FUNCTION:
	case VK_GLOBAL:
		UNREACHABLE();
		break;

	case VK_ADD:
		translate_binop(ts, G1_ADD, res, ops[0], ops[1]);
		break;
	case VK_SUB:
		translate_binop(ts, G1_SUB, res, ops[0], ops[1]);
		break;
	case VK_MUL:
		translate_binop(ts, G1_IMUL, res, ops[0], ops[1]);
		break;
	case VK_DIV:
		translate_div(ts, res, ops[0], ops[1], false);
		break;
	case VK_MOD:
		translate_div(ts, res, ops[0], ops[1], true);
		break;
	case VK_AND:
		translate_binop(ts, G1_AND, res, ops[0], ops[1]);
		break;
	case VK_OR:
		translate_binop(ts, G1_OR, res, ops[0], ops[1]);
		break;
	case VK_SHL:
		translate_shift(ts, G2_SAL, res, ops[0], ops[1]);
		break;
	case VK_SHR:
		translate_shift(ts, G2_SAR, res, ops[0], ops[1]);
		break;
	case VK_NEG:
		translate_unop(ts, G3_NEG, res, ops[0]);
		break;
	case VK_NOT:
		translate_unop(ts, G3_NOT, res, ops[0]);
		break;
	case VK_EQ:
		translate_cmpop(ts, CC_Z, res, ops[0], ops[1]);
		break;
	case VK_NEQ:
		translate_cmpop(ts, CC_NZ, res, ops[0], ops[1]);
		break;
	case VK_LT:
		translate_cmpop(ts, CC_L, res, ops[0], ops[1]);
		break;
	case VK_LEQ:
		translate_cmpop(ts, CC_LE, res, ops[0], ops[1]);
		break;
	case VK_GT:
		translate_cmpop(ts, CC_G, res, ops[0], ops[1]);
		break;
	case VK_GEQ:
		translate_cmpop(ts, CC_GE, res, ops[0], ops[1]);
		break;

	case VK_LOAD:
		add_load(ts, res, ops[0]);
		break;
	case VK_STORE:
		add_store(ts, ops[0], ops[1]);
		break;
	case VK_GET_INDEX_PTR: {
		size_t size = type_size(pointer_child(v->type));
		Oper size_oper = ts->index++;
		add_imul3(ts, size_oper, ops[1], size);
		translate_binop(ts, G1_ADD, res, ops[0], size_oper);
		break;
	}
	case VK_GET_MEMBER_PTR: {
		Field *field = get_member(v);
		// A hack. Since ops[1] (the field index) already got
		// translated, let's change it to the field's offset.
		IIMM(ts->block->insts.prev) = field->offset;
		translate_binop(ts, G1_ADD, res, ops[0], ops[1]);
		break;
	}
	case VK_CALL: {
		Operation *call = (void *) v;
		// TODO: indirect calls
		Function *function = (Function *) call->operands[0];
		FunctionType *fun_type = (FunctionType *) function->base.type;
		translate_call(ts, res, ops[0], &ops[1], fun_type->param_cnt);
		break;
	}
	case VK_JUMP: {
		Block *current = ts->block->block;
		Block *succ = (Block *) ((Operation *) v)->operands[0];
		size_t pred_index;
		Block **succ_preds = block_preds(succ);
		size_t succ_pred_cnt = block_pred_cnt(succ);
		for (size_t i = 0; i < succ_pred_cnt; i++) {
			Block *pred = succ_preds[i];
			if (pred == current) {
				pred_index = i;
				goto found;
			}
		}
		UNREACHABLE();
	found:;
		size_t i = 0;
		for (Value *v = succ->base.next; v != &succ->base; v = v->next) {
			if (VK(v) != VK_PHI) {
				break;
			}
			Operation *phi = (void *) v;
			// TODO: save the phi operands somewhere else
			translate_operand(tos, 9, &phi->operands[pred_index]);
			add_copy(ts, ops[i++] = ts->index++, ops[9]);
		}
		i = 0;
		for (Value *v = succ->base.next; v != &succ->base; v = v->next) {
			if (VK(v) != VK_PHI) {
				break;
			}
			Operation *phi = (void *) v;
			add_copy(ts, VINDEX(phi), ops[i++]);
		}

		add_jmp(ts, succ->base.index);
		break;
	}
	case VK_BRANCH:
		add_cmp(ts, G1_TEST, ops[0], ops[0]);
		add_jcc(ts, CC_Z, ops[2]);
		add_jmp(ts, ops[1]);
		break;
	case VK_RET:
		translate_return(ts, &ops[0]);
		break;
	case VK_RETVOID:
		translate_return(ts, NULL);
		break;
	case VK_PHI: {
		// Nothing to do. We translate phis in jumps from predecessors.
		break;
	}
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
ig_destroy(InterferenceGraph *ig, size_t capacity)
{
	FREE_ARRAY(ig->matrix, capacity * capacity);
	for (size_t i = 0; i < capacity; i++) {
		garena_destroy(&ig->adj_list[i]);
	}
	FREE_ARRAY(ig->adj_list, capacity);
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

void
print_mfunction(FILE *f, MFunction *mfunction)
{
	fprintf(f, "function%zu:\n", mfunction->func->base.index);
	print_str(f, mfunction->func->name);
	fprintf(f, ":\n");
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		fprintf(f, ".BB%zu:", mblock->block->base.index);
		for (Inst *inst = mblock->insts.next; inst != &mblock->insts; inst = inst->next) {
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
		wl_grow(&ras->block_work_list, ras->block_capacity);
		GROW_ARRAY(ras->live_in, ras->block_capacity);
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
		ZERO_ARRAY(&ras->move_list[old_vreg_capacity], ras->vreg_capacity - old_vreg_capacity);
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
	FREE_ARRAY(ras->reg_assignment, ras->vreg_capacity);
	FREE_ARRAY(ras->to_spill, ras->vreg_capacity);
	FREE_ARRAY(ras->alias, ras->vreg_capacity);
	FREE_ARRAY(ras->def_counts, ras->vreg_capacity);
	FREE_ARRAY(ras->use_counts, ras->vreg_capacity);
	FREE_ARRAY(ras->degree, ras->vreg_capacity);
	ig_destroy(&ras->ig, ras->vreg_capacity);
	wl_destroy(&ras->live_set);
	wl_destroy(&ras->block_work_list);
	for (size_t i = 0; i < ras->block_capacity; i++) {
		wl_destroy(&ras->live_in[i]);
	}
	FREE_ARRAY(ras->live_in, ras->block_capacity);
	wl_destroy(&ras->spill_wl);
	wl_destroy(&ras->freeze_wl);
	wl_destroy(&ras->simplify_wl);
	wl_destroy(&ras->moves_wl);
	wl_destroy(&ras->active_moves_wl);
	wl_destroy(&ras->stack);
	garena_destroy(&ras->gmoves);
	for (size_t i = 0; i < ras->vreg_capacity; i++) {
		garena_destroy(&ras->move_list[i]);
	}
	FREE_ARRAY(ras->move_list, ras->vreg_capacity);
}

void
reg_alloc_state_init_for_function(RegAllocState *ras, MFunction *mfunction)
{
	ras->mfunction = mfunction;
	//reg_alloc_state_reset(ras);
}

bool
is_alias(RegAllocState *ras, Oper u)
{
	return ras->alias[u] != u;
}

Oper
get_alias(RegAllocState *ras, Oper u)
{
	while (u != ras->alias[u]) {
		u = ras->alias[u];
	}
	return u;
}

void
ig_add(InterferenceGraph *ig, Oper op1, Oper op2)
{
	assert(op1 < ig->n);
	assert(op2 < ig->n);
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
	FOR_EACH_BLOCK_SUCC(block, succ) {
		wl_union(live_set, &ras->live_in[(*succ)->mblock->index]);
	}
}


void
for_each_def(Inst *inst, void (*fun)(void *user_data, Oper *def), void *user_data)
{
	InsFormat *mode = &formats[inst->mode];
	for (size_t i = mode->def_start; i < mode->def_end; i++) {
		fun(user_data, &inst->ops[i]);
	}
	for (Oper *def = mode->extra_defs; *def != R_NONE; def++) {
		fun(user_data, def);
	}
}

void
for_each_use(Inst *inst, void (*fun)(void *user_data, Oper *use), void *user_data)
{
	InsFormat *mode = &formats[inst->mode];
	for (size_t i = mode->use_start; i < mode->use_end; i++) {
		fun(user_data, &inst->ops[i]);
	}
	if (mode->use_cnt_given_by_first) {
		size_t use_cnt = inst->ops[0];
		for (size_t i = 0; i < use_cnt; i++) {
			fun(user_data, &mode->extra_uses[i]);
		}
	} else {
		for (Oper *use = mode->extra_uses; *use != R_NONE; use++) {
			fun(user_data, use);
		}
	}
}

void
remove_from_set(void *user_data, Oper *oper)
{
	WorkList *live_set = user_data;
	//fprintf(stderr, "Removing from live ");
	//print_reg(stderr, *oper);
	//fprintf(stderr, "\n");
	wl_remove(live_set, *oper);
}

void
add_to_set(void *user_data, Oper *oper)
{
	WorkList *live_set = user_data;
	//fprintf(stderr, "Adding to live ");
	//print_reg(stderr, *oper);
	//fprintf(stderr, "\n");
	wl_add(live_set, *oper);
}

void
live_step(WorkList *live_set, Inst *inst)
{
	//fprintf(stderr, "Live step at\t");
	//print_inst(stderr, inst);
	//fprintf(stderr, "\n");
	// Remove definitions from live.
	for_each_def(inst, remove_from_set, live_set);
	// Add uses to live.
	for_each_use(inst, add_to_set, live_set);
}

typedef struct {
	InterferenceGraph *ig;
	Oper live;
} InterferenceState;

void
add_interference_with(void *user_data, Oper *oper)
{
	InterferenceState *is = user_data;
	ig_add(is->ig, *oper, is->live);
}

void
interference_step(RegAllocState *ras, WorkList *live_set, Inst *inst)
{
	InterferenceGraph *ig = &ras->ig;

	// Special handling of moves:
	// 1) We don't want to introduce interference between move source and
	//    destination.
	// 2) We want to note all moves and for all nodes the moves they are
	//    contained in, because we want to try to coalesce the moves later.
	if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Cr) {
		// Remove uses from live to prevent interference between move
		// destination and source.
		for_each_use(inst, remove_from_set, live_set);

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
	for_each_def(inst, add_to_set, live_set);

	// Add interferences of all definitions with all live.
	InterferenceState is = { .ig = ig };
	FOR_EACH_WL_INDEX(live_set, j) {
		is.live = live_set->dense[j];
		for_each_def(inst, add_interference_with, &is);
	}
}

typedef struct {
	RegAllocState *ras;
	Inst *inst;
	Oper spill_start;
} SpillState;

bool
is_to_be_spilled(SpillState *ss, Oper t)
{
	// Newly introduced temporaries (>= `ss->spill_start`) are:
	// 1) Not spilled.
	// 2) Out of bounds for `to_spill`.
	// So it is important the we check that first.
	return t < ss->spill_start && ss->ras->to_spill[t];
}

void
insert_loads_of_spilled(void *user_data, Oper *src)
{
	SpillState *ss = user_data;
	RegAllocState *ras = ss->ras;
	if (!is_to_be_spilled(ss, *src)) {
		return;
	}
	Inst *inst = ss->inst;

	Oper temp = ras->mfunction->vreg_cnt++;
	fprintf(stderr, "load ");
	print_reg(stderr, *src);
	fprintf(stderr, " through ");
	print_reg(stderr, temp);
	Inst *load = create_inst(ras->arena, IK_MOV, MOV);
	//Inst *load = make_inst(ras->arena, OP_MOV_RMC, temp, R_RBP, 8 + ras->to_spill[src]);
	load->mode = M_CM;
	load->prev = inst->prev;
	load->next = inst;
	IREG(load) = temp;
	IBASE(load) = R_RBP;
	IDISP(load) = - 8 - ras->to_spill[*src];

	inst->prev->next = load;
	inst->prev = load;

	*src = temp;

	// No longer needed
	//ras->to_spill[temp] = ras->to_spill[src];
	//for (size_t j = 0; j < desc->dest_cnt; j++) {
	//	if (inst->ops[j] == src) {
	//		inst->ops[j] = temp;
	//	}
	//}
}

void
insert_stores_of_spilled(void *user_data, Oper *dest)
{
	SpillState *ss = user_data;
	RegAllocState *ras = ss->ras;
	if (!is_to_be_spilled(ss, *dest)) {
		return;
	}
	Inst *inst = ss->inst;

	Oper temp = ras->mfunction->vreg_cnt++;
	fprintf(stderr, "store ");
	print_reg(stderr, *dest);
	fprintf(stderr, " through ");
	print_reg(stderr, temp);
	fprintf(stderr, "\n");
	// NOTE: Three address code would need something different

	//Inst *store = make_inst(ras->arena, OP_MOV_MCR, R_RBP, temp, 8 + ras->to_spill[dest]);
	Inst *store = create_inst(ras->arena, IK_MOV, MOV);
	store->mode = M_Mr;
	store->prev = inst;
	store->next = inst->next;
	IREG(store) = temp;
	IBASE(store) = R_RBP;
	IDISP(store) = - 8 - ras->to_spill[*dest];

	inst->next->prev = store;
	inst->next = store;
	inst = inst->next;

	*dest = temp;
}

void
spill(RegAllocState *ras)
{
	// TODO: Infinite spill costs for uses immediately following
	// definitions.
	MFunction *mfunction = ras->mfunction;
	SpillState ss_ = {
		.ras = ras,
		.spill_start = mfunction->vreg_cnt,
	}, *ss = &ss_;
	print_mfunction(stderr, mfunction);
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		for (Inst *inst = mblock->insts.next; inst != &mblock->insts; inst = inst->next) {
			ss->inst = inst;
			fprintf(stderr, "\n");
			print_inst(stderr, inst);
			fprintf(stderr, "\n");
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Cr) {
				Oper dest = inst->ops[0];
				Oper src = inst->ops[1];
				bool spill_dest = is_to_be_spilled(ss, dest);
				bool spill_src = is_to_be_spilled(ss, src);
				if (spill_dest && spill_src) {
					// If this would be essentially:
					//    mov [rbp+X], [rbp+X]
					// we can just get rid of the copy.
					assert(false);
					if (ras->to_spill[dest] == ras->to_spill[src]) {
						inst->prev->next = inst->next;
						inst->next->prev = inst->prev;
					}
				} else if (spill_dest) {
					inst->mode = M_Mr;
					IREG(inst) = src;
					IBASE(inst) = R_RBP;
					IDISP(inst) = - 8 - ras->to_spill[dest];
				} else if (spill_src) {
					inst->mode = M_CM;
					IREG(inst) = dest;
					IBASE(inst) = R_RBP;
					IDISP(inst) = - 8 - ras->to_spill[src];
				}
				continue;
			}
			//print_inst_d(stderr, inst);
			//fprintf(stderr, "\n");
			// Add loads for all spilled uses.
			for_each_use(inst, insert_loads_of_spilled, ss);
			// Add stores for all spilled defs.
			for_each_def(inst, insert_stores_of_spilled, ss);
		}
	}
	print_mfunction(stderr, mfunction);
}

void
apply_reg_assignment(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		for (Inst *inst = mblock->insts.next; inst != &mblock->insts; inst = inst->next) {
			// TODO: different number of register slots per target
			// TODO: store number of registers in mode
			InsFormat *mode = &formats[inst->mode];
			size_t end = mode->use_end > mode->def_end ? mode->use_end : mode->def_end;
			for (size_t i = 0; i < end; i++) {
				assert(inst->ops[i] >= 0);
				inst->ops[i] = ras->reg_assignment[get_alias(ras, inst->ops[i])];
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
		for (Value *v = block->base.next; v != &block->base; v = v->next) {
			//for_each_operand(v, number_operand, &i);
			v->index = i++;
		}
	}
	function->value_cnt = i;
	return i;
}

static void
print_value(FILE *f, Value *v)
{
	switch (v->kind) {
	case VK_CONSTANT: {
		Constant *k = (void*) v;
		fprintf(f, "%"PRIi64, k->k);
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
	case VK_GET_MEMBER_PTR: {
		Operation *operation = (void*) v;
		fprintf(f, "get_member_ptr ");
		print_index(f, 0, &operation->operands[0]);
		Field *field = get_member(v);
		fprintf(f, " %.*s\n", (int) field->name.len, field->name.str);
		break;
	}
	default: {
		fprintf(f, "%s ", value_kind_repr[v->kind]);
		for_each_operand(v, print_index, f);
		fprintf(f, "\n");
		break;
	}
	}
}

void
print_function(FILE *f, Function *function)
{
	print_str(f, function->name);
	fprintf(f, ":\n");
	//for (size_t i = function->block_cnt; i--;) {
	for (size_t j = function->block_cnt; j--;) {
		Block *block = function->post_order[j];
		Block **preds = block_preds(block);
		size_t pred_cnt = block_pred_cnt(block);
		fprintf(f, "block%zu: ", block->base.index);
		for (size_t p = 0; p < pred_cnt; p++) {
			Block *pred = preds[p];
			if (p != 0) {
				fprintf(f, ", ");
			}
			fprintf(f, "block%zu", pred->base.index);
		}
		fprintf(f, "\n");

		for (Value *v = block->base.next; v != &block->base; v = v->next) {
			fprintf(f, "\tv%zu = ", v->index);
			print_value(f, v);
		}
	}
}

typedef struct {
	size_t function_cnt;
	Function **functions;
	size_t global_cnt;
	Global **globals;
} Module;


void
print_globals(FILE *f, Module *module)
{
	for (size_t i = 0; i < module->global_cnt; i++) {
		Global *global = module->globals[i];
		print_str(f, global->name);
		if (global->init) {
			fprintf(f, " = ");
			print_value(f, global->init);
		}
		fprintf(f, "\n");
	}
}


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
		.env = {0},
	};
	discard(&parser);

	env_push(&parser.env);
	parse_program(&parser);
	env_pop(&parser.env);
	env_free(&parser.env);
	table_destroy(&parser.type_env);

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
	module->global_cnt = garena_cnt(&parser.globals, Global *);
	module->globals = move_to_arena(arena, &parser.globals, 0, Global *);
	for (size_t f = 0; f < module->function_cnt; f++) {
		//Function *function = module->functions[f];
		//print_function(function);
	}
	garena_destroy(&parser.functions);
	garena_destroy(&parser.globals);
	return module;
}

typedef struct {
	GArena *uses;
	Value *current;
} GetUsesState;

void
add_uses(void *user_data, size_t i, Value **operand_)
{
	GetUsesState *gus = user_data;
	Value *operand = *operand_;
	if (operand->index == 0) {
		return;
	}
	garena_push_value(&gus->uses[operand->index], Value *, gus->current);
}

void
get_uses(Function *function)
{
	GROW_ARRAY(function->uses, function->value_cnt);
	ZERO_ARRAY(function->uses, function->value_cnt);
	GetUsesState gus = {
		.uses = function->uses,
	};
	for (size_t b = 0; b < function->block_cnt; b++) {
		Block *block = function->post_order[b];
		for (Value *v = block->base.next; v != &block->base; v = v->next) {
			gus.current = v;
			for_each_operand(v, add_uses, &gus);
		}
	}
}

void
free_uses(Function *function)
{
	for (size_t i = 0; i < function->value_cnt; i++) {
		garena_destroy(&function->uses[i]);
	}
}

void
mem2reg(Function *function)
{
	Block *entry = function->entry;
	for (Value *v = entry->base.next; v != &entry->base; v = v->next) {
		if (v->kind != VK_ALLOCA) {
			continue;
		}
		Alloca *alloca = (void *) v;
		Value **uses = garena_array(&function->uses[v->index], Value *);
		size_t use_cnt = garena_cnt(&function->uses[v->index], Value *);
		print_value(stderr, v);
		for (size_t i = 0; i < use_cnt; i++) {
			Value *use = uses[i];
			if (VK(use) == VK_STORE && STORE_ADDR(use) == v) {
				continue;
			}
			if (VK(use) == VK_LOAD && LOAD_ADDR(use) == v) {
				continue;
			}
			alloca->optimizable = false;
		}
	}
}

bool
is_optimizable_alloca(Value *v)
{
	return VK(v) == VK_ALLOCA && ((Alloca *) v)->optimizable;
}

typedef struct {
	Arena *arena;
	Function *function;
	Value ***var_map;
	Value **canonical;
} ValueNumberingState;

Operation *
insert_phi(Arena *arena, Block *block, Type *type)
{
	Value *non_phi;
	for (non_phi = block->base.next; non_phi != &block->base; non_phi = non_phi->next) {
		if (VK(non_phi) != VK_PHI) {
			break;
		}
	}
	Operation *phi = arena_alloc(arena, sizeof(*phi) + sizeof(phi->operands[0]) * block_pred_cnt(block));
	value_init(&phi->base, VK_PHI, type);
	phi->base.index = ((Function *) block->base.parent)->value_cnt++;
	phi->base.parent = &block->base;
	prepend_value(non_phi, &phi->base);
	return phi;
}

Value *read_variable(ValueNumberingState *vns, Block *block, Value *variable);

void
add_phi_operands(ValueNumberingState *vns, Operation *phi, Block *block, Value *variable)
{
	size_t i = 0;
	FOR_EACH_BLOCK_PRED(block, pred) {
		phi->operands[i++] = read_variable(vns, *pred, variable);
	}
}

typedef struct {
	Operation *phi;
	Value *variable;
} IncompletePhi;

void
write_variable(ValueNumberingState *vns, Block *block, Value *variable, Value *value)
{
	fprintf(stderr, "Writing var %zu from block %zu with value %zu\n", VINDEX(variable), VINDEX(block), VINDEX(value));
	vns->var_map[VINDEX(block)][VINDEX(variable)] = value;
}

Value *
read_variable(ValueNumberingState *vns, Block *block, Value *variable)
{
	fprintf(stderr, "Reading var %zu from block %zu\n", VINDEX(variable), VINDEX(block));
	assert(!block->pending);
	Value *value = vns->var_map[VINDEX(block)][VINDEX(variable)];
	if (value) {
		fprintf(stderr, "Have locally %zu\n", VINDEX(value));
	} else if (block->filled_pred_cnt != block_pred_cnt(block)) {
		fprintf(stderr, "Not sealed\n");
		assert(block_pred_cnt(block) > 1);
                // Not all predecessors are filled yet. We only insert a phi,
                // but initialize it later, when sealing, because only then we
                // actually can read from all predecessors.
		IncompletePhi phi = {
			.phi = insert_phi(vns->arena, block, pointer_child(variable->type)),
			.variable = variable,
		};
		garena_push_value(&block->incomplete_phis, IncompletePhi, phi);
		value = &phi.phi->base;
	} else if (block_pred_cnt(block) == 1) {
		fprintf(stderr, "Single pred\n");
		Block *pred = block_preds(block)[0];
		value = read_variable(vns, pred, variable);
	} else {
		fprintf(stderr, "Merge\n");
		// We already filled all predecessors.
		block->pending = true;
		Operation *phi = insert_phi(vns->arena, block, pointer_child(variable->type));
		add_phi_operands(vns, phi, block, variable);
		block->pending = false;
		value = &phi->base;
	}
	// Memoize
	write_variable(vns, block, variable, value);
	return value;
}

void
prepend_value(Value *pos, Value *new)
{
	Value *prev = pos->prev;
	new->prev = prev;
	new->next = pos;
	prev->next = new;
	pos->prev = new;
}

void
remove_value(Value *v)
{
	v->prev->next = v->next;
	v->next->prev = v->prev;
}

void
canonicalize(void *user_data, size_t i, Value **operand)
{
	ValueNumberingState *vns = user_data;
	Value *canonical = vns->canonical[VINDEX(*operand)];
	if (canonical) {
		*operand = canonical;
	}
}

void
seal_block(ValueNumberingState *vns, Block *block)
{
	size_t incomplete_phi_cnt = garena_cnt(&block->incomplete_phis, IncompletePhi);
	IncompletePhi *incomplete_phis = garena_array(&block->incomplete_phis, IncompletePhi);
	for (size_t i = 0; i < incomplete_phi_cnt; i++) {
		IncompletePhi *inc = &incomplete_phis[i];
		add_phi_operands(vns, inc->phi, block, inc->variable);
	}
}

void
value_numbering(Arena *arena, Function *function)
{
	size_t block_cnt = function->block_cnt;
	size_t value_cnt = function->value_cnt;

	ValueNumberingState vns_ = {
		.arena = arena,
		.function = function,
	}, *vns = &vns_;

	GROW_ARRAY(vns->canonical, value_cnt);
	ZERO_ARRAY(vns->canonical, value_cnt);

	GROW_ARRAY(vns->var_map, function->block_cap);
	ZERO_ARRAY(vns->var_map, function->block_cap);
	for (size_t b = 0; b < block_cnt; b++) {
		Block *block = function->post_order[b];
		GROW_ARRAY(vns->var_map[VINDEX(block)], value_cnt);
		ZERO_ARRAY(vns->var_map[VINDEX(block)], value_cnt);
	}

	seal_block(vns, function->entry);

	for (size_t b = block_cnt; b--;) {
		Block *block = function->post_order[b];
		for (Value *v = block->base.next; v != &block->base; v = v->next) {
			switch (VK(v)) {
			case VK_ALLOCA:
				if (is_optimizable_alloca(v)) {
					remove_value(v);
				}
				continue;
			case VK_LOAD:
				if (is_optimizable_alloca(LOAD_ADDR(v))) {
					Value *val = read_variable(vns, block, LOAD_ADDR(v));
					vns->canonical[VINDEX(v)] = val;
					remove_value(v);
				}
				continue;
			case VK_STORE:
				if (is_optimizable_alloca(STORE_ADDR(v))) {
					write_variable(vns, block, STORE_ADDR(v), STORE_VALUE(v));
					remove_value(v);
				}
				continue;
			default:
				break;
			}
			for_each_operand(v, canonicalize, vns);
		}

		FOR_EACH_BLOCK_SUCC(block, succ) {
			if (++(*succ)->filled_pred_cnt == block_pred_cnt((*succ))) {
				seal_block(vns, (*succ));
			}
		}
	}
	FREE_ARRAY(vns->canonical, value_cnt);
	for (size_t b = 0; b < block_cnt; b++) {
		FREE_ARRAY(vns->var_map[b], value_cnt);
	}
	FREE_ARRAY(vns->var_map, block_cnt);
}

void
merge_simple_blocks(Arena *arena, Function *function)
{
	WorkList worklist = {0};
	size_t block_cap = 1;
	while (block_cap < function->block_cap) {
		block_cap *= 2;
	}
	wl_grow(&worklist, block_cap);
	for (size_t b = function->block_cnt; b--;) {
		Block *block = function->post_order[b];
		wl_add(&worklist, block->base.index);
	}
	Oper b;
	while (wl_take(&worklist, &b)) {
		Block *block = function->post_order[b];
		if (block_succ_cnt(block) != 1) {
			continue;
		}
		Block *succ = block_succs(block)[0];
		if (block_pred_cnt(succ) != 1) {
			continue;
		}
		// Block has one successor, and the successor has only one
		// predecessor. We can just merge the blocks together
		// and get rid of the jump.
		fprintf(stderr, "Merging block%zu with block%zu\n", block->base.index, succ->base.index);

		// Replace all references to `succ` in its successors, to point
		// to `block` instead.
		FOR_EACH_BLOCK_SUCC(succ, ssucc) {
			FOR_EACH_BLOCK_PRED(*ssucc, pred) {
				if (*pred == succ) {
					*pred = block;
					break;
				}
			}
		}

		// Successors of block are fixed up automatically, because they
		// are taken implicitly from the terminator instruction.

		// Remove the jump instruction from `block`.
		remove_value(block->base.prev);
		// Append `succ` to the `block`.
		block->base.prev->next = succ->base.next;
		succ->base.next->prev = block->base.prev;
		succ->base.prev->next = &block->base;
		block->base.prev = succ->base.prev;
		//prepend_value(&block->base, succ->base.next);
		// Remove the redundant and unwanted `succ` block header.
		//remove_value(&succ->base);

		wl_add(&worklist, b);
	}
	wl_destroy(&worklist);

	// Recompute function->post_order, since we invalidated it.
	compute_preorder(function);
}

void
thread_jumps(Arena *arena, Function *function)
{
	WorkList worklist = {0};
	size_t block_cap = 1;
	while (block_cap < function->block_cap) {
		block_cap *= 2;
	}
	wl_grow(&worklist, block_cap);
	for (size_t b = function->block_cnt; b--;) {
		Block *block = function->post_order[b];
		wl_add(&worklist, block->base.index);
	}
	Oper b;
	while (wl_take(&worklist, &b)) {
		Block *block = function->post_order[b];
		if (VK(block->base.next) != VK_JUMP) {
			continue;
		}
		Block *succ = block_succs(block)[0];
                // Block is empty and has only one successor. We can just
		// forward the jumps from predecessors to the successor.
                fprintf(stderr, "Threading block%zu to block%zu\n", block->base.index, succ->base.index);

                // Replace all references to `block` in its predecessors, to
                // point to `succ` instead.
		FOR_EACH_BLOCK_PRED(block, pred) {
			FOR_EACH_BLOCK_PRED(*pred, s) {
				if (*s == block) {
					*s = succ;
					break;
				}
			}
			wl_add(&worklist, (*pred)->base.index);
		}
	}
	wl_destroy(&worklist);

	// Recompute function->post_order, since we invalidated it.
	compute_preorder(function);
}

void
split_critical_edges(Arena *arena, Function *function)
{
	for (size_t b = function->block_cnt; b--;) {
		Block *succ = function->post_order[b];
		if (block_pred_cnt(succ) <= 1) {
			// OK.
			continue;
		}
		FOR_EACH_BLOCK_PRED(succ, pred_) {
			Block *pred = *pred_;
			if (block_succ_cnt(pred) <= 1) {
				// OK.
				continue;
			}
			// Otherwise we have a critical edge (from block to with
			// multiple successors to block with multiple
			// predecessors). We split it by introducing a new
			// block.
			fprintf(stderr, "Splitting critical edge from block%zu to block%zu\n", VINDEX(pred), VINDEX(succ));
			Block *new = create_block(arena, function);
			Value *jump = create_unary(arena, new, VK_JUMP, &TYPE_VOID, &succ->base);
			jump->index = function->value_cnt++;
			prepend_value(&new->base, jump);
			FOR_EACH_BLOCK_SUCC(pred, s) {
				if (*s == succ) {
					*s = new;
				}
			}
		}
	}

	// Recompute function->post_order, since we invalidated it.
	compute_preorder(function);
}

typedef struct {
	Block *block;
	Value *value;
} PendingPhi;

void
single_exit(Arena *arena, Function *function)
{
	GArena gphis = {0};
	for (size_t b = function->block_cnt; b--;) {
		Block *block = function->post_order[b];
		Value *value = NULL;
		switch (VK(block->base.prev)) {
		case VK_RET:
			value = ((Operation *) block->base.prev)->operands[0];
			break;
		case VK_RETVOID:
			break;
		default:
			continue;
		}
		garena_push_value(&gphis, PendingPhi, ((PendingPhi) { .block = block, value = value }));
	}
	PendingPhi *phis = garena_array(&gphis, PendingPhi);
	size_t phi_cnt = garena_cnt(&gphis, PendingPhi);
	if (phi_cnt == 1) {
		garena_destroy(&gphis);
		return;
	}
	Block *ret_block = create_block(arena, function);

	bool ret_void = VK(phis[0].block->base.prev) == VK_RETVOID;

	for (size_t i = 0; i < phi_cnt; i++) {
		PendingPhi *phi = &phis[i];
		Block *pred = phi->block;
		Value *jump = create_unary(arena, pred, VK_JUMP, &TYPE_VOID, &ret_block->base);
		jump->index = function->value_cnt++;
		remove_value(pred->base.prev);
		prepend_value(&pred->base, jump);
		block_add_pred(ret_block, pred);
	}

	Value *ret_inst;
	if (ret_void) {
		ret_inst = &create_operation(arena, ret_block, VK_RETVOID, &TYPE_VOID, 0)->base;
	} else {
		Type *type = phis[0].value->type;
		Operation *phi = insert_phi(arena, ret_block, type);
		phi->base.index = function->value_cnt++;
		prepend_value(&ret_block->base, &phi->base);
		for (size_t i = 0; i < phi_cnt; i++) {
			Value *val = phis[i].value;
			phi->operands[i] = val;
		}
		ret_inst = create_unary(arena, ret_block, VK_RET, &TYPE_VOID, &phi->base);
	}
	ret_inst->index = function->value_cnt++;
	prepend_value(&ret_block->base, ret_inst);

	garena_destroy(&gphis);

	// Recompute function->post_order, since we invalidated it.
	compute_preorder(function);
}

void
add_to_use_or_def_count(void *user_data, Oper *oper)
{
	u8 *counts = user_data;
	counts[*oper]++;
}

void
calculate_spill_cost(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		for (Inst *inst = mblock->insts.next; inst != &mblock->insts; inst = inst->next) {
			for_each_def(inst, add_to_use_or_def_count, ras->def_counts);
			for_each_use(inst, add_to_use_or_def_count, ras->use_counts);
		}
	}
}

MFunction *
translate_function(Arena *arena, Function *function)
{
	Block **post_order = function->post_order;

	MFunction *mfunction = arena_alloc(arena, sizeof(*mfunction));
	memset(mfunction, 0, sizeof(*mfunction));
	mfunction->func = function;
	mfunction->mblocks = arena_alloc(arena, function->block_cnt * sizeof(mfunction->mblocks[0]));
	mfunction->mblock_cnt = 0; // incremented when each block is inserted

	TranslationState ts_ = {
		.arena = arena,
		.index = function->value_cnt,
		.stack_space = 8,
		.block = NULL,
		.function = mfunction,
	};
	TranslationState *ts = &ts_;


	for (size_t b = function->block_cnt; b--;) {
	//for (size_t j = 0; j < function->block_cnt; j++) {
		Block *block = post_order[b];
		//printf(".L%zu:\n", function->block_cnt - b - 1);
		MBlock *mblock = arena_alloc(arena, sizeof(*mblock));
		memset(mblock, 0, sizeof(*mblock));
		mfunction->mblocks[mfunction->mblock_cnt++] = mblock;
		mblock->insts.kind = IK_BLOCK;
		mblock->insts.subkind = 0;
		mblock->insts.mode = M_NONE;
		mblock->insts.next = &mblock->insts;
		mblock->insts.prev = &mblock->insts;
		mblock->block = block;
		//mblock->index = block->base.index;
		mblock->index = mfunction->mblock_cnt - 1;
		block->mblock = mblock;
		ts->block = mblock;
		if (block == function->entry) {
			add_push(ts, R_RBP);
			add_copy(ts, R_RBP, R_RSP);
			// Add instruction to make stack space, since we may
			// spill we don't know how much stack space to reserve
			// yet, we will replace the dummy '0' with proper stack
			// space requirement after register allocation.
			ts->make_stack_space = add_inst(ts, IK_BINALU, G1_SUB);
			Inst *inst = ts->make_stack_space;
			inst->mode = M_RI;
			IREG(inst) = R_RSP;
			IIMM(inst) = 0;

			// Save callee saved registers to temporaries. That way
			// the registers don't automatically intefere with
			// everything (since they will be "read" by the
			// return instruction). If it makes sense to use the
			// callee saved registers, they will be used, if
			// not, due to coalescing these temporaries will
			// likely be coalesced with the registers and
			// the copies eliminated.
			ts->callee_saved_reg_start = ts->index;
			for (size_t i = 0; i < ARRAY_LEN(saved); i++) {
				add_copy(ts, ts->index++, saved[i]);
			}
		}
		for (Value *v = block->base.next; v != &block->base; v = v->next) {
			translate_value(ts, v);
		}
	}

	mfunction->vreg_cnt = ts->index;
	mfunction->stack_space = ts->stack_space;
	mfunction->make_stack_space = ts->make_stack_space;
	function->mfunc = mfunction;
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
		MBlock *mblock = mfunction->mblocks[b];
		Block *block = mblock->block;
		get_live_out(ras, block, live_set);
		// process the block back to front, updating live_set in the
		// process
		for (Inst *inst = mblock->insts.prev; inst != &mblock->insts; inst = inst->prev) {
			live_step(live_set, inst);
		}
		if (!wl_eq(live_set, &ras->live_in[b])) {
			WorkList tmp = ras->live_in[b];
			ras->live_in[b] = *live_set;
			*live_set = tmp;
			FOR_EACH_BLOCK_PRED(block, pred) {
				wl_add(&ras->block_work_list, (*pred)->mblock->index);
			}
		}
	}


	for (b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		Block *block = mblock->block;
		get_live_out(ras, block, live_set);
		for (Inst *inst = mblock->insts.prev; inst != &mblock->insts; inst = inst->prev) {
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
		if (wl_has(&ras->stack, neighbour) || is_alias(ras, neighbour)) {
			continue;
		}
		fun(ras, neighbour);
	}
}

void
for_each_move(RegAllocState *ras, Oper u, void (*fun)(RegAllocState *ras, Oper u, Oper m, Inst *move))
{
	Inst **moves = garena_array(&ras->gmoves, Inst *);
	GArena *gmove_list = &ras->move_list[u];
	Oper *move_list = garena_array(gmove_list, Oper);
	size_t move_cnt = garena_cnt(gmove_list, Oper);
	for (size_t i = 0; i < move_cnt; i++) {
		Oper move_index = move_list[i];
		if (wl_has(&ras->active_moves_wl, move_index) || wl_has(&ras->moves_wl, move_index)) {
			fun(ras, u, move_index, moves[move_index]);
		}
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
enable_move(RegAllocState *ras, Oper u, Oper m, Inst *move)
{
	(void) u;
	if (wl_remove(&ras->active_moves_wl, m)) {
		fprintf(stderr, "Enabling move: \t");
		print_inst(stderr, move);
		fprintf(stderr, "\n");
		wl_add(&ras->moves_wl, m);
	}
}

void
enable_moves_for_one(RegAllocState *ras, Oper op)
{
	for_each_move(ras, op, enable_move);
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
		enable_moves_for_one(ras, op);
		for_each_adjacent(ras, op, enable_moves_for_one);
		wl_remove(&ras->spill_wl, op);
		if (is_move_related(ras, op)) {
			wl_add(&ras->freeze_wl, op);
		} else {
			wl_add(&ras->simplify_wl, op);
		}
	}
}

void
freeze_move(RegAllocState *ras, Oper u, Oper m, Inst *move)
{
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

void
freeze_moves(RegAllocState *ras, Oper u)
{
	fprintf(stderr, "Freezing moves of ");
	print_reg(stderr, u);
	fprintf(stderr, "\n");
	for_each_move(ras, u, freeze_move);
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
	}
}

void
select_potential_spill_if_needed(RegAllocState *ras)
{
	if (!wl_empty(&ras->spill_wl)) {
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
		if (wl_has(&ras->stack, t) || is_alias(ras, t)) {
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
		if (wl_has(&ras->stack, t) || is_alias(ras, t)) {
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
		if (wl_has(&ras->stack, t) || is_alias(ras, t)) {
			continue;
		}
		ig_add(&ras->ig, u, t);
		decrement_degree(ras, t);
	}
	if (ras->degree[u] > ras->reg_avail && wl_remove(&ras->freeze_wl, u)) {
		fprintf(stderr, "Move combined ");
		print_reg(stderr, u);
		fprintf(stderr, " from freeze to spill\n");
		wl_add(&ras->spill_wl, u);
	}
}

void
coalesce(RegAllocState *ras)
{
	Inst **moves = garena_array(&ras->gmoves, Inst *);
	Oper m;
	// TODO: Implications of making this a while?
	while (wl_take(&ras->moves_wl, &m)) {
		Inst *move = moves[m];
		fprintf(stderr, "Coalescing: \t");
		print_inst(stderr, move);
		fprintf(stderr, "\n");
		Oper u = get_alias(ras, move->ops[0]);
		Oper v = get_alias(ras, move->ops[1]);
		if (v < R__MAX) {
			Oper tmp = u;
			u = v;
			v = tmp;
		}
		if (u == v) {
			// already coalesced
			fprintf(stderr, "Already coalesced: \t");
			print_inst(stderr, move);
			fprintf(stderr, "\n");
			add_to_worklist(ras, u);
		} else if (v < R__MAX || ig_interfere(&ras->ig, u, v)) {
			// constrained
			fprintf(stderr, "Constrained: \t");
			print_inst(stderr, move);
			fprintf(stderr, "\n");
			add_to_worklist(ras, u);
			add_to_worklist(ras, v);
		} else if (are_coalesceble(ras, u, v)) {
			// coalesce
			combine(ras, u, v);
			add_to_worklist(ras, u);
		} else {
			fprintf(stderr, "Moving to active: \t");
			print_inst(stderr, move);
			fprintf(stderr, "\n");
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
			size_t neighbour = get_alias(ras, adj_list[j]);
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
		if (is_alias(ras, i)) {
			fprintf(stderr, "Coalesced ");
			print_reg(stderr, i);
			fprintf(stderr, " to ");
			print_reg(stderr, get_alias(ras, i));
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
		build_interference_graph(ras);
		calculate_spill_cost(ras);
		initialize_worklists(ras);
		for (;;) {
			simplify(ras);
			coalesce(ras);
			simplify(ras);
			freeze(ras);
			simplify(ras);
			select_potential_spill_if_needed(ras);

			if (wl_empty(&ras->simplify_wl) && wl_empty(&ras->spill_wl) && wl_empty(&ras->freeze_wl)) {
				break;
			}
		}

		if (assign_registers(ras)) {
			break;
		}
		spill(ras);
	}

	// Fixup stack space amount reserved at the start of the function
	IIMM(mfunction->make_stack_space) = mfunction->stack_space;
	apply_reg_assignment(ras);
}

void
peephole(MFunction *mfunction, Arena *arena)
{
	print_str(stderr, mfunction->func->name);
	fprintf(stderr, "\n");
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		Inst *inst = mblock->insts.next;
		while (inst != &mblock->insts) {
			print_inst(stderr, inst);
			fprintf(stderr, "\n");
			fflush(stderr);
			// mov rax, rax
			// =>
			// [deleted]
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Cr && IREG(inst) == IREG2(inst)) {
				inst->prev->next = inst->next;
				inst->next->prev = inst->prev;
				goto next;
			}

			// cmp rax, 0
			// =>
			// test rax, rax
			if (IK(inst) == IK_BINALU && IS(inst) == G1_CMP && IM(inst) == M_rI && IIMM(inst) == 0) {
				IS(inst) = G1_TEST;
				IM(inst) = M_rr;
				IREG2(inst) = IREG(inst);
				continue;
			}

			Inst *prev = inst->prev;
			if (!prev) {
				goto next;
			}

			//     jmp .BB5
			// .BB5:
			// =>
			// .BB5:
			if (IK(inst) == IK_BLOCK && IK(prev) == IK_JUMP && IIMM(prev) == container_of(inst, MBlock, insts)->block->base.index) {
				prev->prev->next = inst;
				inst->prev = prev->prev;
				inst = inst;
				continue;
			}

			// mov rax, 1
			// add rax, 2
			// =>
			// mov rax, 3
			if (IK(inst) == IK_BINALU && IM(inst) == M_RI && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && IREG(inst) == IREG(prev)) {
				Oper left = IIMM(prev);
				Oper right = IIMM(inst);
				Oper result;
				switch (IS(inst)) {
				case G1_ADD:  result = left + right; break;
				case G1_OR:   result = left | right; break;
				case G1_AND:  result = left & right; break;
				case G1_SUB:  result = left - right; break;
				case G1_XOR:  result = left ^ right; break;
				case G1_IMUL: result = left * right; break;
				default: goto skip;
				}
				IIMM(prev) = result;
				prev->next = inst->next;
				inst->next->prev = prev;
			skip:;
			}

			// mov rcx, 8
			// add rax, rcx
			// =>
			// add rax, 8
			if (IK(inst) == IK_BINALU && (IM(inst) == M_Rr || IM(inst) == M_rr) && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && IREG(prev) == IREG2(inst)) {
				inst->mode = IM(inst) == M_Rr ? M_RI : M_rI;
				IREG2(inst) = R_NONE;
				IIMM(inst) = IIMM(prev);
				inst->prev = prev->prev;
				prev->prev->next = inst;
				inst = inst;
				continue;
			}

			// Produces longer instruction stream, but deletes one
			// definition, so it may unlock other optimizations.
			// mov rax, 5
			// mov rcx, rax
			// =>
			// mov rax, 5
			// mov rcx, 5


			// mov rcx, 5
			// mov [rax], rcx
			// =>
			// mov [rax], 5
			if (IK(inst) == IK_MOV && IM(inst) == M_Mr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && IREG(prev) == IREG(inst)) {
				IM(inst) = M_MI;
				IIMM(inst) = IIMM(prev);
				inst->prev = prev->prev;
				prev->prev->next = inst;
				inst = inst;
				continue;
			}

			// lea rax, [rbp-16]
			// add rax, 8
			// =>
			// lea rax, [rbp-8]
			if (IK(inst) == IK_BINALU && IS(inst) == G1_ADD && IM(inst) == M_RI && IK(prev) == IK_MOV && IS(prev) == LEA && IREG(prev) == IREG(inst)) {
				IDISP(prev) += IIMM(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				prev->next = inst->next;
				inst = prev;
				continue;
			}

			// lea rax, [global0]
			// mov rcx, [rax]
			// =>
			// mov rcx, [global0]
			// TODO: this is incorrect if rax is used, should copy
			// rcx? what does that imply currently? should
			// we require a preceding use for every def to
			// check these? what does regalloc produce? does
			// SSA save us?
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_CM && IINDEX(inst) == R_NONE && ISCALE(inst) == 0 && IDISP(inst) == 0 && IK(prev) == IK_MOV && IS(prev) == LEA && IM(prev) == M_CM && IBASE(inst) == IREG(prev)) {
				IS(prev) = MOV;
				IREG(prev) = IREG(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// mov [global0], rcx
			// mov rax, [global0]
			// =>
			// mov [global0], rcx
			// mov rax, rcx
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_CM && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_Mr && IBASE(inst) == IBASE(prev) && IINDEX(inst) == IINDEX(prev) && ISCALE(inst) == ISCALE(prev) && IDISP(inst) == IDISP(prev)) {
				IM(inst) = M_Cr;
				IREG2(inst) = IREG(prev);
				inst = inst;
				continue;
			}


			// mov rcx, [global1]
			// add rax, rcx
			// =>
			// add rax, [global1]
			// TODO: only valid if rcx is not used
			if (IK(inst) == IK_BINALU && IM(inst) == M_Rr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CM && IREG2(inst) == IREG(prev) && IREG(inst) != IREG2(inst)) {
				IM(prev) = M_RM;
				IK(prev) = IK(inst);
				IS(prev) = IS(inst);
				IREG(prev) = IREG(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// mov rax, [rbp-16]
			// cmp rax, 10
			// =>
			// cmp [rbp-16], 10
			if (IK(inst) == IK_BINALU && IM(inst) == M_rI && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CM) {
				IM(inst) = M_MI;
				ISCALE(inst) = ISCALE(prev);
				IINDEX(inst) = IINDEX(prev);
				IBASE(inst) = IBASE(prev);
				IDISP(inst) = IDISP(prev);
				inst->prev = prev->prev;
				prev->prev->next = inst;
				inst = inst;
			}

			// NOTE: Actually we likely transform `cmp REG, 0` to
			// `test REG, REG` before this, but this pattern is more
			// general than that.
			//
			// mov rax, [rbp-16]
			// cmp rax, 0
			// =>
			// cmp [rbp-16]


			// lea rax, [rbp-8]
			// mov qword [rax], 3
			// =>
			// mov qword [rbp-8], 3
			// TODO: incorrect if rax is used further
			if (IK(inst) == IK_MOV && IS(inst) == MOV && (IM(inst) == M_MI || IM(inst) == M_Mr) && IK(prev) == IK_MOV && IS(prev) == LEA && IINDEX(inst) == R_NONE && ISCALE(inst) == 0 && IDISP(inst) == 0 && IBASE(inst) == IREG(prev)) {
				ISCALE(inst) = ISCALE(prev);
				IINDEX(inst) = IINDEX(prev);
				IBASE(inst) = IBASE(prev);
				IDISP(inst) = IDISP(prev);
				inst->prev = prev->prev;
				prev->prev->next = inst;
				inst = inst;
				continue;
			}

			// add t17, 8
			// mov qword [t17], 5
			// =>
			// mov qword [t17+8], 5
			// TODO: only valid if t17 is not used anywhere
			if (IK(inst) == IK_MOV && IS(inst) == MOV && (IM(inst) == M_MI || IM(inst) == M_Mr) && IK(prev) == IK_BINALU && IS(prev) == G1_ADD && IM(prev) == M_RI && IBASE(inst) == IREG(prev)) {
				IDISP(inst) += IIMM(prev);
				inst->prev = prev->prev;
				prev->prev->next = inst;
				inst = inst;
				continue;
			}

			Inst *pprev = prev->prev;
			if (!pprev) {
				goto next;
			}

			// mov t35, 8
			// mov t14, t34
			// add t14, t35
			// =>
			// mov t14, t34
			// add t14, 8
			// TODO: only valid if t35 is not used anywhere
			// (alternatively keep t35 and delete the unnecessery
			// move somewhere else)
			if (IK(inst) == IK_BINALU && IM(inst) == M_Rr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_Cr && IK(pprev) == IK_MOV && IS(pprev) == MOV && IM(pprev) == M_CI && IREG(pprev) == IREG2(inst)) {
				IM(inst) = M_RI;
				IIMM(inst) = IIMM(pprev);
				pprev->prev->next = prev;
				prev->prev = pprev->prev;
				inst = prev;
				continue;
			}


			// mov t20, t19
			// add t20, X
			// =>
			// coalesce if possible
			// HOW? Integrate with register coalescing?

			//     jge .BB3
			//     jmp .BB4
			// .BB3:
			// =>
			//     jl .BB4
			// .BB3:
			if (IK(pprev) == IK_JCC && IK(prev) == IK_JUMP && IK(inst) == IK_BLOCK && container_of(inst, MBlock, insts)->block->base.index == IIMM(pprev)) {
				IK(prev) = IK_JCC;
				IS(prev) = cc_invert(IS(pprev));
				pprev->prev->next = prev;
				prev->prev = pprev->prev;
				inst = prev;
				continue;
			}

			// mov rax, [rbp-24]
			// add rax, 1
			// mov [rbp-24], rax
			// =>
			// add [rbp-24], 1
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Mr && ((IK(prev) == IK_BINALU && IM(prev) == M_RI) || (IK(prev) == IK_UNALU && IM(prev) == M_R)) && IK(pprev) == IK_MOV && IS(pprev) == MOV && IM(pprev) == M_CM && IREG(prev) == IREG(pprev) && IREG(inst) == IREG(prev) && ISCALE(pprev) == ISCALE(inst) && IINDEX(pprev) == IINDEX(inst) && IBASE(pprev) == IBASE(inst) && IDISP(pprev) == IDISP(inst)) {
				IM(prev) = IM(prev) == M_RI ? M_MI : M_M;
				ISCALE(prev) = ISCALE(inst);
				IINDEX(prev) = IINDEX(inst);
				IBASE(prev) = IBASE(inst);
				IDISP(prev) = IDISP(inst);
				prev->prev = pprev->prev;
				pprev->prev->next = prev;
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}


			// mov t21, [rbp-24]
			// mov t22, t21
			// add t22, 1
			// mov [rbp-24], t22


			// mov t18, 4
			// mov t12, t18
			// add t12, t11
			// =>
			// mov t12, t11
			// add t12, 4
			if (IK(inst) == IK_BINALU && g1_is_commutative(IS(inst)) && IM(inst) == M_Rr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_Cr && IK(pprev) == IK_MOV && IS(pprev) == MOV && IM(pprev) == M_CI && IREG2(prev) == IREG(pprev) && IREG(inst) == IREG(prev)) {
				IREG2(prev) = IREG2(inst);
				IM(inst) = M_RI;
				IIMM(inst) = IIMM(pprev);
				pprev->prev->next = prev;
				prev->prev = pprev->prev;
				inst = prev;
				continue;
			}

			Inst *ppprev = pprev->prev;
			if (!ppprev) {
				goto next;
			}

			Inst *pppprev = ppprev->prev;
			if (!pppprev) {
				goto next;
			}

			// mov rcx, 0
			// cmp rax, rdx
			// setg cl
			// test rcx, rcx
			// jz .BB2
			// =>
			// cmp rax, rdx
			// jng .BB2
			if (IK(inst) == IK_JCC && IS(inst) == CC_Z && IK(prev) == IK_BINALU && IS(prev) == G1_TEST && IM(prev) == M_rr && IREG(prev) == IREG2(prev) && IK(pprev) == IK_SETCC && IREG(prev) == IREG(pprev) && IK(ppprev) == IK_BINALU && IS(ppprev) == G1_CMP && IK(pppprev) == IK_MOV && IS(pppprev) == MOV && IM(pppprev) == M_CI && IIMM(pppprev) == 0) {
				IS(inst) = cc_invert(IS(pprev));
				pppprev->prev->next = ppprev;
				ppprev->prev = pppprev->prev;
				inst->prev = ppprev;
				ppprev->next = inst;
				inst = ppprev;
				continue;
			}
		next:
			inst = inst->next;
		}
	}
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

static void PRINTF_LIKE(2)
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

	fprintf(stderr, "Globals:\n");
	print_globals(stderr, module);
	fprintf(stderr, "\n");
	for (size_t i = 0; i < function_cnt; i++) {
		number_values(functions[i], R__MAX);
		print_function(stderr, functions[i]);
		merge_simple_blocks(arena, functions[i]);
		print_function(stderr, functions[i]);
		get_uses(functions[i]);
		mem2reg(functions[i]);
		free_uses(functions[i]);
		value_numbering(arena, functions[i]);
		print_function(stderr, functions[i]);
		thread_jumps(arena, functions[i]);
		print_function(stderr, functions[i]);
		split_critical_edges(arena, functions[i]);
		print_function(stderr, functions[i]);
		single_exit(arena, functions[i]);
		print_function(stderr, functions[i]);
		///*
		translate_function(arena, functions[i]);
		print_mfunction(stderr, functions[i]->mfunc);
		peephole(functions[i]->mfunc, arena);
		print_mfunction(stderr, functions[i]->mfunc);
		reg_alloc_function(&ras, functions[i]->mfunc);
		print_mfunction(stderr, functions[i]->mfunc);
		peephole(functions[i]->mfunc, arena);
		print_mfunction(stderr, functions[i]->mfunc);
		//*/
		//peephole(functions[i]->mfunc, arena);
	}

	///*
	reg_alloc_state_destroy(&ras);

	printf("\tdefault rel\n\n");

	printf("\tsection .data\n");
	for (size_t i = 0; i < module->global_cnt; i++) {
		Global *global = module->globals[i];
		if (global->init) {
			//printf("\talign 8\n");
			print_str(stdout, global->name);
			printf(":\n");
			printf("global%zu:\n", global->base.index);
			printf("\tdq\t");
			print_value(stdout, global->init);
			printf("\n");
		}
	}
	printf("\n");

	printf("\tsection .bss\n");
	for (size_t i = 0; i < module->global_cnt; i++) {
		Global *global = module->globals[i];
		if (!global->init) {
			//printf("\talign 8\n");
			print_str(stdout, global->name);
			printf(":\n");
			printf("global%zu:\n", global->base.index);
			printf("\tresq\t1\n");
		}
	}
	printf("\n");

	printf("\tsection .text\n");
	printf("\n");
	printf("\tglobal _start\n");
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
	//*/

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
