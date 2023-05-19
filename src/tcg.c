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
#include "str.h"
#include "table.h"
#include "arena.h"
#include "worklist.h"
#include "type.h"
#include "ir.h"

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
	R_NONE = 0,
	R_RAX,
	R_RBX,
	R_RCX,
	R_RDX,
	R_RSI,
	R_RDI,
	R_8,
	R_9,
	R_10,
	R_11,
	R_12,
	R_13,
	R_14,
	R_15,

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
	"r8",
	"r9",
	"r10",
	"r11",
	"r12",
	"r13",
	"r14",
	"r15",

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
	"r8b",
	"r9b",
	"r10b",
	"r11b",
	"r12b",
	"r13b",
	"r14b",
	"r15b",

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

enum {
	F_CF = UINT32_C(1) << 0, // Carry
	F_PF = UINT32_C(1) << 2, // Parity
	F_AF = UINT32_C(1) << 4, // Auxiliary Carry
	F_ZF = UINT32_C(1) << 6, // Zero
	F_SF = UINT32_C(1) << 7, // Sign
	F_OF = UINT32_C(1) << 11, // Overflow
};

u32
cc_read_flags(CondCode cc)
{
	switch (cc) {
	case CC_O:
	case CC_NO:
		return F_OF;
	case CC_B:
	case CC_AE:
		return F_CF;
	case CC_Z:
	case CC_NZ:
		return F_ZF;
	case CC_BE:
	case CC_A:
		return F_CF | F_ZF;
	case CC_S:
	case CC_NS:
		return F_SF;
	case CC_P:
	case CC_NP:
		return F_PF;
	case CC_L:
	case CC_GE:
		return F_SF | F_OF;
	case CC_LE:
	case CC_G:
		return F_SF | F_ZF | F_OF;
	default:
		UNREACHABLE();
	}
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
	table_free(&env->scopes[--env->scope_cnt]);
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
		table_free(&env->scopes[--env->scope_cnt]);
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
	block->base.index = function->block_cap;
	// Functions grow in powers of two.
	if (!(function->block_cap & (function->block_cap - 1))) {
		GROW_ARRAY(function->blocks, function->block_cap ? function->block_cap * 2 : 4);
	}
	function->blocks[function->block_cap++] = block;
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
		type = declarator(parser, name, type, kind);
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
	return rvalue(add_binary(parser, VK_EQ, &TYPE_INT, arg, zero));
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
	if (!type_is_function_compatible(left->type)) {
		parser_error(parser, parser->lookahead, false, "Expected function call target to have function type");
	}
	FunctionType *fun_type = type_as_function(left->type);
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
	Type *field_type = &TYPE_VOID;
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
		// Following code is unreachable. Let's not add it by unsetting
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

static void
dfs(Block *block, size_t *index, Block **post_order)
{
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
print_mem(FILE *f, MFunction *mfunction, Inst *inst)
{
	fprintf(f, "[");
	if (IBASE(inst) == R_NONE) {
		Value *value = garena_array(mfunction->labels, Value *)[IDISP(inst)];
		print_value(f, value);
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
print_inst(FILE *f, MFunction *mfunction, Inst *inst)
{
	fprintf(f, "%s%s", ik_repr[IK(inst)], is_repr[IK(inst)][IS(inst)]);
	switch (inst->mode) {
	case M_Rr:
	case M_rr:
	case M_Cr:
	case M_Cn:
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
		print_mem(f, mfunction, inst);
		break;
	case M_Mr:
		fprintf(f, " ");
		print_mem(f, mfunction, inst);
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
		print_mem(f, mfunction, inst);
		fprintf(f, ", ");
		fprintf(f, "%"PRIi32, IIMM(inst));
		break;
	case M_CrI:
		fprintf(f, " ");
		print_reg(f, IREG1(inst));
		fprintf(f, ", ");
		print_reg(f, IREG2(inst));
		fprintf(f, ", ");
		fprintf(f, "%"PRIi32, IIMM(inst));
		break;
	case M_CMI:
		fprintf(f, " ");
		print_reg(f, IREG(inst));
		fprintf(f, ", ");
		print_mem(f, mfunction, inst);
		fprintf(f, "%"PRIi32, IIMM(inst));
		break;
	case M_R:
	case M_r:
	case M_C:
	case M_ADr:
	case M_rCALL:
		fprintf(f, " ");
		if (IK(inst) == IK_SETCC) {
			print_reg8(f, IREG(inst));
		} else {
			print_reg(f, IREG(inst));
		}
		break;
	case M_ADM:
	case M_M:
	case M_MCALL:
		fprintf(f, " ");
		print_mem(f, mfunction, inst);
		break;
	case M_I:
		fprintf(f, " ");
		fprintf(f, "%"PRIi32, IIMM(inst));
		break;
	case M_L:
		fprintf(f, " ");
		fprintf(f, ".BB%"PRIi32, ILABEL(inst));
		break;
	case M_LCALL: {
		fprintf(f, " ");
		Value *value = garena_array(mfunction->labels, Value *)[ILABEL(inst)];
		print_value(f, value);
		break;
	}
	case M_NONE:
		UNREACHABLE();
		break;
	case M_RET:
		break;
	}

	if (inst->reads_flags || inst->writes_flags || inst->flags_observed) {
		fprintf(f, " ; ");
		fprintf(f, "%s", inst->reads_flags ? "R" : "");
		fprintf(f, "%s", inst->writes_flags ? "W" : "");
		fprintf(f, "%s", inst->flags_observed ? "O" : "");
	}
}


typedef struct {
	Arena *arena;
	GArena *labels;
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
	inst->flags_observed = false; // Redefined later by analysis.
	inst->writes_flags = false; // Default is no flags.
	inst->reads_flags = false; // Default is no flags.
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
	inst->writes_flags = true;
	IREG(inst) = op1;
}

static void
add_binop(TranslationState *ts, X86Group1 op, Oper op1, Oper op2)
{
	Inst *inst = add_inst(ts, IK_BINALU, op);
	inst->mode = M_Rr;
	inst->writes_flags = true;
	IREG1(inst) = op1;
	IREG2(inst) = op2;
}

static void
add_cmp(TranslationState *ts, X86Group1 op, Oper op1, Oper op2)
{
	Inst *inst = add_inst(ts, IK_BINALU, op);
	inst->mode = M_rr;
	inst->writes_flags = true;
	IREG1(inst) = op1;
	IREG2(inst) = op2;
}

static void
add_shift(TranslationState *ts, X86Group2 op, Oper op1, Oper op2)
{
	Inst *inst = add_inst(ts, IK_SHIFT, op);
	inst->mode = M_Rr;
	inst->writes_flags = true;
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
	inst->reads_flags = true;
	IREG(inst) = oper;
}

static void
add_imul3(TranslationState *ts, Oper dest, Oper arg, Oper imm)
{
	Inst *inst = add_inst(ts, IK_IMUL3, 0);
	inst->mode = M_CrI;
	inst->writes_flags = true;
	IREG(inst) = dest;
	IREG2(inst) = arg;
	IIMM(inst) = imm;
}

static void
add_jmp(TranslationState *ts, Oper block_index)
{
	Inst *inst = add_inst(ts, IK_JUMP, 0);
	inst->mode = M_L;
	ILABEL(inst) = block_index;
}

static void
add_jcc(TranslationState *ts, CondCode cc, Oper block_index)
{
	Inst *inst = add_inst(ts, IK_JCC, cc);
	inst->mode = M_L;
	inst->reads_flags = true;
	ILABEL(inst) = block_index;
}

static void
add_call(TranslationState *ts, Oper function_reg, Oper arg_cnt)
{
	Inst *inst = add_inst(ts, IK_CALL, 0);
	inst->mode = M_rCALL;
	IREG(inst) = function_reg;
	IARG_CNT(inst) = arg_cnt;
}

static void
add_entry(TranslationState *ts, Oper arg_cnt)
{
	Inst *inst = add_inst(ts, IK_ENTRY, 0);
	inst->mode = M_ENTRY;
	IARG_CNT(inst) = arg_cnt;
}

static void
translate_call(TranslationState *ts, Oper res, Oper fun, Oper *args, size_t arg_cnt)
{
	assert(arg_cnt < ARRAY_LEN(argument_regs) - 1);
	for (size_t i = 0; i < arg_cnt; i++) {
		add_copy(ts, argument_regs[i], args[i]);
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

size_t
add_label(GArena *labels, Value *value)
{
	Value **existing = garena_array(labels, Value *);
	size_t index = garena_cnt(labels, Value *);
	for (size_t i = index; i--;) {
		if (existing[i] == value) {
			return i;
		}
	}
	garena_push_value(labels, Value *, value);
	return index;
}

void
translate_operand(void *user_data, size_t i, Value **operand_)
{
	TranslateOperandState *tos = user_data;
	TranslationState *ts = tos->ts;
	Value *operand = *operand_;
	Oper res;
	switch (operand->kind) {
	case VK_BLOCK:
		res = operand->index;
		break;
	case VK_FUNCTION: {
		//Function *function = (void*) operand;
		size_t label_index = add_label(ts->labels, operand);
		res = tos->ts->index++;
		add_lea(tos->ts, res, R_NONE, label_index);
		break;
	}
	case VK_GLOBAL: {
		//Global *global = (void*) operand;
		res = tos->ts->index++;
		size_t label_index = add_label(ts->labels, operand);
		add_lea(tos->ts, res, R_NONE, label_index);
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
	if (v->kind == VK_PHI) {
		// Don't translate phi nor its operands -- they are handled in
		// the predecessors.
		return;
	}
	fprintf(stderr, "Translating: ");
	print_value(stderr, v);
	for_each_operand(v, translate_operand, tos);
	Oper *ops = &tos->opers[0];
	//Oper res = ts->index++;
	Oper res = v->index;
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
		translate_cmpop(ts, CC_E, res, ops[0], ops[1]);
		break;
	case VK_NEQ:
		translate_cmpop(ts, CC_NE, res, ops[0], ops[1]);
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
		size_t arg_cnt = type_function_param_cnt(call->operands[0]->type);
		translate_call(ts, res, ops[0], &ops[1], arg_cnt);
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
ig_free(InterferenceGraph *ig, size_t capacity)
{
	FREE_ARRAY(ig->matrix, capacity * capacity);
	for (size_t i = 0; i < capacity; i++) {
		garena_free(&ig->adj_list[i]);
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
	print_str(f, mfunction->func->name);
	fprintf(f, ":\n");
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		fprintf(f, ".BB%zu:\n", mblock->block->base.index);
		for (Inst *inst = mblock->insts.next; inst != &mblock->insts; inst = inst->next) {
			fprintf(f, "\t");
			print_inst(f, mfunction, inst);
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
	u8 *def_count;
	u8 *use_count;
	u8 *unspillable;

	// Degrees of nodes.
	u32 *degree;

	InterferenceGraph ig;
	WorkList live_set;
	WorkList uninterrupted;
	u8 *ever_interrupted;
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
		.reg_avail = 14,
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
		GROW_ARRAY(ras->def_count, ras->vreg_capacity);
		GROW_ARRAY(ras->use_count, ras->vreg_capacity);
		GROW_ARRAY(ras->unspillable, ras->vreg_capacity);
		GROW_ARRAY(ras->degree, ras->vreg_capacity);
		ig_grow(&ras->ig, old_vreg_capacity, ras->vreg_capacity);
		wl_grow(&ras->live_set, ras->vreg_capacity);
		wl_grow(&ras->uninterrupted, ras->vreg_capacity);
		GROW_ARRAY(ras->ever_interrupted, ras->vreg_capacity);
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
	ZERO_ARRAY(ras->def_count, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->use_count, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->unspillable, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->degree, ras->mfunction->vreg_cnt);
	ig_reset(&ras->ig, ras->mfunction->vreg_cnt);
	wl_reset(&ras->live_set);
	wl_reset(&ras->uninterrupted);
	ZERO_ARRAY(ras->ever_interrupted, ras->vreg_capacity);
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
reg_alloc_state_free(RegAllocState *ras)
{
	FREE_ARRAY(ras->reg_assignment, ras->vreg_capacity);
	FREE_ARRAY(ras->to_spill, ras->vreg_capacity);
	FREE_ARRAY(ras->alias, ras->vreg_capacity);
	FREE_ARRAY(ras->def_count, ras->vreg_capacity);
	FREE_ARRAY(ras->use_count, ras->vreg_capacity);
	FREE_ARRAY(ras->unspillable, ras->vreg_capacity);
	FREE_ARRAY(ras->degree, ras->vreg_capacity);
	ig_free(&ras->ig, ras->vreg_capacity);
	wl_free(&ras->live_set);
	wl_free(&ras->uninterrupted);
	FREE_ARRAY(ras->ever_interrupted, ras->vreg_capacity);
	wl_reset(&ras->block_work_list);
	wl_free(&ras->block_work_list);
	for (size_t i = 0; i < ras->block_capacity; i++) {
		wl_free(&ras->live_in[i]);
	}
	FREE_ARRAY(ras->live_in, ras->block_capacity);
	wl_free(&ras->spill_wl);
	wl_free(&ras->freeze_wl);
	wl_free(&ras->simplify_wl);
	wl_free(&ras->moves_wl);
	wl_free(&ras->active_moves_wl);
	wl_free(&ras->stack);
	garena_free(&ras->gmoves);
	for (size_t i = 0; i < ras->vreg_capacity; i++) {
		garena_free(&ras->move_list[i]);
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
	if (op1 >= R__MAX) {
		garena_push_value(&ig->adj_list[op1], Oper, op2);
	}
	if (op2 >= R__MAX) {
		garena_push_value(&ig->adj_list[op2], Oper, op1);
	}
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
	if (mode->def_cnt_given_by_arg_cnt) {
		size_t def_cnt = IARG_CNT(inst);
		for (size_t i = 0; i < def_cnt; i++) {
			fun(user_data, &mode->extra_defs[i]);
		}
	} else {
		for (Oper *def = mode->extra_defs; *def != R_NONE; def++) {
			fun(user_data, def);
		}
	}
}

void
for_each_use(Inst *inst, void (*fun)(void *user_data, Oper *use), void *user_data)
{
	InsFormat *mode = &formats[inst->mode];
	for (size_t i = mode->use_start; i < mode->use_end; i++) {
		fun(user_data, &inst->ops[i]);
	}
	if (mode->use_cnt_given_by_arg_cnt) {
		size_t use_cnt = IARG_CNT(inst);
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

// Add spill code, coalesce registers that were found to be coalescable before
// the first potential spill.
void
rewrite_program(RegAllocState *ras)
{
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
			print_inst(stderr, mfunction, inst);
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
	table_free(&parser.type_env);

	if (parser.had_error) {
		return NULL;
	}
	Module *module = arena_alloc(arena, sizeof(*module));
	module->function_cnt = garena_cnt(&parser.functions, Function *);
	module->functions = move_to_arena(arena, &parser.functions, 0, Function *);
	module->global_cnt = garena_cnt(&parser.globals, Global *);
	module->globals = move_to_arena(arena, &parser.globals, 0, Global *);
	garena_free(&parser.functions);
	garena_free(&parser.globals);
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
		garena_free(&function->uses[i]);
	}
	free(function->uses);
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
	garena_free(&block->incomplete_phis);
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
		Block *block = function->post_order[b];
		FREE_ARRAY(vns->var_map[VINDEX(block)], value_cnt);
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

		for (Value *v = succ->base.next; v != &succ->base; v = v->next) {
			v->parent = &block->base;
		}

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
	wl_free(&worklist);

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
	wl_free(&worklist);

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
		garena_free(&gphis);
		return;
	}
	Block *ret_block = create_block(arena, function);

	bool ret_void = VK(phis[0].block->base.prev) == VK_RETVOID;

	for (size_t i = 0; i < phi_cnt; i++) {
		PendingPhi *phi = &phis[i];
		Block *pred = phi->block;
		Value *jump = create_unary(arena, pred, VK_JUMP, &TYPE_VOID, &ret_block->base);
		jump->index = function->value_cnt++;
		jump->parent = &pred->base;
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
		for (size_t i = 0; i < phi_cnt; i++) {
			phi->operands[i] = phis[i].value;
		}
		ret_inst = create_unary(arena, ret_block, VK_RET, &TYPE_VOID, &phi->base);
	}
	ret_inst->index = function->value_cnt++;
	ret_inst->parent = &ret_block->base;
	prepend_value(&ret_block->base, ret_inst);

	garena_free(&gphis);

	// Recompute function->post_order, since we invalidated it.
	compute_preorder(function);
}

void
mark_defs_with_uninterrupted_uses_unspillable(void *user_data, Oper *def_)
{
	RegAllocState *ras = user_data;
	Oper def = *def_;
	// Check if this definition has a following use and the live range is
	// uninterrupted by any death of other live range. Make sure that the
	// use is really uninterrupted, by checking global flag which forbids
	// interruptions.
	if (wl_remove(&ras->uninterrupted, def) && !ras->ever_interrupted[def]) {
		ras->unspillable[def] = true;
		if (def >= R__MAX) {
			fprintf(stderr, "Marking ");
			print_reg(stderr, def);
			fprintf(stderr, " as unspillable\n");
		}
	}
	// Update def count.
	ras->def_count[def] += 1;
	// Update liveness.
	wl_remove(&ras->live_set, def);
}

void
detect_interrupting_deaths(void *user_data, Oper *use_)
{
	RegAllocState *ras = user_data;
	Oper use = *use_;
	if (!wl_has(&ras->live_set, use)) {
		WorkList *uninterrupted = &ras->uninterrupted;
		FOR_EACH_WL_INDEX(uninterrupted, i) {
			Oper op = uninterrupted->dense[i];
			ras->ever_interrupted[op] = true;
		}
		wl_reset(uninterrupted);
	}
}

void
add_live(void *user_data, Oper *use_)
{
	RegAllocState *ras = user_data;
	Oper use = *use_;
	// Update use count.
	ras->use_count[use] += 1;
	// Update liveness and add note that this use is uninterrupted for now.
	wl_add(&ras->live_set, use);
	wl_add(&ras->uninterrupted, use);
}

void
calculate_spill_cost(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	WorkList *live_set = &ras->live_set;

	for (Oper b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		Block *block = mblock->block;
		get_live_out(ras, block, live_set);
		// We currently can't make unspillable those vregs whose live
		// ranges cross basic block boundaries. Make sure we don't mark
		// them unspillable by marking them as "interrupted somewhere"
		// (in this case by basic block boundary).
		FOR_EACH_WL_INDEX(live_set, i) {
			Oper live_across_block = live_set->dense[i];
			ras->ever_interrupted[live_across_block] = true;
		}
		for (Inst *inst = mblock->insts.prev; inst != &mblock->insts; inst = inst->prev) {
			for_each_def(inst, mark_defs_with_uninterrupted_uses_unspillable, ras);
			for_each_use(inst, detect_interrupting_deaths, ras);
			for_each_use(inst, add_live, ras);
		}
	}
}

MFunction *
translate_function(Arena *arena, GArena *labels, Function *function)
{
	Block **post_order = function->post_order;

	MFunction *mfunction = arena_alloc(arena, sizeof(*mfunction));
	memset(mfunction, 0, sizeof(*mfunction));
	mfunction->func = function;
	mfunction->labels = labels;
	mfunction->mblocks = arena_alloc(arena, function->block_cnt * sizeof(mfunction->mblocks[0]));
	mfunction->mblock_cnt = 0; // incremented when each block is inserted

	TranslationState ts_ = {
		.arena = arena,
		.labels = labels,
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
			add_entry(ts, type_function_param_cnt(function->base.type));
			add_push(ts, R_RBP);
			add_copy(ts, R_RBP, R_RSP);
			// Add instruction to make stack space, since we may
			// spill we don't know how much stack space to reserve
			// yet, we will replace the dummy '0' with proper stack
			// space requirement after register allocation.
			ts->make_stack_space = add_inst(ts, IK_BINALU, G1_SUB);
			Inst *inst = ts->make_stack_space;
			inst->mode = M_RI;
			inst->writes_flags = true;
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
liveness_analysis(RegAllocState *ras)
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
}

void
build_interference_graph(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	WorkList *live_set = &ras->live_set;

	for (Oper b = 0; b < mfunction->mblock_cnt; b++) {
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
	//fprintf(stderr, "Is move related ");
	//print_reg(stderr, i);
	//fprintf(stderr, "\n");
	//Inst **moves = garena_array(&ras->gmoves, Inst *);
	GArena *gmove_list = &ras->move_list[i];
	Oper *move_list = garena_array(gmove_list, Oper);
	size_t move_cnt = garena_cnt(gmove_list, Oper);
	for (size_t i = 0; i < move_cnt; i++) {
		Oper move_index = move_list[i];
		//Inst *move = moves[move_index];
		//fprintf(stderr, "Moved in \t");
		//print_inst(stderr, ras->mfunction, move);
		//fprintf(stderr, "\n");
		if (wl_has(&ras->active_moves_wl, move_index) || wl_has(&ras->moves_wl, move_index)) {
			return true;
		}
	}
	//fprintf(stderr, "Not move related\n");
	return false;
}


void
for_each_adjacent(RegAllocState *ras, Oper op, void (*fun)(RegAllocState *ras, Oper neighbour))
{
	assert(op >= R__MAX);
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

bool
is_precolored(RegAllocState *ras, Oper op)
{
	return op < R__MAX;
}

bool
is_trivially_colorable(RegAllocState *ras, Oper op)
{
	return ras->degree[op] < ras->reg_avail;
}

bool
is_significant(RegAllocState *ras, Oper op)
{
	return ras->degree[op] >= ras->reg_avail;
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
		if (is_significant(ras, i)) {
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
	fprintf(stderr, " degree: %"PRIu32", defs: %zu, uses: %zu, unspillable: %d\n", ras->degree[i], (size_t) ras->def_count[i], (size_t) ras->use_count[i], (int) ras->unspillable[i]);
	if (ras->unspillable[i]) {
		return 0.0;
	}
	return (double) ras->degree[i] / (ras->def_count[i] + ras->use_count[i]);
}

void
enable_move(RegAllocState *ras, Oper u, Oper m, Inst *move)
{
	(void) u;
	if (wl_remove(&ras->active_moves_wl, m)) {
		fprintf(stderr, "Enabling move: \t");
		print_inst(stderr, ras->mfunction, move);
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
	ras->degree[op]--;
	if (is_trivially_colorable(ras, op)) {
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
	print_inst(stderr, ras->mfunction, move);
	fprintf(stderr, "\n");
	if (!wl_remove(&ras->active_moves_wl, m)) {
		wl_remove(&ras->moves_wl, m);
	}
	Oper v = move->ops[0] != u ? move->ops[0] : move->ops[1];
	if (!is_move_related(ras, v) && is_trivially_colorable(ras, v)) {
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
freeze_one(RegAllocState *ras, Oper i)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->moves_wl));

	fprintf(stderr, "Freezing node ");
	print_reg(stderr, i);
	fprintf(stderr, "\n");

	wl_add(&ras->simplify_wl, i);
	freeze_moves(ras, i);
}

void
simplify_one(RegAllocState *ras, Oper i)
{
	fprintf(stderr, "Pushing ");
	print_reg(stderr, i);
	fprintf(stderr, "\n");

	wl_add(&ras->stack, i);
	for_each_adjacent(ras, i, decrement_degree);
}

void
choose_and_spill_one(RegAllocState *ras)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->moves_wl));
	assert(!wl_empty(&ras->spill_wl));

	fprintf(stderr, "Potential spill\n");

	Oper candidate = OPER_MAX;
	double max = 0.0;
	WorkList *spill_wl = &ras->spill_wl;
	FOR_EACH_WL_INDEX(spill_wl, j) {
		Oper i = spill_wl->dense[j];
		double curr = spill_metric(ras, i);
		// Prefer for spill either more beneficial candidates (with
		// bigger metric) or "earlier" vregs ("smaller index"). This
		// comes in handy for spilling callee saved registers, where we
		// want to spill `rbx` first, since encoding it is (sometimes)
		// shorter.
		if (curr > max || (curr == max && i < candidate)) {
			max = curr;
			candidate = i;
		}
	}

	fprintf(stderr, "Choosing for spill ");
	print_reg(stderr, candidate);
	fprintf(stderr, "\n");
	assert(candidate != OPER_MAX);
	assert(max > 0.0);

	wl_remove(&ras->spill_wl, candidate);
	wl_add(&ras->simplify_wl, candidate);
	freeze_moves(ras, candidate);
}

void
add_to_worklist(RegAllocState *ras, Oper op)
{
	if (!is_precolored(ras, op) && !is_move_related(ras, op) && is_trivially_colorable(ras, op)) {
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
	assert(op >= R__MAX);
	GArena *gadj_list = &ras->ig.adj_list[op];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t j = 0; j < adj_cnt; j++) {
		Oper t = adj_list[j];
		if (wl_has(&ras->stack, t) || is_alias(ras, t)) {
			continue;
		}
		n += is_significant(ras, t);
	}
	return n;
}

bool
ok(RegAllocState *ras, Oper t, Oper r)
{
	return is_trivially_colorable(ras, t) || is_precolored(ras, t) || ig_interfere(&ras->ig, t, r);
}

bool
precolored_coalesce_heuristic(RegAllocState *ras, Oper u, Oper v)
{
	assert(v >= R__MAX);
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

	assert(v >= R__MAX);
	if (!wl_remove(&ras->freeze_wl, v)) {
		assert(wl_remove(&ras->spill_wl, v));
	}

	// Set `v` as alias of `u`. Caller should already pass canonical `u`
	// and `v`, which are not aliases themselves.
	ras->alias[v] = u;

	// Add moves of `v` to `u`.
	Oper *other_moves = garena_array(&ras->move_list[v], Oper);
	size_t other_move_cnt = garena_cnt(&ras->move_list[v], Oper);
	for (size_t i = 0; i < other_move_cnt; i++) {
		// NOTE: would deduplication be beneficial?
		garena_push_value(&ras->move_list[u], Oper, other_moves[i]);
	}

	// Add edges of `v` to `u`.
	GArena *gadj_list = &ras->ig.adj_list[v];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t i = 0; i < adj_cnt; i++) {
		Oper t = adj_list[i];
		if (wl_has(&ras->stack, t) || is_alias(ras, t)) {
			continue;
		}
		// Add `u` as a neighbour to `v`'s neighbour `t`.
		ig_add(&ras->ig, u, t);
		// Since we coalesce `u` and `v`, we should remove `v` as a
		// neighbour. The important thing that we want to achieve is
		// actually decrement of `t`'s degree, which might make it
		// trivially colorable.
		//
		// We can get away with not removing `v` from adjacency list of
		// `u`, because aliased registers are skipped or resolve by
		// those iterating over them.
		decrement_degree(ras, t);
	}

	if (is_significant(ras, u) && wl_remove(&ras->freeze_wl, u)) {
		fprintf(stderr, "Move combined ");
		print_reg(stderr, u);
		fprintf(stderr, " from freeze to spill\n");
		wl_add(&ras->spill_wl, u);
	}
}

void
coalesce_move(RegAllocState *ras, Oper m)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->simplify_wl));
	MFunction *mfunction = ras->mfunction;

	Inst **moves = garena_array(&ras->gmoves, Inst *);
	Inst *move = moves[m];
	fprintf(stderr, "Coalescing: \t");
	print_inst(stderr, mfunction, move);
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
		print_inst(stderr, mfunction, move);
		fprintf(stderr, "\n");
		add_to_worklist(ras, u);
	} else if (v < R__MAX || ig_interfere(&ras->ig, u, v)) {
		// constrained
		fprintf(stderr, "Constrained: \t");
		print_inst(stderr, mfunction, move);
		fprintf(stderr, "\n");
		add_to_worklist(ras, u);
		add_to_worklist(ras, v);
	} else if (are_coalesceble(ras, u, v)) {
		// coalesce
		combine(ras, u, v);
		add_to_worklist(ras, u);
	} else {
		fprintf(stderr, "Moving to active: \t");
		print_inst(stderr, mfunction, move);
		fprintf(stderr, "\n");
		wl_add(&ras->active_moves_wl, m);
	}
}

bool
assign_registers(RegAllocState *ras)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->spill_wl));
	assert(wl_empty(&ras->freeze_wl));
	assert(wl_empty(&ras->moves_wl));

	bool have_spill = false;
	MFunction *mfunction = ras->mfunction;

	// Physical registers are assigned themselves.
	for (size_t i = 0; i < R__MAX; i++) {
		ras->reg_assignment[i] = i;
	}

	Oper i;
	while (wl_take_back(&ras->stack, &i)) {
		assert(i >= R__MAX);
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
			Oper neighbour = get_alias(ras, adj_list[j]);
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
		liveness_analysis(ras);
		build_interference_graph(ras);
		calculate_spill_cost(ras);
		initialize_worklists(ras);

		Oper i;
	simplify:
		while (wl_take_back(&ras->simplify_wl, &i)) {
			simplify_one(ras, i);
		}
		if (wl_take(&ras->moves_wl, &i)) {
			coalesce_move(ras, i);
			goto simplify;
		}
		if (wl_take_back(&ras->freeze_wl, &i)) {
			freeze_one(ras, i);
			goto simplify;
		}
		if (!wl_empty(&ras->spill_wl)) {
			choose_and_spill_one(ras);
			goto simplify;
		}

		if (assign_registers(ras)) {
			break;
		}
		rewrite_program(ras);
	}

	// Fixup stack space amount reserved at the start of the function
	IIMM(mfunction->make_stack_space) = mfunction->stack_space;
	apply_reg_assignment(ras);
}

void
increment_count(void *user_data, Oper *oper)
{
	u8 *count = user_data;
	count[*oper]++;
}

void
decrement_count(void *user_data, Oper *oper)
{
	u8 *count = user_data;
	count[*oper]--;
}

typedef struct {
	Inst *inst;
	Inst **only_def;
	u8 *def_cnt;
} LastDefState;

void
track_last_def(void *user_data, Oper *oper)
{
	LastDefState *lds = user_data;
	// It is important that we set this to NULL if any second definition
	// exists, otherwise decrements of the def count might make it seem
	// like there was only one definition.
	lds->only_def[*oper] = lds->def_cnt[*oper] == 1 ? lds->inst : NULL;
}

void
calculate_def_use_info(MFunction *mfunction)
{
	GROW_ARRAY(mfunction->def_count, mfunction->vreg_cnt);
	GROW_ARRAY(mfunction->use_count, mfunction->vreg_cnt);
	GROW_ARRAY(mfunction->only_def, mfunction->vreg_cnt);
	ZERO_ARRAY(mfunction->def_count, mfunction->vreg_cnt);
	ZERO_ARRAY(mfunction->use_count, mfunction->vreg_cnt);
	ZERO_ARRAY(mfunction->only_def, mfunction->vreg_cnt);
	LastDefState lds = { .only_def = mfunction->only_def, .def_cnt = mfunction->def_count };
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		bool flags_needed = false;
		for (Inst *inst = mblock->insts.prev; inst != &mblock->insts; inst = inst->prev) {
			lds.inst = inst;
			for_each_def(inst, increment_count, mfunction->def_count);
			for_each_def(inst, track_last_def, &lds);
			for_each_use(inst, increment_count, mfunction->use_count);
			inst->flags_observed = flags_needed;
			if (inst->writes_flags) {
				flags_needed = false;
			}
			if (inst->reads_flags) {
				flags_needed = true;
			}
		}
	}
}

void
mfunction_free(MFunction *mfunction)
{
	FREE_ARRAY(mfunction->def_count, mfunction->vreg_cnt);
	FREE_ARRAY(mfunction->use_count, mfunction->vreg_cnt);
	FREE_ARRAY(mfunction->only_def, mfunction->vreg_cnt);
}

bool
try_replace_by_immediate(MFunction *mfunction, Inst *inst, Oper o)
{
	Inst *def = mfunction->only_def[o];
	if (!def) {
		return false;
	}
	assert(mfunction->def_count[o] == 1);
	if (!(IK(def) == IK_MOV && IS(def) == MOV && IM(def) == M_CI)) {
		return false;
	}
	IIMM(inst) = IIMM(def);
	if (--mfunction->use_count[IREG(def)] == 0) {
		assert(--mfunction->def_count[IREG(def)] == 0);
		def->prev->next = def->next;
		def->next->prev = def->prev;
	}
	return true;
}

bool
try_combine_memory(MFunction *mfunction, Inst *inst)
{
	Inst *def = mfunction->only_def[IBASE(inst)];
	if (!def) {
		return false;
	}
	assert(mfunction->def_count[IBASE(inst)] == 1);
	if (!(IK(def) == IK_MOV && IS(def) == LEA)) {
		return false;
	}
	i64 disp = IDISP(inst) + IDISP(def);
	if (disp > INT32_MAX || disp < INT32_MIN) {
		return false;
	}
	if (IINDEX(inst)) {
                // We could try harder to support some combinations, but we
                // currently don't. E.g. if only has one index or both have same
                // index and both scales are 1 (making the combined scale 2),
                // etc.
                return false;
	}
	if (ISCALE(inst) != 0) {
		// Like above.
		return false;
	}
	IBASE(inst) = IBASE(def);
	ISCALE(inst) = ISCALE(def);
	IINDEX(inst) = IINDEX(def);
	IDISP(inst) = disp;
	if (--mfunction->use_count[IREG(def)] == 0) {
		assert(--mfunction->def_count[IREG(def)] == 0);
		def->prev->next = def->next;
		def->next->prev = def->prev;
	}
	return true;
}

bool
try_combine_label(MFunction *mfunction, Inst *inst)
{
	Inst *def = mfunction->only_def[IREG(inst)];
	if (!def) {
		return false;
	}
	assert(mfunction->def_count[IREG(inst)] == 1);
	if (!(IK(def) == IK_MOV && IS(def) == LEA && IBASE(def) == R_NONE)) {
		return false;
	}
	ILABEL(inst) = IDISP(def);
	if (--mfunction->use_count[IREG(def)] == 0) {
		def->prev->next = def->next;
		def->next->prev = def->prev;
	}
	return true;
}

void
peephole(MFunction *mfunction, Arena *arena)
{
	u8 *use_cnt = mfunction->use_count;
	u8 *def_cnt = mfunction->def_count;
	Inst **defs = mfunction->only_def;
	print_str(stderr, mfunction->func->name);
	fprintf(stderr, "\n");
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		Inst *inst = mblock->insts.next;
		while (inst != &mblock->insts) {
			print_inst(stderr, mfunction, inst);
			fprintf(stderr, "\n");
			fflush(stderr);
			// mov rax, rax
			// =>
			// [deleted]
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Cr && IREG(inst) == IREG2(inst)) {
				use_cnt[IREG(inst)]--;
				def_cnt[IREG(inst)]--;
				inst->prev->next = inst->next;
				inst->next->prev = inst->prev;
				goto next;
			}

			// mov t13, ... (where t13 is not used further)
			// =>
			// deleted
			//
			// xor t14, t14 (where t14 is not used further)
			// =>
			// deleted
			if ((IM(inst) == M_CI || IM(inst) == M_Cr || IM(inst) == M_CM || IM(inst) == M_Cn) && use_cnt[IREG(inst)] == 0) {
				def_cnt[IREG(inst)]--;
				for_each_use(inst, decrement_count, use_cnt);
				inst->prev->next = inst->next;
				inst->next->prev = inst->prev;
				goto next;
			}

			// cmp rax, 0
			// =>
			// test rax, rax
			if (IK(inst) == IK_BINALU && IS(inst) == G1_CMP && IM(inst) == M_rI && IIMM(inst) == 0) {
				use_cnt[IREG(inst)]++;
				IS(inst) = G1_TEST;
				IM(inst) = M_rr;
				IREG2(inst) = IREG(inst);
				continue;
			}

			// test/cmp ..., ... (and no flags observed)
			// =>
			// [deleted]
			if (IK(inst) == IK_BINALU && (IS(inst) == G1_TEST || IS(inst) == G1_CMP) && !IOF(inst)) {
				for_each_use(inst, decrement_count, use_cnt);
				inst->prev->next = inst->next;
				inst->next->prev = inst->prev;
				goto next;
			}

			// mov t20, 0 (and flags not observed)
			// =>
			// xor t20, t20 (sets flags, but noone will read them)
			if (false && IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_CI && IIMM(inst) == 0 && !IOF(inst)) {
				// the second occurence doesn't count as use
				IK(inst) = IK_BINALU;
				IS(inst) = G1_XOR;
				IM(inst) = M_Cn;
				IWF(inst) = true;
				IREG2(inst) = IREG(inst);
				continue;
			}

			// add ..., 1 (and flags not observed)
			// =>
			// inc ...
			// Probably not worth it.
			// https://www.agner.org/optimize/microarchitecture.pdf
			if (false) {}

			Inst *prev = inst->prev;
			if (!prev) {
				goto next;
			}

			// lea t32, [rbp-16] // IK_MOV ANY M_C*
			// mov t14, t32
			// =>
			// lea t14, [rbp-16]
			//
			// mov t27, 1
			// mov t18, t27
			// =>
			// mov t18, 1
			if (IK(inst) == IK_MOV && IM(inst) == M_Cr && (IM(prev) == M_CI || IM(prev) == M_Cr || IM(prev) == M_CM) && IREG(prev) == IREG2(inst) && use_cnt[IREG(prev)] == 1) {
				def_cnt[IREG(prev)]--;
				use_cnt[IREG(prev)]--;
				IREG(prev) = IREG(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				prev->next = inst->next;
				inst = prev;
				continue;
			}

			// mov t12, 8
			// add t11, t12
			// =>
			//|mov t12, 8|
			// add t11, 8
			if (IK(inst) == IK_BINALU && (IM(inst) == M_Rr || IM(inst) == M_rr) && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && IREG(prev) == IREG2(inst)) {
				inst->mode = IM(inst) == M_Rr ? M_RI : M_rI;
				IREG2(inst) = R_NONE;
				IIMM(inst) = IIMM(prev);
				if (--use_cnt[IREG(prev)] == 0) {
					--def_cnt[IREG(prev)];
					inst->prev = prev->prev;
					prev->prev->next = inst;
				}
				inst = inst;
				continue;
			}

			// mov t34, 3
			// mov [t14], t34
			// =>
			//|mov t34, 3|
			// mov [t14], 3
			if (IK(inst) == IK_MOV && IM(inst) == M_Mr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && IREG(prev) == IREG(inst)) {
				IM(inst) = M_MI;
				IIMM(inst) = IIMM(prev);
				if (--use_cnt[IREG(prev)] == 0) {
					--def_cnt[IREG(prev)];
					inst->prev = prev->prev;
					prev->prev->next = inst;
				}
				inst = inst;
				continue;
			}

			// lea t25, [rbp-24]
			// mov t26, [t25]
			// =>
			// mov t26, [rbp-24]
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_CM && IINDEX(inst) == R_NONE && ISCALE(inst) == 0 && IDISP(inst) == 0 && IK(prev) == IK_MOV && IS(prev) == LEA && IM(prev) == M_CM && IBASE(inst) == IREG(prev) && use_cnt[IREG(prev)] == 1) {
				def_cnt[IREG(prev)]--;
				use_cnt[IREG(prev)]--;
				IS(prev) = MOV;
				IREG(prev) = IREG(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// mov rcx, [global1]
			// add rax, rcx
			// =>
			// add rax, [global1]
			if (IK(inst) == IK_BINALU && IM(inst) == M_Rr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CM && IREG2(inst) == IREG(prev) && IREG(inst) != IREG2(inst) && use_cnt[IREG(prev)] == 1) {
				def_cnt[IREG(prev)]--;
				use_cnt[IREG(prev)]--;
				IM(prev) = M_RM;
				IK(prev) = IK(inst);
				IS(prev) = IS(inst);
				IREG(prev) = IREG(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// mov t13, [rbp-16]
			// cmp t13, 10
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


			// mov rax, 1
			// add rax, 2
			// =>
			// mov rax, 3
			if (IK(inst) == IK_BINALU && IM(inst) == M_RI && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && IREG(inst) == IREG(prev)) {
				def_cnt[IREG(inst)]--;
				use_cnt[IREG(inst)]--;
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
				inst = prev;
				continue;
			skip:;
			}

			// lea t14, [rbp-16]
			// add t14, 8
			// =>
			// lea t14, [rbp-8]
			if (IK(inst) == IK_BINALU && IS(inst) == G1_ADD && IM(inst) == M_RI && IK(prev) == IK_MOV && IS(prev) == LEA && IREG(prev) == IREG(inst)) {
				def_cnt[IREG(inst)]--;
				use_cnt[IREG(inst)]--;
				IDISP(prev) += IIMM(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				prev->next = inst->next;
				inst = prev;
				continue;
			}

			// mov [G], t27
			// mov t28, [G]
			// =>
			// mov [G], t27
			// mov t28, t27
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_CM && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_Mr && IBASE(inst) == IBASE(prev) && ISCALE(inst) == ISCALE(prev) && IINDEX(inst) == IINDEX(prev) && IDISP(inst) == IDISP(prev)) {
				use_cnt[IREG(prev)]++;
				IM(inst) = M_Cr;
				IREG2(inst) = IREG(prev);
				inst = inst;
				continue;
			}

			// lea rax, [rbp-8]
			// mov qword [rax], 3
			// =>
			// mov qword [rbp-8], 3
			if (IK(inst) == IK_MOV && IS(inst) == MOV && (IM(inst) == M_MI || IM(inst) == M_Mr) && IK(prev) == IK_MOV && IS(prev) == LEA && IINDEX(prev) == R_NONE && ISCALE(prev) == 0 && IBASE(inst) == IREG(prev) && use_cnt[IREG(prev)] == 1) {
				IBASE(inst) = IBASE(prev);
				IDISP(inst) += IDISP(prev);
				inst->prev = prev->prev;
				prev->prev->next = inst;
				inst = inst;
				continue;
			}

			// add t17, 8
			// mov qword [t17], 5
			// =>
			// mov qword [t17+8], 5
			// NOTE: only valid if t17 is not used anywhere
			if (IK(inst) == IK_MOV && IS(inst) == MOV && (IM(inst) == M_MI || IM(inst) == M_Mr) && IK(prev) == IK_BINALU && IS(prev) == G1_ADD && IM(prev) == M_RI && IBASE(inst) == IREG(prev) && use_cnt[IBASE(inst)] == 2) {
				def_cnt[IBASE(inst)]--;
				use_cnt[IBASE(inst)]--;
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

			// CP
			// mov t35, 8
			// mov t14, t34
			// add t14, t35
			// =>
			// mov t14, t34
			// add t14, 8
			if (IK(inst) == IK_BINALU && IM(inst) == M_Rr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_Cr && IK(pprev) == IK_MOV && IS(pprev) == MOV && IM(pprev) == M_CI && IREG(pprev) == IREG2(inst) && use_cnt[IREG2(inst)] == 1) {
				def_cnt[IREG2(inst)]--;
				use_cnt[IREG2(inst)]--;
				IM(inst) = M_RI;
				IIMM(inst) = IIMM(pprev);
				pprev->prev->next = prev;
				prev->prev = pprev->prev;
				inst = prev;
				continue;
			}

			// CP
			// mov t22, [H]
			// mov t23, ...
			// add t23, t22
			// =>
			// mov t23, ...
			// add t23, [H]
			if (IK(inst) == IK_BINALU && IM(inst) == M_Rr && IK(prev) == IK_MOV && IS(prev) == MOV && (IM(pprev) == M_CI || IM(pprev) == M_Cr || IM(pprev) == M_CM) && IREG(prev) == IREG(inst) && IREG(pprev) == IREG2(inst) && use_cnt[IREG(pprev)] == 1 && def_cnt[IREG(inst)] == 2) {
				// We made sure that def_cnt of t23 is 2, which
				// is the two definitions we see in this
				// peephole. This should guarantee us, that t23
				// isn't in any way connected to definition of
				// of [H] (because then there would be an
				// additional definition).
				def_cnt[IREG(pprev)]--;
				use_cnt[IREG(pprev)]--;
				IK(pprev) = IK(inst);
				IS(pprev) = IS(inst);
				switch (IM(pprev)) {
				case M_CI: IM(pprev) = M_RI; break;
				case M_Cr: IM(pprev) = M_Rr; break;
				case M_CM: IM(pprev) = M_RM; break;
				default: UNREACHABLE();
				}
				IREG(pprev) = IREG(inst);
				pprev->prev->next = prev;
				prev->prev = pprev->prev;
				prev->next = pprev;
				pprev->prev = prev;
				pprev->next = inst->next;
				inst->next->prev = pprev;
				inst = pprev;
				continue;
			}

			// mov t26, t18
			// add t26, t34 ; W (no flags observed)
			// =>
			// lea t26, [t18+t34]
			if (IK(inst) == IK_BINALU && IS(inst) == G1_ADD && (IM(inst) == M_Rr || IM(inst) == M_RI) && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_Cr && IREG(prev) == IREG(inst) && def_cnt[IREG(inst)] == 2) {
				use_cnt[IREG(inst)]--;
				def_cnt[IREG(inst)]--;
				defs[IREG(inst)] = prev;
				IS(prev) = LEA;
				IM(prev) = M_CM;
				IBASE(prev) = IREG2(prev);
				ISCALE(prev) = 0;
				if (IM(inst) == M_Rr) {
					IINDEX(prev) = IREG2(inst);
					IDISP(prev) = 0;
				} else {
					IINDEX(prev) = R_NONE;
					IDISP(prev) = IIMM(inst);
				}
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// imul t50, t21, 8 ; W
			// lea t32, [t18+t50]
			// =>
			// lea t32, [t18+8*t50]
			if (mode_has_memory(IM(inst)) && IINDEX(inst) != R_NONE && IK(prev) == IK_IMUL3 && IM(prev) == M_CrI && IREG(prev) == IINDEX(inst) && IIMM(prev) == 8 && ISCALE(inst) == 0 && use_cnt[IREG(prev)] == 1) {
				use_cnt[IREG(prev)]--;
				ISCALE(inst) = 3;
				IINDEX(inst) = IREG2(prev);
				inst->prev = pprev;
				pprev->next = inst;
				inst = inst;
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


			// imul t36, t44 ; W
			// test t36, t36 ; WO
			// =>
			// imul t36, t44 ; WO
			if (IK(inst) == IK_BINALU && (IS(inst) == G1_CMP || IS(inst) == G1_TEST) && IM(inst) == M_rr && IREG(inst) == IREG2(inst) && IWF(prev) && ((IK(prev) == IK_BINALU && (IM(prev) == M_Rr || IM(prev) == M_RI || IM(prev) == M_RM)) || (IK(prev) == IK_UNALU && IM(prev) == M_R)) && IREG(prev) == IREG(inst)) {
				IOF(prev) = true;
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// setg t28
			// test t28, t28
			// jz .BB3
			// =>
			// jng .BB2
			if ((IK(inst) == IK_JCC || IK(inst) == IK_CMOVCC || IK(inst) == IK_SETCC) && IS(inst) == CC_Z && IK(prev) == IK_BINALU && IS(prev) == G1_TEST && IM(prev) == M_rr && IREG(prev) == IREG2(prev) && IK(pprev) == IK_SETCC && IREG(prev) == IREG(pprev)) {
				def_cnt[IREG(pprev)]--;
				use_cnt[IREG(pprev)] -= 3; // (2 for test, 1 for setcc)
				IS(inst) = cc_invert(IS(pprev));
				pprev->prev->next = inst;
				inst->prev = pprev->prev;
				// Go back before the flags are set and look for
				// optimization opportunities. For example for
				// the rest of the following pattern:
				// xor t28, t28 ; W
				// cmp t27, t41 ; WO
				// setg t28 ; R
				while (IRF(inst) || IOF(inst)) {
					inst = inst->prev;
				}
				continue;
			}

			// ... t32, CONST
			// ...
			// mov t14, t32
			// =>
			//|... t32, ...|
			// mov t14, CONST
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Cr && try_replace_by_immediate(mfunction, inst, IREG2(inst))) {
				IM(inst) = M_CI;
				continue;
			}

			// ... t32, CONST
			// ...
			// add t14, t32
			// =>
			//|... t32, ...|
			// add t14, CONST
			if (IK(inst) == IK_BINALU && (IM(inst) == M_Rr || IM(inst) == M_rr) && try_replace_by_immediate(mfunction, inst, IREG2(inst))) {
				assert(IM(inst) == M_rr || inst->writes_flags);
				IM(inst) = IM(inst) == M_Rr ? M_RI : M_rI;
				continue;
			}

			// ... t32, CONST
			// ...
			// mov [t14], t32
			// =>
			//|... t32, ...|
			// mov [t14], CONST
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Mr && try_replace_by_immediate(mfunction, inst, IREG2(inst))) {
				IM(inst) = M_MI;
				continue;
			}

			// lea t25, [rbp-24]
			// ...
			// mov t26, [t25]
			// =>
			// mov t26, [rbp-24]
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_CM && try_combine_memory(mfunction, inst)) {
				continue;
			}

			// lea t25, [rbp-24]
			// ...
			// mov [t25], t24
			// =>
			// mov [rbp-24], t24
			if (IK(inst) == IK_MOV && IS(inst) == MOV && (IM(inst) == M_Mr || IM(inst) == M_MI) && try_combine_memory(mfunction, inst)) {
				continue;
			}

			// lea rax, [one]
			// call rax
			//=>
			// call one
			if (IK(inst) == IK_CALL && IM(inst) == M_rCALL && try_combine_label(mfunction, inst)) {
				IM(inst) = M_LCALL;
				continue;
			}

		next:
			inst = inst->next;
		}

		if (b == mfunction->mblock_cnt - 1) {
			break;
		}

		Oper next_block_index = mfunction->mblocks[b + 1]->block->base.index;
		Inst *last = mblock->insts.prev;
		Inst *prev = last->prev;

		//     jge .BB3
		//     jmp .BB4
		// .BB3:
		// =>
		//     jl .BB4
		// .BB3:
		if (IK(last) == IK_JUMP && IK(prev) == IK_JCC && ILABEL(prev) == next_block_index) {
			IS(prev) = cc_invert(IS(prev));
			ILABEL(prev) = ILABEL(last);
			last->prev->next = last->next;
			last->next->prev = last->prev;
			continue;
		}

		//     jmp .BB5
		// .BB5:
		// =>
		// .BB5:
		if (IK(last) == IK_JUMP && ILABEL(last) == next_block_index) {
			last->prev->next = last->next;
			last->next->prev = last->prev;
			continue;
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
	garena_free(&scratch);

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

	Function **functions = NULL;
	size_t function_cnt = 0;

	if (argc < 2) {
		goto end;
	}

	Str source = read_file(&ec, arena, argv[1]);
	Module *module = parse_source(&ec, arena, source);
	functions = module->functions;
	function_cnt = module->function_cnt;

	RegAllocState ras;
	reg_alloc_state_init(&ras, arena);
	GArena labels = {0};

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
		translate_function(arena, &labels, functions[i]);
		calculate_def_use_info(functions[i]->mfunc);
		print_mfunction(stderr, functions[i]->mfunc);
		peephole(functions[i]->mfunc, arena);
		print_mfunction(stderr, functions[i]->mfunc);
		reg_alloc_function(&ras, functions[i]->mfunc);
		print_mfunction(stderr, functions[i]->mfunc);
		calculate_def_use_info(functions[i]->mfunc);
		peephole(functions[i]->mfunc, arena);
		print_mfunction(stderr, functions[i]->mfunc);
		//*/
		//peephole(functions[i]->mfunc, arena);
	}

	///*
	reg_alloc_state_free(&ras);

	printf("\tdefault rel\n\n");

	printf("\tsection .data\n");
	for (size_t i = 0; i < module->global_cnt; i++) {
		Global *global = module->globals[i];
		if (global->init) {
			//printf("\talign 8\n");
			print_str(stdout, global->name);
			printf(":\n");
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

	for (size_t i = 0; i < function_cnt; i++) {
		Function *function = functions[i];
		for (size_t b = 0; b < function->block_cap; b++) {
			Block *block = function->blocks[b];
			free(block->preds_);
		}
		free(function->blocks);
		free(function->post_order);
		mfunction_free(function->mfunc);
	}
	garena_free(&labels);

	arena_free(&ec.arena);
	arena_free(arena);
	return ec.error_head ? EXIT_FAILURE : EXIT_SUCCESS;
}
