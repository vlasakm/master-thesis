#include "parser.h"
#include "table.h"
#include "environment.h"

#include "lexer.c"

typedef struct {
	bool lvalue;
	Value *value;
} CValue;

Value NOP = { .type = &TYPE_VOID, .kind = VK_NOP };

static Type *
typeof(CValue cvalue)
{
	Type *type = cvalue.value->type;
	if (cvalue.lvalue) {
		assert(type_is_pointer(type));
		return pointer_child(type);
	} else {
		return type;
	}
}

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
	size_t loop_nesting_depth;
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
add_block(Parser *parser)
{
	Block *block = create_block(parser->arena, parser->current_function);
	block->depth = parser->loop_nesting_depth;
	return block;
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
switch_to_block(Parser *parser, Block *new_block)
{
	if (parser->current_block) {
		if (!parser->had_error) {
			assert(value_is_terminator(parser->current_block->base.prev));
		}
		block_add_pred_to_succs(parser->current_block);
	}
	parser->current_block = new_block;
}

static void
add_jump(Parser *parser, Block *destination)
{
	if (parser->current_block) {
		assert(!value_is_terminator(parser->current_block->base.prev));
	}
	add_unary(parser, VK_JUMP, &TYPE_VOID, &destination->base);
}

static void
add_cond_jump(Parser *parser, Value *cond, Block *true_block, Block *false_block)
{
	if (parser->current_block) {
		assert(!value_is_terminator(parser->current_block->base.prev));
	}
	Operation *op = add_operation(parser, VK_BRANCH, &TYPE_VOID, 3);
	op->operands[0] = cond;
	op->operands[1] = &true_block->base;
	op->operands[2] = &false_block->base;
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
as_rvalue(Parser *parser, CValue cvalue)
{
	if (cvalue.lvalue) {
		Value *lvalue = cvalue.value;
		assert(type_is_pointer(lvalue->type));
		Type *child = pointer_child(lvalue->type);
		return add_unary(parser, VK_LOAD, child, lvalue);
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
parse_type(Parser *parser, bool allow_void)
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
	default:
		type = &TYPE_VOID;
		parser_error(parser, token, false, "Unexpected token %s in type specifier", tok_repr[token.kind]);
	}

	while (try_eat(parser, TK_ASTERISK)) {
		type = type_pointer(parser->arena, type);
	}

	if (!allow_void && type == &TYPE_VOID) {
		parser_error(parser, token, false, "Type 'void' is not allowed here");
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
create_const(Parser *parser, Type *type, u64 value)
{
	Constant *k = arena_alloc(parser->arena, sizeof(*k));
	value_init(&k->base, VK_CONSTANT, type);
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
		return rvalue(create_const(parser, &TYPE_INT, value));
	}
	case TK_STRING: {
		NOT_IMPLEMENTED("string literals");
	}
	default:
		  UNREACHABLE();
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
	Type *new_type = parse_type(parser, true);
	eat(parser, TK_GREATER);
	eat(parser, TK_LPAREN);
	CValue cvalue = expression(parser);
	eat(parser, TK_RPAREN);

	if (new_type == &TYPE_VOID) {
		return rvalue(&NOP);
	}
	if (type_is_struct(typeof(cvalue))) {
		parser_error(parser, parser->lookahead, false, "Cannot cast struct");
	}

	Value *value = as_rvalue(parser, cvalue);
	if (type_is_pointer(new_type) && type_is_pointer(value->type)) {
		value->type = new_type;
	}
	return rvalue(value);
}

static CValue
inc_dec(Parser *parser, CValue carg, bool inc, bool pre)
{
	Type *arg_type = typeof(carg);

	if (type_is_struct(arg_type)) {
	}

	Value *arg_addr = as_lvalue(parser, carg, "Expected argument of increment/decrement to be an lvalue");
	Value *arg = as_rvalue(parser, carg);
	Value *res = &NOP;
	if (type_is_pointer(arg_type)) {
		Value *one = create_const(parser, &TYPE_INT, inc ? 1 : -1);
		res = add_binary(parser, VK_GET_INDEX_PTR, arg->type, arg, one);
	} else if (type_is_numeric(arg_type)) {
		Value *one = create_const(parser, &TYPE_INT, 1);
		res = add_binary(parser, inc ? VK_ADD : VK_SUB, arg_type, arg, one);
	} else {
		parser_error(parser, parser->lookahead, false, "Cannot increment/decrement non-numeric, non-pointer value");
	}

	add_binary(parser, VK_STORE, &TYPE_VOID, arg_addr, res);

	return rvalue(pre ? res : arg);
}

static CValue
pre(Parser *parser)
{
	bool inc = discard(parser).kind == TK_PLUS_PLUS;
	CValue carg = expression_bp(parser, 14);
	return inc_dec(parser, carg, inc, true);
}

static CValue
unop(Parser *parser)
{
	Token token = discard(parser);
	CValue carg = expression_bp(parser, 14);

	if (!type_is_numeric(typeof(carg))) {
		parser_error(parser, parser->lookahead, false, "Unary arithmetic not on non-numeric type is not allowed");
	}

	Value *arg = as_rvalue(parser, carg);

	Value *result;
	switch (token.kind) {
	case TK_PLUS:
		result = arg;
		break;
	case TK_MINUS:
		result = add_unary(parser, VK_NEG, arg->type, arg);
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

	if (!type_is_pointer(typeof(carg))) {
		parser_error(parser, parser->lookahead, false, "Cannot dereference non-pointer");
	}

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

	if (!type_is_integral(typeof(carg))) {
		parser_error(parser, parser->lookahead, false, "Logical not on non-integral type is not allowed");
	}

	Value *arg = as_rvalue(parser, carg);
	Value *zero = create_const(parser, arg->type, 0);
	return rvalue(add_binary(parser, VK_EQ, arg->type, arg, zero));
}

static CValue
bitnot(Parser *parser)
{
	eat(parser, TK_TILDE);
	CValue carg = expression_bp(parser, 14);

	if (type_is_integral(typeof(carg))) {
		parser_error(parser, parser->lookahead, false, "Bitwise not on non-integral type is not allowed");
	}

	Value *arg = as_rvalue(parser, carg);
	return rvalue(add_unary(parser, VK_NOT, arg->type, arg));
}

static CValue
cmp(Parser *parser, CValue cleft, int rbp)
{
	TokenKind tok = discard(parser).kind;
	CValue cright = expression_bp(parser, rbp);

	Type *tleft = typeof(cleft);
	Type *tright = typeof(cright);
	if (!type_is_numeric(tleft) || !types_compatible(tleft, tright)) {
		parser_error(parser, parser->lookahead, false, "Cannot compare values of incompatible / non-integral types");
	}

	Value *left = as_rvalue(parser, cleft);
	Value *right = as_rvalue(parser, cright);
	ValueKind kind;
	switch (tok) {
	case TK_EQUAL_EQUAL:   kind = VK_EQ;  break;
	case TK_BANG_EQUAL:    kind = VK_NEQ; break;
	case TK_LESS:          kind = VK_SLT;  break;
	case TK_LESS_EQUAL:    kind = VK_SLEQ; break;
	case TK_GREATER:       kind = VK_SGT;  break;
	case TK_GREATER_EQUAL: kind = VK_SGEQ; break;
	default: UNREACHABLE();
	}
	return rvalue(add_binary(parser, kind, tleft, left, right));
}

static CValue
binop(Parser *parser, CValue cleft, int rbp)
{
	TokenKind tok = discard(parser).kind;
	CValue cright = expression_bp(parser, rbp);

	Type *tleft = typeof(cleft);
	Type *tright = typeof(cright);
	Value *left = as_rvalue(parser, cleft);
	Value *right = as_rvalue(parser, cright);
	ValueKind kind = VK_UNDEFINED;
	if (type_is_numeric(tleft) && types_compatible(tleft, tright)) {
		switch (tok) {
		case TK_PLUS:     kind = VK_ADD; break;
		case TK_MINUS:    kind = VK_SUB; break;
		case TK_ASTERISK: kind = VK_MUL; break;
		case TK_SLASH:    kind = VK_SDIV; break;
		case TK_PERCENT:  kind = VK_SREM; break;
		default: UNREACHABLE();
		}
	} else if (type_is_pointer(tleft) && type_is_integral(tright)) {
		kind = VK_GET_INDEX_PTR;
		switch (tok) {
		case TK_PLUS:
			break;
		case TK_MINUS:
			right = add_unary(parser, VK_NEG, right->type, right);
			break;
		default:
			parser_error(parser, parser->lookahead, false, "Invalid operator for pointer arithmetic");
		}
	} else {
		parser_error(parser, parser->lookahead, false, "Binary arithmetic on values of incompatible / non-numeric types is not allowed");
	}

	return rvalue(add_binary(parser, kind, tleft, left, right));
}

static CValue
bitbinop(Parser *parser, CValue cleft, int rbp)
{
	TokenKind tok = discard(parser).kind;
	CValue cright = expression_bp(parser, rbp);

	Type *tleft = typeof(cleft);
	Type *tright = typeof(cright);
	if (!type_is_numeric(tleft) || !types_compatible(tleft, tright)) {
		parser_error(parser, parser->lookahead, false, "Bitwise binary arithmetic on values of incompatible / non-integral types is not allowed");
	}

	Value *left = as_rvalue(parser, cleft);
	Value *right = as_rvalue(parser, cright);
	ValueKind kind;
	switch (tok) {
	case TK_AMP:             kind = VK_AND; break;
	case TK_BAR:             kind = VK_OR;  break;
	case TK_LESS_LESS:       kind = VK_SHL; break;
	case TK_GREATER_GREATER: kind = VK_SAR; break;
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

	if (!type_is_pointer(typeof(cleft))) {
		parser_error(parser, parser->lookahead, false, "Expected indexing to subscript a pointer");
	}
	if (!type_is_integral(typeof(cright))) {
		parser_error(parser, parser->lookahead, false, "Expected index to be an integer");
	}

	Value *left = as_rvalue(parser, cleft);
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
	Operation *call = create_operation(parser->arena, parser->current_block, VK_CALL, fun_type->ret_type, 1 + argument_cnt);

	size_t i = 0;
	call->operands[i++] = left;
	while (!try_eat(parser, TK_RPAREN)) {
		CValue carg = expression_no_comma(parser);
		if (type_is_struct(typeof(carg))) {
			parser_error(parser, parser->lookahead, false, "Passing structs as arguments is currently not allowed");
		}
		if (i - 1 < argument_cnt) {
			call->operands[i] = as_rvalue(parser, carg);
			if (!types_compatible(call->operands[i]->type, fun_type->params[i - 1].type)) {
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
	append_to_block(parser->current_block, &call->base);
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
	if (!type_is_pointer(struct_type)) {
		parser_error(parser, parser->prev, false, "Member access with '->' on non-pointer");
		return lvalue(&NOP);
	}
	struct_type = ((PointerType *) struct_type)->child;
	if (!type_is_struct(struct_type)) {
		parser_error(parser, parser->prev, false, "Member access on non-struct");
	}
	if (!type_is_complete(struct_type)) {
		parser_error(parser, parser->prev, false, "Member access on incomplete struct type");
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
	parser_error(parser, parser->prev, false, "Field %.*s not found", (int) name.len, name.str);
found:;
	field_type = type_pointer(parser->arena, field_type);
	Value *member_index = create_const(parser, &TYPE_INT, i);
	Value *member_access = add_binary(parser, VK_GET_MEMBER_PTR, field_type, left, member_index);
	return lvalue(member_access);
}

static CValue
ternop(Parser *parser, CValue ccond, int rbp)
{
	eat(parser, TK_QUESTION_MARK);

	Block *true_block = add_block(parser);
	Block *false_block = add_block(parser);
	Block *after_block = add_block(parser);

	Value *cond = as_rvalue(parser, ccond);
	add_cond_jump(parser, cond, true_block, false_block);

	// Parse the true branch
	switch_to_block(parser, true_block);
	CValue cleft = expression(parser);
	Value *left = as_rvalue(parser, cleft);
	eat(parser, TK_COLON);
	add_jump(parser, after_block);

	// Parse the false branch
	switch_to_block(parser, false_block);
	CValue cright = expression_bp(parser, rbp);
	Value *right = as_rvalue(parser, cright);
	add_jump(parser, after_block);

	if (left->type != right->type) {
		parser_error(parser, parser->lookahead, false, "Expected both sides of short circuiting operation to have the same type");
	}

	// Merge
	switch_to_block(parser, after_block);
	assert(block_pred_cnt(after_block) == 2);
	assert(block_preds(after_block)[0] == true_block);
	assert(block_preds(after_block)[1] == false_block);
	Operation *phi = insert_phi(parser->arena, after_block, left->type);
	phi->operands[0] = left;
	phi->operands[1] = right;
	return rvalue(&phi->base);
}

static CValue
shortcirc(Parser *parser, CValue cleft, int rbp)
{
	TokenKind tok = discard(parser).kind;
	Value *left = as_rvalue(parser, cleft);
	Block *left_block = parser->current_block;
	Block *right_block = add_block(parser);
	Block *after_block = add_block(parser);
	switch (tok) {
	case TK_AMP_AMP:
		add_cond_jump(parser, left, right_block, after_block);
		break;
	case TK_BAR_BAR:
		add_cond_jump(parser, left, after_block, right_block);
		break;
	default:
		UNREACHABLE();
	}

	// Compile the right hand side into its own conditionally executed block
	switch_to_block(parser, right_block);
	CValue cright = expression_bp(parser, rbp);
	Value *right = as_rvalue(parser, cright);
	add_jump(parser, after_block);

	if (left->type != right->type) {
		parser_error(parser, parser->lookahead, false, "Expected both sides of short circuiting operation to have the same type");
	}

	// Merge both branches
	switch_to_block(parser, after_block);
	assert(block_pred_cnt(after_block) == 2);
	assert(block_preds(after_block)[0] == left_block);
	assert(block_preds(after_block)[1] == right_block);
	Operation *phi = insert_phi(parser->arena, after_block, left->type);
	phi->operands[0] = left;
	phi->operands[1] = right;
	return rvalue(&phi->base);
}

static CValue
post(Parser *parser, CValue cleft, int rbp)
{
	bool inc = discard(parser).kind == TK_PLUS_PLUS;
	return inc_dec(parser, cleft, inc, false);
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
	add_binary(parser, VK_STORE, &TYPE_VOID, left, right);
	return lvalue(left);
}

static Value *
condition(Parser *parser)
{
	CValue ccond = expression(parser);
	Value *cond = as_rvalue(parser, ccond);
	if (!type_is_numeric(cond->type) && !type_is_pointer(cond->type)) {
		parser_error(parser, parser->prev, false, "Condition must have numeric or pointer type");
	}
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
	parser->loop_nesting_depth++;
	statement(parser);
	parser->loop_nesting_depth--;
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
		add_jump(parser, cond_block);

		// Parse condition
		switch_to_block(parser, cond_block);
		eat(parser, TK_LPAREN);
		Value *cond = condition(parser);
		eat(parser, TK_RPAREN);
		add_cond_jump(parser, cond, true_block, false_block);

		// Parse the true branch
		switch_to_block(parser, true_block);
		statement(parser);
		add_jump(parser, after_block);

		// Parse the (optional) false branch
		switch_to_block(parser, false_block);
		if (try_eat(parser, TK_ELSE)) {
			statement(parser);
		}
		add_jump(parser, after_block);

		switch_to_block(parser, after_block);
		break;
	}
	case TK_SWITCH: {
		NOT_IMPLEMENTED("switch parsing");
		break;
	}
	case TK_WHILE: {
		eat(parser, TK_WHILE);
		Block *cond_block = add_block(parser);
		Block *body_block = add_block(parser);
		Block *after_block = add_block(parser);
		add_jump(parser, cond_block);

		// Parse the condition
		switch_to_block(parser, cond_block);
		eat(parser, TK_LPAREN);
		Value *cond = condition(parser);
		eat(parser, TK_RPAREN);
		add_cond_jump(parser, cond, body_block, after_block);

		// Parse the loop body
		switch_to_block(parser, body_block);
		loop_body(parser, cond_block, after_block);
		add_jump(parser, cond_block);

		cond_block->depth++;
		body_block->depth++;

		switch_to_block(parser, after_block);
		break;
	}
	case TK_DO: {
		eat(parser, TK_DO);
		Block *body_block = add_block(parser);
		Block *cond_block = add_block(parser);
		Block *after_block = add_block(parser);
		add_jump(parser, body_block);

		// Parse the loop body
		switch_to_block(parser, body_block);
		loop_body(parser, cond_block, after_block);
		add_jump(parser, cond_block);

		// Parse the condition
		switch_to_block(parser, cond_block);
		eat(parser, TK_WHILE);
		eat(parser, TK_LPAREN);
		Value *cond = condition(parser);
		eat(parser, TK_RPAREN);
		eat(parser, TK_SEMICOLON);
		add_cond_jump(parser, cond, body_block, after_block);

		cond_block->depth++;
		body_block->depth++;

		switch_to_block(parser, after_block);
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
		add_jump(parser, init_block);

		// Parse the (optional) initializer
		switch_to_block(parser, init_block);
		if (peek(parser) != TK_SEMICOLON) {
			expression_or_variable_declaration(parser);
		}
		eat(parser, TK_SEMICOLON);
		add_jump(parser, cond_block);

		// Parse the (optional) condition
		switch_to_block(parser, cond_block);
		if (peek(parser) != TK_SEMICOLON) {
			Value *cond = condition(parser);
			add_cond_jump(parser, cond, body_block, after_block);
		} else {
			add_jump(parser, body_block);
		}
		eat(parser, TK_SEMICOLON);

		// Parse the (optional) "increment" expression
		switch_to_block(parser, incr_block);
		if (peek(parser) != TK_RPAREN) {
			expression(parser);
		}
		eat(parser, TK_RPAREN);
		add_jump(parser, cond_block);

		// Parse the loop body
		switch_to_block(parser, body_block);
		loop_body(parser, incr_block, after_block);
		add_jump(parser, incr_block);

		cond_block->depth++;
		incr_block->depth++;
		body_block->depth++;

		switch_to_block(parser, after_block);
		break;
	}
	case TK_BREAK: {
		Token tok = discard(parser);
		if (parser->break_block) {
			add_jump(parser, parser->break_block);
		} else {
			parser_error(parser, tok, true, "'break' outside of loop or switch");
		}
		eat(parser, TK_SEMICOLON);
		// Following code is unreachable.
		switch_to_block(parser, NULL);
		break;
	}
	case TK_CONTINUE: {
		Token tok = discard(parser);
		if (parser->continue_block) {
			add_jump(parser, parser->continue_block);
		} else {
			parser_error(parser, tok, true, "'continue' outside of loop");
		}
		eat(parser, TK_SEMICOLON);
		// Following code is unreachable.
		switch_to_block(parser, NULL);
		break;
	}
	case TK_RETURN: {
		Token tok = discard(parser);
		Type *return_type = ((FunctionType *) parser->current_function->base.type)->ret_type;
		if (peek(parser) != TK_SEMICOLON) {
			Value *value = as_rvalue(parser, expression(parser));
			if (!types_compatible(value->type, return_type)) {
				parser_error(parser, tok, false, "Type of 'return'ed value does not match nominal type");
			}
			add_unary(parser, VK_RET, &TYPE_VOID, value);
		} else if (return_type == &TYPE_VOID) {
			add_operation(parser, VK_RETVOID, &TYPE_VOID, 0);
		} else {
			parser_error(parser, tok, false, "Expected some value to be 'return'ed");
		}
		eat(parser, TK_SEMICOLON);
		// Following code is unreachable.
		switch_to_block(parser, NULL);
		break;
	}
	case TK_SEMICOLON: {
		// An empty statement consisting of only semicolon.
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
function_declaration(Parser *parser, Str fun_name, FunctionType *fun_type)
{
	Parameter *params = fun_type->params;
	size_t param_cnt = fun_type->param_cnt;

	Function *function = arena_alloc(parser->arena, sizeof(*function));
	*function = (Function) {0};
	function->name = fun_name;
	value_init(&function->base, VK_FUNCTION, (Type *) fun_type);

	// Prepare for the arguments and function body.
	env_define(&parser->env, fun_name, &function->base);
	eat(parser, TK_LBRACE);
	parser->current_function = function;
	function->block_cnt = 0;
	function->entry = add_block(parser);
	// Can't use `switch_to_block` here, because this is the first block and
	// we have to get the thing going somehow.
	parser->current_block = function->entry;

	env_push(&parser->env);

	// Prepare arguments
	Argument *args = arena_alloc(parser->arena, param_cnt * sizeof(args[0]));
	for (size_t i = 0; i < param_cnt; i++) {
		Argument *arg = &args[i];
		value_init(&arg->base, VK_ARGUMENT, params[i].type);
	}
	for (size_t i = 0; i < param_cnt; i++) {
		Value *arg = &args[i].base;
		Value *addr = add_alloca(parser, params[i].type);
		add_binary(parser, VK_STORE, &TYPE_VOID, addr, arg);
		env_define(&parser->env, params[i].name, addr);
	}
	function->args = args;

	// Parse function body
	statements(parser);

	// Complete the function
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
	Type *type = parse_type(parser, false);
	Str name = eat_identifier(parser);
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
struct_declaration(Parser *parser)
{
	eat(parser, TK_STRUCT);
	Str tag = eat_identifier(parser);

	Type *type = NULL;
	if (!table_get(&parser->type_env, tag, (void **) &type)) {
		type = type_struct_forward(parser->arena);
		table_insert(&parser->type_env, tag, type);
	}

	if (!try_eat(parser, TK_LBRACE)) {
		eat(parser, TK_SEMICOLON);
		return;
	}

	size_t start = garena_save(parser->scratch);
	while (!try_eat(parser, TK_RBRACE)) {
		Type *field_type = parse_type(parser, false);
		Str field_name = eat_identifier(parser);

		Field field = {
			.name = field_name,
			.type = field_type,
		};
		garena_push_value(parser->scratch, Field, field);
		eat(parser, TK_SEMICOLON);
	}
	eat(parser, TK_SEMICOLON);

	size_t field_cnt = garena_cnt_from(parser->scratch, start, Field);
	Field *fields = move_to_arena(parser->arena, parser->scratch, start, Field);
	type_struct_define(type, fields, field_cnt);
}

static FunctionType *
function_declarator(Parser *parser, Type *type, bool param_names)
{
	eat(parser, TK_LPAREN);
	size_t start = garena_save(parser->scratch);
	while (!try_eat(parser, TK_RPAREN)) {
		Type *param_type = parse_type(parser, false);
		Str param_name = STR("<anon>");
		if (param_names) {
			param_name = eat_identifier(parser);
		}
		Parameter param = { param_name, param_type };
		garena_push_value(parser->scratch, Parameter, param);
		if (!try_eat(parser, TK_COMMA)) {
			eat(parser, TK_RPAREN);
			break;
		}
	}
	size_t param_cnt = garena_cnt_from(parser->scratch, start, Parameter);
	Parameter *params = move_to_arena(parser->arena, parser->scratch, start, Parameter);
	return (FunctionType *) type_function(parser->arena, type, params, param_cnt);
}

static void
function_pointer_declaration(Parser *parser)
{
	eat(parser, TK_TYPEDEF);
	Type *type = parse_type(parser, true);
	eat(parser, TK_LPAREN);
	eat(parser, TK_ASTERISK);
	Str name = eat_identifier(parser);
	eat(parser, TK_RPAREN);
	type = &function_declarator(parser, type, false)->base;
	eat(parser, TK_SEMICOLON);

	table_insert(&parser->type_env, name, type);
}

static void
global_declarations(Parser *parser, Type *type, Str name)
{
	for (;;) {
		global_declaration(parser, name, type);
		if (try_eat(parser, TK_SEMICOLON)) {
			break;
		}
		eat(parser, TK_COMMA);
		type = parse_type(parser, false);
		name = eat_identifier(parser);
	}
}

static void
parse_program(Parser *parser)
{
	for (;;) {
		switch (peek(parser)) {
		case TK_EOF:
			return;
		case TK_STRUCT:
			struct_declaration(parser);
			continue;
		case TK_TYPEDEF:
			function_pointer_declaration(parser);
			continue;
		default:
			break;
		}
		Type *type = parse_type(parser, true);
		Str name = eat_identifier(parser);
		switch (peek(parser)) {
		case TK_LPAREN: {
			FunctionType *fun_type = function_declarator(parser, type, true);
			function_declaration(parser, name, fun_type);
			break;
		}
		default:
			if (type == &TYPE_VOID) {
				parser_error(parser, parser->prev, false, "Type 'void' is not allowed here");
			}
			global_declarations(parser, type, name);
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
		.loop_nesting_depth = 0,
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
