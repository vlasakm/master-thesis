#include "ir.h"
#include "utils.h"

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

void
value_init(Value *value, ValueKind kind, Type *type)
{
	*value = (Value) { .kind = kind, .type = type };
}

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

size_t
value_arg_cnt(Value *value)
{
	switch (value->kind) {
	case VK_CALL: {
		Operation *op = (void *) value;
		return 1 + type_function_param_cnt(op->operands[0]->type);
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
	size_t operand_cnt = value_arg_cnt(value);
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
	case VK_FUNCTION: {
		Function *fun = (void *) operand;
		print_str(f, fun->name);
		break;
	}
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

size_t
number_values(Function *function, size_t start_index)
{
	size_t i = start_index;
	for (size_t b = function->block_cnt; b--;) {
		Block *block = function->post_order[b];
		for (Value *v = block->base.next; v != &block->base; v = v->next) {
			v->index = i++;
		}
	}
	function->value_cnt = i;
	return i;
}

void
print_value(FILE *f, Value *v)
{
	switch (v->kind) {
	case VK_FUNCTION: {
		Function *fun = (void *) v;
		print_str(f, fun->name);
		break;
	}
	case VK_GLOBAL: {
		Global *g = (void *) v;
		print_str(f, g->name);
		break;
	}
	case VK_CONSTANT: {
		Constant *k = (void *) v;
		fprintf(f, "%"PRIi64, k->k);
		break;
	}
	case VK_ALLOCA: {
		Alloca *a = (void *) v;
		fprintf(f, "alloca %zu\n", a->size);
		break;
	}
	case VK_ARGUMENT: {
		Argument *a = (void *) v;
		fprintf(f, "argument %zu\n", a->index);
		break;
	}
	case VK_GET_MEMBER_PTR: {
		Operation *operation = (void *) v;
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
validate_function(Function *function)
{
#ifndef NDEBUG
	for (size_t j = function->block_cnt; j--;) {
		Block *block = function->post_order[j];
		assert(block->base.parent == &function->base);
		value_is_terminator(block->base.prev);

		FOR_EACH_BLOCK_PRED(block, pred) {
			FOR_EACH_BLOCK_SUCC(*pred, s) {
				if (*s == block) {
					goto pred_ok;
				}
			}
			assert(false);
		}
		pred_ok:;
		FOR_EACH_BLOCK_SUCC(block, succ) {
			FOR_EACH_BLOCK_PRED(*succ, p) {
				if (*p == block) {
					goto succ_ok;
				}
			}
			assert(false);
		}
		succ_ok:;

		for (Value *v = block->base.next; v != &block->base; v = v->next) {
			assert(v->prev);
			assert(v->next);
			assert(v->prev->next == v);
			assert(v->next->prev == v);
			assert(v->parent == &block->base);
		}
	}
#endif // NDEBUG
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
	validate_function(function);
}

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

Field *
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

