#include "ir.h"
#include "utils.h"

char *value_kind_repr[] = {
#define REPR(kind, repr, ...) repr,
VALUE_KINDS(REPR)
#undef REPR
};

void
value_init(Value *value, ValueKind kind, Type *type)
{
	*value = (Value) { .kind = kind, .type = type };
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
replace_value(Value *old, Value *new)
{
	old->prev->next = new;
	old->next->prev = new;
	new->next = old->next;
	new->prev = old->prev;
}

void
change_to_identity(Operation *operation, Value *source)
{
	assert(value_operand_cnt(&operation->base) >= 1);
	operation->base.kind = VK_IDENTITY;
	operation->operands[0] = source;
}

bool
value_is_terminator(Value *value)
{
	switch (VK(value)) {
	case VK_JUMP:
	case VK_BRANCH:
	case VK_RET:
		return true;
	case VK_BLOCK:
	     // fallthrough
	default:
		return false;
	}
}

Operation *
create_operation(Arena *arena, ValueKind kind, Type *type, size_t operand_cnt)
{
	Operation *op = arena_alloc(arena, sizeof(*op) + sizeof(op->operands[0]) * operand_cnt);
	value_init(&op->base, kind, type);
	op->base.kind = kind;
	op->base.type = type;
	op->base.operand_cnt = operand_cnt;
	return op;
}

Value *
create_unary(Arena *arena, ValueKind kind, Type *type, Value *arg)
{
	Operation *op = create_operation(arena, kind, type, 1);
	op->operands[0] = arg;
	return &op->base;
}

Value NOP = { .type = &TYPE_VOID, .kind = VK_NOP };

Operation *
insert_phi(Arena *arena, Block *block, Type *type)
{
	// Find the position where to insert the phi. It should be inserted as
	// the last phi in the group of phis at the start of a block.
	Value *non_phi;
	for (non_phi = block->base.next; non_phi != &block->base; non_phi = non_phi->next) {
		if (VK(non_phi) != VK_PHI) {
			break;
		}
	}
	Operation *phi = arena_alloc(arena, sizeof(*phi) + sizeof(phi->operands[0]) * block_pred_cnt(block));
	// Due to possible cyclic nature of phis, the operands may be read as
	// their values are being deteremined. As we don't want unitialized
	// memory to be read, we initialize the operands iwth dummy NOPs.
	for (size_t i = 0; i < block_pred_cnt(block); i++) {
	     phi->operands[i] = &NOP;
	}
	value_init(&phi->base, VK_PHI, type);
	phi->base.index = ((Function *) block->base.parent)->value_cnt++;
	phi->base.parent = &block->base;
	phi->base.operand_cnt = block_pred_cnt(block);
	prepend_value(non_phi, &phi->base);
	return phi;
}


Block *
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
	// 1 is reasonable default if not overriden by the caller
	block->depth = 1;
	// Functions grow in powers of two.
	if (!(function->block_cap & (function->block_cap - 1))) {
		GROW_ARRAY(function->blocks, function->block_cap ? function->block_cap * 2 : 4);
	}
	function->blocks[function->block_cap++] = block;
	return block;
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
	default:
		return 0;
	}
}

Block **
block_succs(Block *block)
{
	Value *last = block->base.prev;
	switch (VK(last)) {
	case VK_JUMP:
		// Jump has just the one succesor operand.
		return (Block **) &((Operation *) last)->operands[0];
	case VK_BRANCH:
		// Branch has the condition and then two successor operands.
		return (Block **) &((Operation *) last)->operands[1];
	default:
		assert(block_succ_cnt(block) == 0);
		return NULL;
	}
}

void
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

void
block_add_pred_to_succs(Block *block)
{
	FOR_EACH_BLOCK_SUCC(block, succ) {
		block_add_pred(*succ, block);
	}
}

size_t
block_index_of_pred(Block *succ, Block *pred)
{
	size_t i = 0;
	FOR_EACH_BLOCK_PRED(succ, p) {
		if (*p == pred) {
			return i;
		}
		i++;
	}
	UNREACHABLE();
}

void
append_to_block(Block *block, Value *new)
{
	if (!block) {
		return;
	}
	prepend_value(&block->base, new);
	new->parent = &block->base;
}

size_t
value_operand_cnt(Value *value)
{
	return value->operand_cnt;
}

Value **
value_operands(Value *value)
{
	return ((Operation *) value)->operands;
}

void
print_operand(FILE *f, Value *operand)
{
	switch (operand->kind) {
	case VK_BLOCK:
	case VK_FUNCTION:
	case VK_GLOBAL:
	case VK_CONSTANT:
	case VK_STRING:
		print_value(f, operand);
		break;
	default:
		fprintf(f, "v%zu", operand->index);
		break;
	}
}

size_t
number_values(Function *function, size_t start_index)
{
	size_t index = start_index;
	size_t param_cnt = type_function_param_cnt(function->base.type);
	for (size_t i = 0; i < param_cnt; i++) {
		function->args[i].base.index = index++;
		function->args[i].index = i;
	}
	for (size_t b = function->block_cnt; b--;) {
		Block *block = function->post_order[b];
		FOR_EACH_IN_BLOCK(block, v) {
			v->index = index++;
		}
	}
	function->value_cnt = index;
	return index;
}

void
print_value(FILE *f, Value *v)
{
	switch (v->kind) {
	case VK_BLOCK:
		fprintf(f, "block%zu", v->index);
		break;
	case VK_FUNCTION: {
		Function *fun = (void *) v;
		print_str(f, fun->name);
		break;
	}
	case VK_GLOBAL: {
		Global *global = (void *) v;
		print_str(f, global->name);
		break;
	}
	case VK_CONSTANT: {
		Constant *k = (void *) v;
		fprintf(f, "%"PRIi64, k->k);
		break;
	}
	case VK_STRING: {
		fprintf(f, "$str%zu", v->index);
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
		print_operand(f, operation->operands[0]);
		Field *field = get_member(v);
		fprintf(f, " %.*s\n", (int) field->name.len, field->name.str);
		break;
	}
	default: {
		fprintf(f, "%s ", value_kind_repr[v->kind]);
		size_t i = 0;
		FOR_EACH_OPERAND(v, operand) {
			if (i != 0) {
				fprintf(f, ", ");
			}
			print_operand(f, *operand);
			i++;
		}
		fprintf(f, "\n");
		break;
	}
	}
}

Function *
create_function(Arena *arena, Str name, Type *type)
{
	Function *function = arena_alloc(arena, sizeof(*function));
	*function = (Function) {0};
	function->name = name;
	value_init(&function->base, VK_FUNCTION, type_pointer(arena, type));
	return function;
}

void
validate_function(Function *function)
{
#ifndef NDEBUG
	for (size_t j = function->block_cnt; j--;) {
		Block *block = function->post_order[j];
		assert(block->base.parent == &function->base);

		FOR_EACH_IN_BLOCK(block, v) {
			assert(v->prev);
			assert(v->next);
			assert(v->prev->next == v);
			assert(v->next->prev == v);
			assert(v->parent == &block->base);
			if (v != block->base.prev) {
				assert(!value_is_terminator(v));
			} else {
				assert(value_is_terminator(v));
			}
		}

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
	}
#endif // NDEBUG
}

void
print_index_type_value(FILE *f, Value *v)
{
	if (v->type->kind != TY_VOID) {
		print_operand(f, v);
		fprintf(f, ": ");
		print_type(f, v->type);
		fprintf(f, " = ");
	}
	print_value(f, v);
}

void
print_function(FILE *f, Function *function)
{
	print_str(f, function->name);
	fprintf(f, ":\n");
	size_t param_cnt = type_function_param_cnt(function->base.type);
	for (size_t i = 0; i < param_cnt; i++) {
		Value *arg = &function->args[i].base;
		fprintf(f, "\t");
		print_index_type_value(f, arg);
	}
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

		FOR_EACH_IN_BLOCK(block, v) {
			fprintf(f, "\t");
			print_index_type_value(f, v);
		}
	}
	validate_function(function);
}

bool
function_is_fully_defined(Function *function)
{
	return function->entry != NULL;
}

static void dfs(Block *block, size_t *index, Block **post_order);

void
compute_postorder(Function *function)
{
	// Reserve sufficient space in the post order array
	GROW_ARRAY(function->post_order, function->block_cap);
	// Reset the number of blocks in the post order array to zero. Depth
	// first search will only count reachable blocks, thus this value will
	// become the number of reachable blocks (in the post order array).
	function->block_cnt = 0;
	// Perform Depth First Search on the blocks, starting from entry block
	// and following all successors.
	dfs(function->entry, &function->block_cnt, function->post_order);
	// Reset the `visited` flag on blocks, so we can comput post odrer in
	// the same way next time.
	for (size_t b = function->block_cnt; b--;) {
		function->post_order[b]->base.visited = 0;
	}
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
