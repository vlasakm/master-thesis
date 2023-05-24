#include "ir.h"

void
get_uses(Function *function)
{
	GROW_ARRAY(function->uses, 2 * function->value_cnt);
	ZERO_ARRAY(function->uses, 2 * function->value_cnt);
	for (size_t b = 0; b < function->block_cnt; b++) {
		Block *block = function->post_order[b];
		FOR_EACH_IN_BLOCK(block, v) {
			FOR_EACH_OPERAND(v, operand_) {
				Value *operand = *operand_;
				// Skip getting uses of things like functions,
				// constants, etc.
				if (operand->index == 0) {
					continue;
				}
				// Add to `operand`'s uses the use in `v`.
				GArena *uses = &function->uses[operand->index];
				garena_push_value(uses, Value *, v);
			}
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
analyze_optimizable_allocas(Function *function)
{
	Block *entry = function->entry;
	FOR_EACH_IN_BLOCK(entry, v) {
		if (v->kind != VK_ALLOCA) {
			continue;
		}
		Alloca *alloca = (void *) v;
		Value **uses = garena_array(&function->uses[v->index], Value *);
		size_t use_cnt = garena_cnt(&function->uses[v->index], Value *);
		print_value(stderr, v);
		for (size_t i = 0; i < use_cnt; i++) {
			Value *use = uses[i];
			if (VK(use) == VK_STORE && STORE_ADDR(use) == v && STORE_VALUE(use) != v) {
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

Value *read_variable(ValueNumberingState *vns, Block *block, Value *variable);

void
add_use(Function *function, Value *what, Value *where)
{
	GArena *uses = &function->uses[what->index];
	garena_push_value(uses, Value *, where);
}

void
remove_use(Function *function, Value *what, Value *where, bool assert)
{
	if (what->index == 0) {
		return;
	}
	GArena *guses = &function->uses[what->index];
	size_t use_cnt = garena_cnt(guses, Value *);
	Value **uses = garena_array(guses, Value *);
	for (size_t i = 0; i < use_cnt; i++) {
		if (uses[i] == where) {
			uses[i] = uses[--use_cnt];
			guses->pos -= sizeof(Value *);
			return;
		}
	}
	if (assert) {
		UNREACHABLE();
	}
}

void
replace_by(Function *function, Value *old, Value *new)
{
	GArena *guses = &function->uses[old->index];
	size_t use_cnt = garena_cnt(guses, Value *);
	Value **uses = garena_array(guses, Value *);
	for (size_t i = 0; i < use_cnt; i++) {
		Value *use = uses[i];
		FOR_EACH_OPERAND(use, operand) {
			if (*operand == old) {
				*operand = new;
			}
		}
		add_use(function, new, use);
	}
}

void
remove_value_and_uses_of_operands(Function *function, Value *where)
{
	FOR_EACH_OPERAND(where, operand) {
		remove_use(function, *operand, where, true);
	}
	remove_value(where);
}


Value *
try_remove_trivial_phi(Arena *arena, Function *function, Value *phi)
{
	// Simplify trivial phis like:
	//
	//     v30 = phi v20, v20
	//
	// or
	//     v32 = phi v32, v19
	//
	// and use the value (v20, v19 in the examples above) instead. Since the
	// values may also be phis which might become trivial, also investigate
	// them. For this we need the uses, which we keep updated.

	Value *same = NULL;
	FOR_EACH_OPERAND(phi, op) {
		if (*op == same || *op == phi) {
			continue;
		} else if (same) {
			return phi;
		}
		same = *op;
	}
	if (!same) {
		Operation *undefined = create_operation(arena, (Block *) phi->parent, VK_UNDEFINED, phi->type, 0);
		same = &undefined->base;
	}
	remove_value_and_uses_of_operands(function, phi);
	replace_by(function, phi, same);
	GArena *guses = &function->uses[phi->index];
	size_t use_cnt = garena_cnt(guses, Value *);
	Value **uses = garena_array(guses, Value *);
	for (size_t i = 0; i < use_cnt; i++) {
		Value *use = uses[i];
		if (VK(use) == VK_PHI) {
			try_remove_trivial_phi(arena, function, use);
		}
	}
	return same;
}

Value *
add_phi_operands(ValueNumberingState *vns, Operation *phi, Block *block, Value *variable)
{
	size_t i = 0;
	FOR_EACH_BLOCK_PRED(block, pred) {
		Value *value = read_variable(vns, *pred, variable);
		phi->operands[i++] = value;
		add_use(vns->function, value, &phi->base);
	}
	return try_remove_trivial_phi(vns->arena, vns->function, &phi->base);
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
		value = add_phi_operands(vns, phi, block, variable);
		block->pending = false;
	}
	// Memoize
	write_variable(vns, block, variable, value);
	return value;
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
do_value_numbering(Arena *arena, Function *function)
{
	size_t block_cnt = function->block_cnt;
	// Overallocate, so we can store information also for newly introduced
	// phi nodes.
	size_t value_cnt = 2 * function->value_cnt;

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
		FOR_EACH_IN_BLOCK(block, v) {
			switch (VK(v)) {
			case VK_ALLOCA:
				if (is_optimizable_alloca(v)) {
					remove_value(v);
					continue;
				}
				break;
			case VK_LOAD:
				if (is_optimizable_alloca(LOAD_ADDR(v))) {
					Value *val = read_variable(vns, block, LOAD_ADDR(v));
					vns->canonical[VINDEX(v)] = val;
					remove_value_and_uses_of_operands(function, v);
					continue;
				}
				break;
			case VK_STORE:
				if (is_optimizable_alloca(STORE_ADDR(v))) {
					write_variable(vns, block, STORE_ADDR(v), STORE_VALUE(v));
					remove_value_and_uses_of_operands(function, v);
					continue;
				}
			default:
				break;
			}
			FOR_EACH_OPERAND(v, operand) {
				Value *canonical = vns->canonical[VINDEX(*operand)];
				if (canonical) {
					Value *old_operand = *operand;
					*operand = canonical;
					remove_use(function, old_operand, v, true);
					add_use(function, canonical, v);
				}
			}
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
value_numbering(Arena *arena, Function *function)
{
	get_uses(function);
	analyze_optimizable_allocas(function);
	do_value_numbering(arena, function);
	free_uses(function);
	validate_function(function);
}
