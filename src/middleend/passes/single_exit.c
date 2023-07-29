#include "../ir.h"

typedef struct {
	Block *block;
	Value *value;
} PendingPhi;

void
single_exit(Arena *arena, Function *function)
{
	bool ret_void = type_function_return_type(function->base.type) == &TYPE_VOID;

	GArena gphis = {0};
	for (size_t b = function->block_cnt; b--;) {
		Block *block = function->post_order[b];
		Value *value = NULL;
		switch (VK(block->base.prev)) {
		case VK_RET:
			if (!ret_void) {
				value = OPER(block->base.prev, 0);
			}
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

	for (size_t i = 0; i < phi_cnt; i++) {
		PendingPhi *phi = &phis[i];
		Block *pred = phi->block;
		Value *jump = create_unary(arena, VK_JUMP, &TYPE_VOID, &ret_block->base);
		jump->index = function->value_cnt++;
		jump->parent = &pred->base;
		remove_value(pred->base.prev);
		prepend_value(&pred->base, jump);
		block_add_pred(ret_block, pred);
	}

	Value *ret_inst;
	if (ret_void) {
		ret_inst = &create_operation(arena, VK_RET, &TYPE_VOID, 0)->base;
	} else {
		Type *type = phis[0].value->type;
		Operation *phi = insert_phi(arena, ret_block, type);
		phi->base.index = function->value_cnt++;
		for (size_t i = 0; i < phi_cnt; i++) {
			phi->operands[i] = phis[i].value;
		}
		ret_inst = create_unary(arena, VK_RET, &TYPE_VOID, &phi->base);
	}
	ret_inst->index = function->value_cnt++;
	ret_inst->parent = &ret_block->base;
	prepend_value(&ret_block->base, ret_inst);

	garena_free(&gphis);

	// Recompute function->post_order, since we invalidated it.
	compute_postorder(function);
}
