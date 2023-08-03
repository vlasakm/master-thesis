#include "../ir.h"

void
deconstruct_ssa(Arena *arena, Function *function)
{
	for (size_t b = function->block_cnt; b--;) {
		Block *block = function->post_order[b];
		FOR_EACH_PHI_IN_BLOCK(block, phi) {
			Type *type = phi->base.type;
			size_t index = function->value_cnt++;
			size_t i = 0;
			FOR_EACH_BLOCK_PRED(block, pred_) {
				Value *pred_block = &(*pred_)->base;
				Value *copy = create_unary(arena, VK_IDENTITY, type, phi->operands[i++]);
				copy->index = index;
				copy->parent = pred_block;
				// Append copy to the end of the block
				prepend_value(pred_block->prev, copy);
			}
			// Transform the phi into a copy of the virtual register
			// with `index` (which we do through a dummy operation).
			Value *dummy = &create_operation(arena, VK_NOP, type, 0)->base;
			dummy->index = index;
			change_to_identity(phi, dummy);
		}
	}

	if (DUMP) {
		fprintf(stderr, "Function %.*s after SSA deconstruction:\n", (int) function->name.len, function->name.str);
		print_function(stderr, function);
	}
}
