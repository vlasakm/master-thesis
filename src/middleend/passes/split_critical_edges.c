#include "../ir.h"

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
			Block *new_block = create_block(arena, function);
			block_add_pred(new_block, pred);
			Value *jump = create_unary(arena, VK_JUMP, &TYPE_VOID, &succ->base);
			jump->parent = &new_block->base;
			jump->index = function->value_cnt++;
			prepend_value(&new_block->base, jump);
			FOR_EACH_BLOCK_SUCC(pred, s) {
				if (*s == succ) {
					*s = new_block;
				}
			}
			FOR_EACH_BLOCK_PRED(succ, p) {
				if (*p == pred) {
					*p = new_block;
				}
			}
		}
	}

	// Recompute function->post_order, since we invalidated it.
	compute_postorder(function);
}
