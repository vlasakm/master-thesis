#include "../ir.h"

// Split *all* critical edges
//  - critical edge = control flow change from block with multiple successors to
//                    block with multiple predecessors
//  - splits needed for the backend where phi nodes are present
//  - we split all, since we can merge back easily in the backend
//
// See also:
//  - https://nickdesaulniers.github.io/blog/2023/01/27/critical-edge-splitting/
//
// Example, from:
//
//     f:
//             v17: int = argument 0
//     block0:
//             branch v17, block2, block4
//     block2: block0
//             jump block4
//     block4: block2, block0
//             v30: int = phi 4, 3
//             ret v30
//
//
// to:
//
//     f:
//             v17: int = argument 0
//     block0:
//             branch v17, block2, block5
//     block5: block0
//             jump block4
//     block2: block0
//             jump block4
//     block4: block2, block5
//             v30: int = phi 4, 3
//             ret v30
//
//
// block5 got introduced, because there was an edge between block0 and block4,
// where block0 had 2 successors (block2 and block4) and block4 had 2
// predecessors (block2 and block0).

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

	dump_function_after_pass(function, "critical edge splitting");
}
