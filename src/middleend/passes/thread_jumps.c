#include "../ir.h"

// NOTE: May introduce critical edges.
void
thread_jumps(Arena *arena, Function *function)
{
	(void) arena;
	for (size_t b = 0; b < function->block_cnt; b++) {
		Block *block = function->post_order[b];
		if (VK(block->base.next) != VK_JUMP) {
			continue;
		}
		Block *succ = block_succs(block)[0];
		if (VK(succ->base.next) == VK_PHI) {
			// If the (only) successors has phi nodes, than bail
			// out, since we currently are not able to handle it.
			continue;
		}
		// Block is empty and has only one successor. We can just
		// forward the jumps from predecessors to the successor.

		// Replace all references to `block` in its predecessors, to
		// point to `succ` instead.
		FOR_EACH_BLOCK_PRED(block, pred) {
			FOR_EACH_BLOCK_SUCC(*pred, s) {
				if (*s == block) {
					*s = succ;
					break;
				}
			}
		}

		// Swap-remove `block` from the list of predecessors of `succ`.
		// We access the private members `preds_` and `pred_cnt_`
		// directly so we need to be careful about invariants - in
		// particular, the array of predecessors is heap allocated and
		// has limited capacity. Since we only remove a predecessor, it
		// is fine.
		Block **preds = succ->preds_;
		for (size_t i = 0; i < succ->pred_cnt_; i++) {
			if (preds[i] == block) {
				preds[i] = preds[--succ->pred_cnt_];
				break;
			}
		}

		// Add all predecessors of `block` as predecessors to `succ`.
		FOR_EACH_BLOCK_PRED(block, p) {
			block_add_pred(succ, *p);
		}
	}

	// Recompute function->post_order, since we invalidated it.
	compute_postorder(function);

	if (DUMP) {
		fprintf(stderr, "Function %.*s after jump threading:\n", (int) function->name.len, function->name.str);
		print_function(stderr, function);
	}
}
