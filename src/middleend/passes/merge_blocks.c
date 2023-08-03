#include "../ir.h"

void
merge_blocks(Arena *arena, Function *function)
{
	(void) arena;
	//for (size_t b = function->block_cnt; b--;) {
	for (size_t b = 0; b < function->block_cnt; b++) {
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

		// Fix parent links.
		FOR_EACH_IN_BLOCK(succ, v) {
			v->parent = &block->base;
		}

		// Remove the jump instruction from `block`.
		remove_value(block->base.prev);

		// Append `succ` instructions to `block`.
		block->base.prev->next = succ->base.next;
		succ->base.next->prev = block->base.prev;
		block->base.prev = succ->base.prev;
		block->base.prev->next = &block->base;

		// Make sure we don't operate on the merge successor if it
		// happens to be in processed later.
		succ->base.next = &succ->base;
		succ->base.prev = &succ->base;
	}

	// Recompute function->post_order, since we invalidated it.
	compute_postorder(function);

	if (DUMP) {
		fprintf(stderr, "Function %.*s after merging blocks:\n", (int) function->name.len, function->name.str);
		print_function(stderr, function);
	}
}
