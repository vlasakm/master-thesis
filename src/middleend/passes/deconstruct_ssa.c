#include "../ir.h"

// Deconstruct SSA form
//  - introduce "identity" (copy) instructions in predecessors to simulate phi
//  functions
//  - necessary for the lowering to backend, since it doesn't have phi
//  instructions
//  - we introduce don't delete the phi, but instead replace it with a copy
//  ("identity") instruction, this prevents the lost copy and swap problems
//
// Example, from:
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
// to:
//
//     f:
//             v17: int = argument 0
//     block0:
//             branch v17, block2, block5
//     block5: block0
//             v32: int = identity 3
//             jump block4
//     block2: block0
//             v32: int = identity 4
//             jump block4
//     block4: block2, block5
//             v30: int = identity v32
//             ret v30
//
// The integer constants 3 and 4 are now moved into a newly created common
// "register" 32 in both blocks 2 and 5. The original register of the phi got
// reused for the identity (copy) instruction.

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

	dump_function_after_pass(function, "SSA deconstruction");
}
