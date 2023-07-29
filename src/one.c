#include "utils/arena.c"
#include "utils/worklist.c"
#include "utils/str.c"
#include "utils/table.c"
#include "utils/environment.c"
#include "utils/bitset.c"
#include "utils/utils.c"

#include "frontend/c/parser.c"

#include "middleend/type.c"
#include "middleend/ir.c"

#include "middleend/passes/value_numbering.c"
#include "middleend/passes/merge_blocks.c"
#include "middleend/passes/thread_jumps.c"
#include "middleend/passes/split_critical_edges.c"
#include "middleend/passes/single_exit.c"
#include "middleend/passes/deconstruct_ssa.c"

#include "backend/inst.c"
#include "backend/regalloc.c"
#include "backend/x86-64/x86-64.c"
#include "backend/x86-64/lower.c"
#include "backend/x86-64/peephole.c"


#include "main.c"
