#include "arena.c"
#include "worklist.c"
#include "str.c"
#include "table.c"
#include "environment.c"
#include "utils.c"
#include "type.c"
#include "ir.c"
#include "inst.c"
#include "regalloc.c"
#include "parser.c"
#include "x86-64.c"
#include "lower.c"

#include "value_numbering.c"
#include "merge_blocks.c"
#include "thread_jumps.c"
#include "split_critical_edges.c"
#include "single_exit.c"
#include "deconstruct_ssa.c"

#include "tcg.c"
#include "bitset.c"
