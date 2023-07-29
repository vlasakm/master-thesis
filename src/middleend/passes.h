#include "ir.h"

// IR passes (each in its own file)

// value_numbering.c
void value_numbering(Arena *arena, Function *function);

// merge_blocks.c
void merge_blocks(Arena *arena, Function *function);

// thread_jumps.c
void thread_jumps(Arena *arena, Function *function);

// split_critical_edges.c
void split_critical_edges(Arena *arena, Function *function);

// single_exit.c
void single_exit(Arena *arena, Function *function);

// deconstruct_ssa.c
void deconstruct_ssa(Arena *arena, Function *function);
