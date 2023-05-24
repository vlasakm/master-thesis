#pragma once

#include "arena.h"
#include "inst.h"

typedef struct RegAllocState RegAllocState;

// Public "full regalloc" API

RegAllocState *reg_alloc_state_create(Arena *arena);

void reg_alloc_function(RegAllocState *ras, MFunction *mfunction);

void reg_alloc_state_free(RegAllocState *ras);
