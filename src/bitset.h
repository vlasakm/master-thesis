#pragma once

#include "utils.h"

typedef struct {
	u32 *buf;
} BitSet;

void bs_init(BitSet *bs);

void bs_grow(BitSet *bs, size_t size);

void bs_free(BitSet *bs, size_t size);

void bs_reset(BitSet *bs, size_t size);

bool bs_test(BitSet *bs, Oper index);

void bs_set(BitSet *bs, Oper index);

void bs_clear(BitSet *bs, Oper index);
