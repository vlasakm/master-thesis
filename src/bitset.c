#include "bitset.h"

#define SIZE 32U
#define SHIFT 5U
#define MASK 31U

// Round up the size to whole 4 bytes
#define SIZE_TO_CAPACITY(size) (((size) + MASK) >> SHIFT)

void
bs_init(BitSet *bs)
{
	bs->buf = NULL;
}

void
bs_grow(BitSet *bs, size_t size)
{
	size = SIZE_TO_CAPACITY(size);
	GROW_ARRAY(bs->buf, size);
}

void
bs_free(BitSet *bs, size_t size)
{
	size = SIZE_TO_CAPACITY(size);
	FREE_ARRAY(bs->buf, size);
}

void
bs_reset(BitSet *bs, size_t size)
{
	size = SIZE_TO_CAPACITY(size);
	ZERO_ARRAY(bs->buf, size);
}

bool
bs_test(BitSet *bs, Oper index)
{
	return (bs->buf[index >> SHIFT] & (1U << (index & MASK))) != 0;
}

void
bs_set(BitSet *bs, Oper index)
{
	bs->buf[index >> SHIFT] |= 1U << (index & MASK);
}

void
bs_clear(BitSet *bs, Oper index)
{
	bs->buf[index >> SHIFT] &= ~(1U << (index & MASK));
}
