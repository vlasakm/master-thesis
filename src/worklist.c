#include "worklist.h"
#include "utils.h"

void
wl_grow(WorkList *wl, size_t new_capacity)
{
	// Worklist can't be entirely full (2^new_capacity elements), because
	// then we wouldn't be able to distinguish between "full" and "empty",
	// so we overallocate to make sure we don't hit this edge case.
	new_capacity *= 2;
	wl->mask = new_capacity - 1;
	GROW_ARRAY(wl->dense, new_capacity);
	GROW_ARRAY(wl->sparse, new_capacity);
#ifdef USE_VALGRIND
	ZERO_ARRAY(wl->sparse, new_capacity);
#endif
}

void
wl_init_all(WorkList *wl, Oper op)
{
	assert(op < wl->mask);
	wl->tail = op;
	for (size_t i = 0; i < op; i++) {
		wl->dense[i] = i;
		wl->sparse[i] = i;
	}
	for (size_t i = wl->head; i < wl->tail; i++) {
		assert(wl->sparse[wl->dense[i]] == (Oper) i);
	}
}

#define FOR_EACH_WL_INDEX(wl, i) \
	for (size_t i = (wl)->head; i != (wl)->tail; i = (i + 1) & (wl)->mask)

void
wl_init_all_reverse(WorkList *wl, Oper op)
{
	assert(op < wl->mask);
	wl->head = 0;
	wl->tail = op;
	for (size_t i = 0; i < op; i++) {
		wl->dense[i] = op - i - 1;
		wl->sparse[op - i - 1] = i;
	}
	for (size_t i = 0; i < op; i++) {
		assert(wl->sparse[wl->dense[i]] == (Oper) i);
	}
}

bool
wl_has(WorkList *wl, Oper op)
{
	return wl->sparse[op] >= wl->head && wl->sparse[op] < wl->tail && wl->dense[wl->sparse[op]] == op;
}

bool
wl_add(WorkList *wl, Oper op)
{
	assert(op < wl->mask);
	if (!wl_has(wl, op)) {
		wl->sparse[op] = wl->tail;
		wl->dense[wl->tail] = op;
		wl->tail = (wl->tail + 1) & wl->mask;
		FOR_EACH_WL_INDEX(wl, i) {
			assert(wl->sparse[wl->dense[i]] == (Oper) i);
		}
		return true;
	}
	return false;
}

void
wl_union(WorkList *wl, WorkList *other)
{
	FOR_EACH_WL_INDEX(other, i) {
		wl_add(wl, other->dense[i]);
	}
}

bool
wl_remove(WorkList *wl, Oper op)
{
	assert(op < wl->mask);
	if (wl_has(wl, op)) {
		wl->tail = (wl->tail - 1) & wl->mask;
		Oper last = wl->dense[wl->tail];
		wl->dense[wl->sparse[op]] = last;
		wl->sparse[last] = wl->sparse[op];
		wl->dense[wl->tail] = op;
		FOR_EACH_WL_INDEX(wl, i) {
			assert(wl->sparse[wl->dense[i]] == (Oper) i);
		}
		return true;
	}
	return false;
}

bool
wl_take(WorkList *wl, Oper *taken)
{
	if (wl->head == wl->tail) {
		return false;
	}
	*taken = wl->dense[wl->head];
	wl->head = (wl->head + 1) & wl->mask;
	return true;
}

bool
wl_take_back(WorkList *wl, Oper *taken)
{
	if (wl->head == wl->tail) {
		return false;
	}
	wl->tail = (wl->tail - 1) & wl->mask;
	*taken = wl->dense[wl->tail];
	return true;
}

Oper
wl_cnt(WorkList *wl)
{
	if (wl->head <= wl->tail) {
		return wl->tail - wl->head;
	} else {
		return wl->tail + wl->mask + 1 - wl->head;
	}
}

Oper
wl_empty(WorkList *wl)
{
	return wl->tail == wl->head;
}

void
wl_reset(WorkList *wl)
{
	wl->head = wl->tail = 0;
}

bool
wl_eq(WorkList *wl, WorkList *other)
{
	assert(wl->mask == other->mask);
	if (wl_cnt(wl) != wl_cnt(other)) {
		return false;
	}
	for (size_t i = wl->head; i < wl->tail; i++) {
		if (!wl_has(other, wl->dense[i])) {
			return false;
		}
	}
	return true;
}

void
wl_destroy(WorkList *wl)
{
	free(wl->sparse);
	free(wl->dense);
	*wl = (WorkList) {0};
}
