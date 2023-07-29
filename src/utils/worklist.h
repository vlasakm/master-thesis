#pragma once

#include <stddef.h>

#include "utils.h"

typedef struct {
	size_t head;
	size_t tail;
	size_t mask;
	Oper *sparse;
	Oper *dense;
} WorkList;

#define FOR_EACH_WL_INDEX(wl, i) \
	for (size_t i = (wl)->head; i != (wl)->tail; i = (i + 1) & (wl)->mask)

void wl_grow(WorkList *wl, size_t new_capacity);

void wl_init_all(WorkList *wl, Oper op);

void wl_init_all_reverse(WorkList *wl, Oper op);

bool wl_has(WorkList *wl, Oper op);

bool wl_add(WorkList *wl, Oper op);

void wl_union(WorkList *wl, WorkList *other);

bool wl_remove(WorkList *wl, Oper op);

bool wl_take(WorkList *wl, Oper *taken);

bool wl_take_back(WorkList *wl, Oper *taken);

Oper wl_cnt(WorkList *wl);

Oper wl_empty(WorkList *wl);

void wl_reset(WorkList *wl);

bool wl_eq(WorkList *wl, WorkList *other);

void wl_free(WorkList *wl);
