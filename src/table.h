#pragma once

#include "utils.h"
#include "str.h"

typedef struct {
	Str key;
	void *value;
} Entry;

typedef struct {
	Entry *entries;
	size_t entry_cnt;
	size_t capacity;
} Table;

void table_init(Table *table);

void table_free(Table *table);

Entry *table_find_entry(Entry *entries, size_t capacity, Str key);

void table_grow(Table *table);

bool table_get(Table *table, Str key, void **value);

bool table_insert(Table *table, Str key, void *value);
