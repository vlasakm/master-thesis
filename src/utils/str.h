#pragma once

#include <stdio.h>

#include "utils.h"

typedef struct {
	const u8 *str;
	size_t len;
} Str;
#define STR(lit) (Str) { .str = (const u8 *) lit, .len = sizeof(lit) - 1 }

bool str_eq(Str a, Str b);

int str_cmp(Str a, Str b);

u64 str_hash(Str id);

void print_str(FILE *f, Str s);
