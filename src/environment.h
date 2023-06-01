#pragma once

#include "table.h"

typedef struct {
	Table *scopes;
	size_t scope_cnt;
	size_t scope_cap;
} Environment;

void env_push(Environment *env);

void env_pop(Environment *env);

void env_define(Environment *env, Str name, void *value);

bool env_lookup(Environment *env, Str name, void **value);

void env_free(Environment *env);
