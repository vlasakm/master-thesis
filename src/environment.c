#include "environment.h"

void
env_push(Environment *env)
{
	if (env->scope_cnt == env->scope_cap) {
		env->scope_cap = env->scope_cap ? env->scope_cap * 2 : 8;
		GROW_ARRAY(env->scopes, env->scope_cap);
	}
	table_init(&env->scopes[env->scope_cnt++]);
}

void
env_pop(Environment *env)
{
	assert(env->scope_cnt > 0);
	table_free(&env->scopes[--env->scope_cnt]);
}

void
env_define(Environment *env, Str name, Value *value)
{
	assert(env->scope_cnt > 0);
	table_insert(&env->scopes[env->scope_cnt - 1], name, value);
}

bool
env_lookup(Environment *env, Str name, void **value)
{
	for (size_t i = env->scope_cnt; i--;) {
		if (table_get(&env->scopes[i], name, value)) {
			return true;
		}
	}
	return false;
}

void
env_free(Environment *env)
{
	for (size_t i = 0; i < env->scope_cnt; i++) {
		table_free(&env->scopes[--env->scope_cnt]);
	}
	FREE_ARRAY(env->scopes, env->scope_cnt);
}

