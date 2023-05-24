#include "inst.h"
#include "x86-64.h"

void
mfunction_free(MFunction *mfunction)
{
	FREE_ARRAY(mfunction->def_count, mfunction->vreg_cnt);
	FREE_ARRAY(mfunction->use_count, mfunction->vreg_cnt);
	FREE_ARRAY(mfunction->only_def, mfunction->vreg_cnt);

	FREE_ARRAY(mfunction->block_use_count, mfunction->mblock_cnt);
}

void
for_each_def(Inst *inst, void (*fun)(void *user_data, Oper *def), void *user_data)
{
	InsFormat *mode = &formats[inst->mode];
	for (size_t i = mode->def_start; i < mode->def_end; i++) {
		fun(user_data, &inst->ops[i]);
	}
	if (mode->def_cnt_given_by_arg_cnt) {
		size_t def_cnt = IARG_CNT(inst);
		for (size_t i = 0; i < def_cnt; i++) {
			fun(user_data, &mode->extra_defs[i]);
		}
	} else {
		for (Oper *def = mode->extra_defs; *def != R_NONE; def++) {
			fun(user_data, def);
		}
	}
}

void
for_each_use(Inst *inst, void (*fun)(void *user_data, Oper *use), void *user_data)
{
	InsFormat *mode = &formats[inst->mode];
	for (size_t i = mode->use_start; i < mode->use_end; i++) {
		fun(user_data, &inst->ops[i]);
	}
	if (mode->use_cnt_given_by_arg_cnt) {
		size_t use_cnt = IARG_CNT(inst);
		for (size_t i = 0; i < use_cnt; i++) {
			fun(user_data, &mode->extra_uses[i]);
		}
	} else {
		for (Oper *use = mode->extra_uses; *use != R_NONE; use++) {
			fun(user_data, use);
		}
	}
}
