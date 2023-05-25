#include "inst.h"
#include "x86-64.h"

MFunction *
mfunction_create(Arena *arena, Function *function, GArena *labels)
{
	MFunction *mfunction = arena_alloc(arena, sizeof(*mfunction));
	*mfunction = (MFunction) {
		.func = function,
		.labels = labels,
		.mblocks = arena_alloc(arena, function->block_cnt * sizeof(mfunction->mblocks[0])),
		.mblock_cnt = function->block_cnt,
	};

	function->mfunction = mfunction;

	return mfunction;
}

MBlock *
mblock_create(Arena *arena, Block *block)
{
	MBlock *mblock = arena_alloc(arena, sizeof(*mblock));
	*mblock = (MBlock) {
		.block = block,
		// head of the linked list of instructions
		.insts = (Inst) {
			.kind = IK_BLOCK,
			.subkind = 0,
			.mode = M_NONE,
			.next = &mblock->insts,
			.prev = &mblock->insts,
		},
	};

	block->mblock = mblock;

	return mblock;
}

void
mfunction_free(MFunction *mfunction)
{
	if (!mfunction) {
		return;
	}
	FREE_ARRAY(mfunction->def_count, mfunction->vreg_cnt);
	FREE_ARRAY(mfunction->use_count, mfunction->vreg_cnt);
	FREE_ARRAY(mfunction->only_def, mfunction->vreg_cnt);

	FREE_ARRAY(mfunction->block_use_count, mfunction->mblock_cnt);
}

void
print_mfunction(FILE *f, MFunction *mfunction)
{
	print_str(f, mfunction->func->name);
	fprintf(f, ":\n");
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		fprintf(f, ".L%zu:\n", mblock->block->base.index);
		for (Inst *inst = mblock->insts.next; inst != &mblock->insts; inst = inst->next) {
			fprintf(f, "\t");
			print_inst(f, mfunction, inst);
			fprintf(f, "\n");
		}
	}
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
