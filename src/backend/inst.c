#include "inst.h"
#include "x86-64/x86-64.h"

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

Oper
mfunction_reserve_stack_space(MFunction *mfunction, size_t size, size_t alignment)
{
	mfunction->stack_space = align(mfunction->stack_space, alignment);
	mfunction->stack_space += size;
	return -mfunction->stack_space;
}

void
mfunction_finalize_stack(MFunction *mfunction)
{
	// Align the stack space to 16 bytes (mandated by the calling
	// convention)
	mfunction->stack_space = align(mfunction->stack_space, 16);
	if (mfunction->make_stack_space) {
		IIMM(mfunction->make_stack_space) = mfunction->stack_space;
	}

	if (DUMP) {
		fprintf(stderr, "Function %.*s after stack finalization:\n", (int) mfunction->func->name.len, mfunction->func->name.str);
		print_mfunction(stderr, mfunction);
	}
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
remove_inst(Inst *inst)
{
	inst->prev->next = inst->next;
	inst->next->prev = inst->prev;
}

void
prepend_inst(Inst *pos, Inst *new)
{
	Inst *prev = pos->prev;
	new->prev = prev;
	new->next = pos;
	prev->next = new;
	pos->prev = new;
}

void
append_inst(Inst *pos, Inst *new)
{
	Inst *next = pos->next;
	new->next = next;
	new->prev = pos;
	next->prev = new;
	pos->next = new;
}

void
for_each_def(Inst *inst, void (*fun)(void *user_data, Oper *def), void *user_data)
{
	ModeDescriptor *mode = &mode_descs[inst->mode];
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
	ModeDescriptor *mode = &mode_descs[inst->mode];
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

void
increment_count(void *user_data, Oper *oper)
{
	u8 *count = user_data;
	count[*oper]++;
}

void
decrement_count(void *user_data, Oper *oper)
{
	u8 *count = user_data;
	count[*oper]--;
}

typedef struct {
	Inst *inst;
	Inst **only_def;
	u8 *def_cnt;
} LastDefState;

static void
track_last_def(void *user_data, Oper *oper)
{
	LastDefState *lds = user_data;
	// It is important that we set this to NULL if any second definition
	// exists, otherwise decrements of the def count might make it seem
	// like there was only one definition.
	lds->only_def[*oper] = lds->def_cnt[*oper] == 1 ? lds->inst : NULL;
}

void
calculate_def_use_info(MFunction *mfunction)
{
	GROW_ARRAY(mfunction->def_count, mfunction->vreg_cnt);
	GROW_ARRAY(mfunction->use_count, mfunction->vreg_cnt);
	GROW_ARRAY(mfunction->only_def, mfunction->vreg_cnt);
	ZERO_ARRAY(mfunction->def_count, mfunction->vreg_cnt);
	ZERO_ARRAY(mfunction->use_count, mfunction->vreg_cnt);
	ZERO_ARRAY(mfunction->only_def, mfunction->vreg_cnt);

	GROW_ARRAY(mfunction->block_use_count, mfunction->func->block_cap);
	ZERO_ARRAY(mfunction->block_use_count, mfunction->func->block_cap);

	LastDefState lds = { .only_def = mfunction->only_def, .def_cnt = mfunction->def_count };
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		bool flags_needed = false;
		for (Inst *inst = mblock->insts.prev; inst != &mblock->insts; inst = inst->prev) {
			lds.inst = inst;
			for_each_def(inst, increment_count, mfunction->def_count);
			for_each_def(inst, track_last_def, &lds);
			for_each_use(inst, increment_count, mfunction->use_count);
			inst->flags_observed = flags_needed;
			if (inst->writes_flags) {
				flags_needed = false;
			}
			if (inst->reads_flags) {
				flags_needed = true;
			}

			if (IM(inst) == M_L) {
				mfunction->block_use_count[ILABEL(inst)]++;
			}
		}
	}
}
