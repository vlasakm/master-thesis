#include "arena.h"
#include "inst.h"
#include "worklist.h"
#include "utils.h"
#include "x86-64.h"

#include "regalloc.h"

struct RegAllocState {
	Arena *arena;

	// Current function for which we are allocating registers.
	MFunction *mfunction;
	// Current block, for some notion of current (used by some iterators).
	MBlock *mblock;
	// vreg_cnt stored duplicitly for convenience, but function could also
	// get out of sync with it's `mfunction->vreg_cnt` - but that doesn't
	// reflect vreg_cnt reserved for `RegAllocState`, which is given by n
	size_t n;
	// vreg_cnt * vreg_cnt
	size_t N;

	size_t vreg_capacity;
	size_t block_capacity;
	size_t move_capacity;

	// Parameters
	size_t reg_avail;

	// Final register allocation
	Oper *reg_assignment;

	u8 *to_spill;
	Oper *alias;

	// Spill cost related
	u16 *def_cost;
	u16 *use_cost;
	u8 *unspillable; // true/false for each vreg

	// Degrees of nodes.
	u32 *degree;

	// Interference Graph
	u8 *matrix; // bit map (u8/bool per vreg)
	GArena *adj_list;

	WorkList live_set;
	WorkList uninterrupted;
	u8 *ever_interrupted;
	WorkList block_work_list;
	WorkList *live_in;

	// Worklists for the different register allocation phases
	WorkList spill_wl;
	WorkList freeze_wl;
	WorkList simplify_wl;
	WorkList moves_wl;
	WorkList active_moves_wl;
	WorkList stack;

	GArena gmoves; // Array of Inst *
	GArena *move_list; // Array of GArena of Oper
};

RegAllocState *
reg_alloc_state_create(Arena *arena)
{
	RegAllocState *ras = arena_alloc(arena, sizeof(*ras));
	*ras = (RegAllocState) {
		.arena = arena,
		.reg_avail = 14,
	};
	return ras;
}

void
reg_alloc_state_reset(RegAllocState *ras)
{
	assert(ras->mfunction->vreg_cnt > 0);
	ras->n = ras->mfunction->vreg_cnt;
	ras->N = ras->n * ras->n;
	size_t old_vreg_capacity = ras->vreg_capacity;
	if (ras->vreg_capacity == 0) {
		ras->vreg_capacity = 64;
	}
	while (ras->vreg_capacity < ras->mfunction->vreg_cnt) {
		ras->vreg_capacity += ras->vreg_capacity;
	}
	size_t old_block_capacity = ras->block_capacity;
	if (ras->block_capacity == 0) {
		ras->block_capacity = 16;
	}
	while (ras->block_capacity < ras->mfunction->mblock_cnt) {
		ras->block_capacity += ras->block_capacity;
	}

	if (old_block_capacity < ras->block_capacity) {
		wl_grow(&ras->block_work_list, ras->block_capacity);
		GROW_ARRAY(ras->live_in, ras->block_capacity);
		ZERO_ARRAY(&ras->live_in[old_block_capacity], ras->block_capacity - old_block_capacity);
		for (size_t i = old_block_capacity; i < ras->block_capacity; i++) {
			wl_grow(&ras->live_in[i], ras->vreg_capacity);
		}
	}

	if (old_vreg_capacity < ras->vreg_capacity) {
		GROW_ARRAY(ras->reg_assignment, ras->vreg_capacity);
		GROW_ARRAY(ras->to_spill, ras->vreg_capacity);
		GROW_ARRAY(ras->alias, ras->vreg_capacity);
		GROW_ARRAY(ras->def_cost, ras->vreg_capacity);
		GROW_ARRAY(ras->use_cost, ras->vreg_capacity);
		GROW_ARRAY(ras->unspillable, ras->vreg_capacity);
		GROW_ARRAY(ras->degree, ras->vreg_capacity);
		GROW_ARRAY(ras->matrix, ras->vreg_capacity * ras->vreg_capacity);
		GROW_ARRAY(ras->adj_list, ras->vreg_capacity);
		ZERO_ARRAY(&ras->adj_list[old_vreg_capacity], ras->vreg_capacity - old_vreg_capacity);
		wl_grow(&ras->live_set, ras->vreg_capacity);
		wl_grow(&ras->uninterrupted, ras->vreg_capacity);
		GROW_ARRAY(ras->ever_interrupted, ras->vreg_capacity);
		for (size_t i = 0; i < old_block_capacity; i++) {
			wl_grow(&ras->live_in[i], ras->vreg_capacity);
		}
		wl_grow(&ras->spill_wl, ras->vreg_capacity);
		wl_grow(&ras->freeze_wl, ras->vreg_capacity);
		wl_grow(&ras->simplify_wl, ras->vreg_capacity);
		//wl_grow(&ras->moves_wl, ras->vreg_capacity);
		//wl_grow(&ras->active_moves_wl, ras->vreg_capacity);
		wl_grow(&ras->stack, ras->vreg_capacity);
		// gmoves doesn't need to grow
		GROW_ARRAY(ras->move_list, ras->vreg_capacity);
		ZERO_ARRAY(&ras->move_list[old_vreg_capacity], ras->vreg_capacity - old_vreg_capacity);
	}

	ZERO_ARRAY(ras->reg_assignment, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->to_spill, ras->mfunction->vreg_cnt);
	for (size_t i = 0; i < ras->mfunction->vreg_cnt; i++) {
		ras->alias[i] = i;
	}
	ZERO_ARRAY(ras->def_cost, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->use_cost, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->unspillable, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->degree, ras->mfunction->vreg_cnt);
	ZERO_ARRAY(ras->matrix, ras->N);
	for (size_t i = 0; i < ras->mfunction->vreg_cnt; i++) {
		garena_restore(&ras->adj_list[i], 0);
	}
	wl_reset(&ras->live_set);
	wl_reset(&ras->uninterrupted);
	ZERO_ARRAY(ras->ever_interrupted, ras->vreg_capacity);
	wl_reset(&ras->block_work_list);
	for (size_t i = 0; i < ras->mfunction->mblock_cnt; i++) {
		wl_reset(&ras->live_in[i]);
	}
	wl_reset(&ras->spill_wl);
	wl_reset(&ras->freeze_wl);
	wl_reset(&ras->simplify_wl);
	//wl_reset(&ras->moves_wl);
	//wl_reset(&ras->active_moves_wl);
	wl_reset(&ras->stack);
	garena_restore(&ras->gmoves, 0);
	for (size_t i = 0; i < ras->mfunction->vreg_cnt; i++) {
		garena_restore(&ras->move_list[i], 0);
	}
}

void
reg_alloc_state_free(RegAllocState *ras)
{
	FREE_ARRAY(ras->reg_assignment, ras->vreg_capacity);
	FREE_ARRAY(ras->to_spill, ras->vreg_capacity);
	FREE_ARRAY(ras->alias, ras->vreg_capacity);
	FREE_ARRAY(ras->def_cost, ras->vreg_capacity);
	FREE_ARRAY(ras->use_cost, ras->vreg_capacity);
	FREE_ARRAY(ras->unspillable, ras->vreg_capacity);
	FREE_ARRAY(ras->degree, ras->vreg_capacity);
	FREE_ARRAY(ras->matrix, ras->vreg_capacity);
	for (size_t i = 0; i < ras->vreg_capacity; i++) {
		garena_free(&ras->adj_list[i]);
	}
	FREE_ARRAY(ras->adj_list, ras->vreg_capacity);
	wl_free(&ras->live_set);
	wl_free(&ras->uninterrupted);
	FREE_ARRAY(ras->ever_interrupted, ras->vreg_capacity);
	wl_reset(&ras->block_work_list);
	wl_free(&ras->block_work_list);
	for (size_t i = 0; i < ras->block_capacity; i++) {
		wl_free(&ras->live_in[i]);
	}
	FREE_ARRAY(ras->live_in, ras->block_capacity);
	wl_free(&ras->spill_wl);
	wl_free(&ras->freeze_wl);
	wl_free(&ras->simplify_wl);
	wl_free(&ras->moves_wl);
	wl_free(&ras->active_moves_wl);
	wl_free(&ras->stack);
	garena_free(&ras->gmoves);
	for (size_t i = 0; i < ras->vreg_capacity; i++) {
		garena_free(&ras->move_list[i]);
	}
	FREE_ARRAY(ras->move_list, ras->vreg_capacity);
}

void
reg_alloc_state_init_for_function(RegAllocState *ras, MFunction *mfunction)
{
	ras->mfunction = mfunction;
	// Don't need to reset for function, since each iteration of reg alloc
	// needs reset anyways.
	//reg_alloc_state_reset(ras);
}

bool
is_alias(RegAllocState *ras, Oper u)
{
	return ras->alias[u] != u;
}

Oper
get_alias(RegAllocState *ras, Oper u)
{
	while (u != ras->alias[u]) {
		u = ras->alias[u];
	}
	return u;
}

bool
are_interfering(RegAllocState *ras, Oper u, Oper v)
{
	// R_NONE (0) is a special case - it is used as a place holder of "no
	// register used currently, but the slot could be occupied by a
	// register." We don't need to store any interferences related to it,
	// and instead we treat it as if it interfered with everything
	// automatically.
	if (u == R_NONE || v == R_NONE) {
		return true;
	}
	u8 one = ras->matrix[u * ras->n + v];
	u8 two = ras->matrix[v * ras->n + u];
	assert(one == two);
	return one;
}

void
add_interference(RegAllocState *ras, Oper u, Oper v)
{
	assert(u < ras->mfunction->vreg_cnt);
	assert(v < ras->mfunction->vreg_cnt);
	if (u == v || are_interfering(ras, u, v)) {
		return;
	}
	fprintf(stderr, "Adding interference ");
	print_reg(stderr, u);
	fprintf(stderr, " ");
	print_reg(stderr, v);
	fprintf(stderr, "\n");
	assert(ras->matrix[u * ras->n + v] == 0);
	assert(ras->matrix[v * ras->n + u] == 0);
	ras->matrix[u * ras->n + v] = 1;
	ras->matrix[v * ras->n + u] = 1;
	// Only populate adjacency lists for vregs. Adjacency lists for physical
	// regs would be too large. We don't actually need them - color
	// assigning needs only neighbours of vregs (since we have to choose a
	// color distinct from neighbours), and for coalescing heuristic we use
	// George's test, which doesn't use adjacency lists, unlike Briggs'
	// test (which we use for vregs).
	if (u >= R__MAX) {
		garena_push_value(&ras->adj_list[u], Oper, v);
	}
	if (v >= R__MAX) {
		garena_push_value(&ras->adj_list[v], Oper, u);
	}
	ras->degree[u]++;
	ras->degree[v]++;
}


void
get_live_out(RegAllocState *ras, Block *block, WorkList *live_set)
{
	// live-out of this block is the union of live-ins of all
	// successors
	wl_reset(live_set);
	FOR_EACH_BLOCK_SUCC(block, succ) {
		wl_union(live_set, &ras->live_in[(*succ)->mblock->index]);
	}
}


void
remove_from_set(void *user_data, Oper *oper)
{
	WorkList *live_set = user_data;
	fprintf(stderr, "Removing from live ");
	print_reg(stderr, *oper);
	fprintf(stderr, "\n");
	wl_remove(live_set, *oper);
}

void
add_to_set(void *user_data, Oper *oper)
{
	WorkList *live_set = user_data;
	fprintf(stderr, "Adding to live ");
	print_reg(stderr, *oper);
	fprintf(stderr, "\n");
	wl_add(live_set, *oper);
}

void
live_step(WorkList *live_set, MFunction *mfunction, Inst *inst)
{
	fprintf(stderr, "Live step at\t");
	print_inst(stderr, mfunction, inst);
	fprintf(stderr, "\n");
	// Remove definitions from live.
	for_each_def(inst, remove_from_set, live_set);
	// Add uses to live.
	for_each_use(inst, add_to_set, live_set);
}

typedef struct {
	RegAllocState *ras;
	Oper live;
} InterferenceState;

void
add_interference_with(void *user_data, Oper *oper)
{
	InterferenceState *is = user_data;
	add_interference(is->ras, *oper, is->live);
}

void
interference_step(RegAllocState *ras, WorkList *live_set, Inst *inst)
{
	// Special handling of moves:
	// 1) We don't want to introduce interference between move source and
	//    destination.
	// 2) We want to note all moves and for all nodes the moves they are
	//    contained in, because we want to try to coalesce the moves later.
	if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Cr) {
		// Remove uses from live to prevent interference between move
		// destination and source.
		for_each_use(inst, remove_from_set, live_set);

		// Accumulate moves.
		size_t index = garena_cnt(&ras->gmoves, Inst *);
		garena_push_value(&ras->gmoves, Inst *, inst);
		garena_push_value(&ras->move_list[inst->ops[0]], Oper, index);
		garena_push_value(&ras->move_list[inst->ops[1]], Oper, index);
	}


	// Add all definitions to live. Because the next step adds
	// interferences between all definitions and all live, we will thus also
	// make all the definitions interfere with each other. Since the
	// liveness step (run after us) removes all definitions, this is OK and
	// local to the current instruction.
	for_each_def(inst, add_to_set, live_set);

	// Add interferences of all definitions with all live.
	InterferenceState is = { .ras = ras };
	FOR_EACH_WL_INDEX(live_set, j) {
		is.live = live_set->dense[j];
		for_each_def(inst, add_interference_with, &is);
	}
}

typedef struct {
	RegAllocState *ras;
	Inst *inst;
	Oper spill_start;
} SpillState;

Oper
get_fresh_vreg_for_spill(RegAllocState *ras)
{
	Oper vreg = ras->mfunction->vreg_cnt++;
	// If we get out of capacity, reserve 3 times that much in the spill
	// array, just so we can progress. The rest of the data structures are
	// only needed in the second reg alloc try, which resets and reallocates
	// them. This still doesn' guarantee, that we won't get out of vregs,
	// because we don't bump the capacity, but at that point, there should
	// be a better solution altogether.
	if (vreg == ras->vreg_capacity) {
		GROW_ARRAY(ras->to_spill, ras->vreg_capacity * 4);
	}
	assert(vreg != 4 * ras->vreg_capacity);
	return vreg;
}

bool
is_to_be_spilled(SpillState *ss, Oper t)
{
	// NOTE: We make sure that even `to_spill` is in bounds even for vregs
	// introduced for spill code, see `get_fresh_vreg_for_spill` above.
	return ss->ras->to_spill[t];
}

Inst *create_inst(Arena *arena, InstKind kind, u8 subkind, X86Mode mode);

void
insert_loads_of_spilled(void *user_data, Oper *src)
{
	SpillState *ss = user_data;
	RegAllocState *ras = ss->ras;
	if (!is_to_be_spilled(ss, *src)) {
		return;
	}
	Inst *inst = ss->inst;

	Oper temp = get_fresh_vreg_for_spill(ras);
	ras->to_spill[temp] = ras->to_spill[*src];
	fprintf(stderr, "load ");
	print_reg(stderr, *src);
	fprintf(stderr, " through ");
	print_reg(stderr, temp);
	Inst *load = create_inst(ras->arena, IK_MOV, MOV, M_CM);
	//Inst *load = make_inst(ras->arena, OP_MOV_RMC, temp, R_RBP, 8 + ras->to_spill[src]);
	load->prev = inst->prev;
	load->next = inst;
	IREG(load) = temp;
	IBASE(load) = R_RBP;
	IDISP(load) = - 8 - ras->to_spill[*src];

	inst->prev->next = load;
	inst->prev = load;

	*src = temp;
}

void
insert_stores_of_spilled(void *user_data, Oper *dest)
{
	SpillState *ss = user_data;
	RegAllocState *ras = ss->ras;
	if (!is_to_be_spilled(ss, *dest)) {
		return;
	}
	Inst *inst = ss->inst;

	// If the "to be spilled" register has actually been introduced only
	// after we started spilling (i.e. it is bigger than `spill_start`, then
	// we actually have a definition of a use in this same instruction.
	// Think:
	//
	//    add t20, t21
	//
	// If use of t20 has been spilled through t30, and we have:
	//
	//    mov t30, [rbp+t20]
	//    add t30, t21
	//
	// Then we need to store t30 and not introduce a new vreg:
	//
	//    mov t30, [rbp+t20]
	//    add t30, t21
	//    mov [rbp+t20], t30
	//
	// Of course at that point we could also have:
	//
	//    add [rbp+t20], t21
	//
	// But:
	//  1) that is the business of the instruction selection,
	//  2) it may be actually worse, depending on the surrounding code.
	//
	// For example if we originally had:
	//
	//    mov t20, t22
	//    add t20, t21
	//
	// Then we don't want store followed immediately by a load:
	//
	//    mov [rbp+t20], t22
	//    add [rbp+t20], t21
	//
	// But instead we would want:
	//
	//    mov t30, t22
	//    add t30, t21
	//    mov [rbp+t20], t30
	//
	Oper temp;
	if (*dest >= ss->spill_start) {
		temp = *dest;
	} else {
		temp = get_fresh_vreg_for_spill(ras);
	}
	fprintf(stderr, "store ");
	print_reg(stderr, *dest);
	fprintf(stderr, " through ");
	print_reg(stderr, temp);
	fprintf(stderr, "\n");

	//Inst *store = make_inst(ras->arena, OP_MOV_MCR, R_RBP, temp, 8 + ras->to_spill[dest]);
	Inst *store = create_inst(ras->arena, IK_MOV, MOV, M_Mr);
	store->prev = inst;
	store->next = inst->next;
	IREG(store) = temp;
	IBASE(store) = R_RBP;
	IDISP(store) = - 8 - ras->to_spill[*dest];

	inst->next->prev = store;
	inst->next = store;
	inst = inst->next;

	*dest = temp;
}

// Add spill code, coalesce registers that were found to be coalescable before
// the first potential spill.
void
rewrite_program(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	SpillState ss_ = {
		.ras = ras,
		.spill_start = mfunction->vreg_cnt,
	}, *ss = &ss_;
	print_mfunction(stderr, mfunction);
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		for (Inst *inst = mblock->insts.next; inst != &mblock->insts; inst = inst->next) {
			ss->inst = inst;
			fprintf(stderr, "\n");
			print_inst(stderr, mfunction, inst);
			fprintf(stderr, "\n");
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Cr) {
				Oper dest = inst->ops[0];
				Oper src = inst->ops[1];
				bool spill_dest = is_to_be_spilled(ss, dest);
				bool spill_src = is_to_be_spilled(ss, src);
				if (spill_dest && spill_src) {
					// If this would be essentially:
					//    mov [rbp+X], [rbp+X]
					// we can just get rid of the copy.
					assert(false);
					if (ras->to_spill[dest] == ras->to_spill[src]) {
						inst->prev->next = inst->next;
						inst->next->prev = inst->prev;
					}
				} else if (spill_dest) {
					inst->mode = M_Mr;
					IREG(inst) = src;
					IBASE(inst) = R_RBP;
					IDISP(inst) = - 8 - ras->to_spill[dest];
				} else if (spill_src) {
					inst->mode = M_CM;
					IREG(inst) = dest;
					IBASE(inst) = R_RBP;
					IDISP(inst) = - 8 - ras->to_spill[src];
				}
				continue;
			}
			//print_inst_d(stderr, inst);
			//fprintf(stderr, "\n");
			// Add loads for all spilled uses.
			for_each_use(inst, insert_loads_of_spilled, ss);
			// Add stores for all spilled defs.
			for_each_def(inst, insert_stores_of_spilled, ss);
		}
	}
	print_mfunction(stderr, mfunction);
}

void
apply_reg_assignment(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		for (Inst *inst = mblock->insts.next; inst != &mblock->insts; inst = inst->next) {
			// TODO: different number of register slots per target
			// TODO: store number of registers in mode
			InsFormat *mode = &formats[inst->mode];
			size_t end = mode->use_end > mode->def_end ? mode->use_end : mode->def_end;
			for (size_t i = 0; i < end; i++) {
				inst->ops[i] = ras->reg_assignment[get_alias(ras, inst->ops[i])];
			}
		}
	}
}

void
mark_defs_with_uninterrupted_uses_unspillable(void *user_data, Oper *def_)
{
	RegAllocState *ras = user_data;
	Oper def = *def_;
	// Check if this definition has a following use and the live range is
	// uninterrupted by any death of other live range. Make sure that the
	// use is really uninterrupted, by checking global flag which forbids
	// interruptions.
	if (wl_remove(&ras->uninterrupted, def) && !ras->ever_interrupted[def]) {
		ras->unspillable[def] = true;
		if (def >= R__MAX) {
			fprintf(stderr, "Marking ");
			print_reg(stderr, def);
			fprintf(stderr, " as unspillable\n");
		}
	}
	// Update def cost by the depth of the current block, which is zero
	// based, so we offset by one to not have zero cost in the top level.
	ras->def_cost[def] += 1 << (3 * (ras->mblock->block->depth + 1));
	// Update liveness.
	wl_remove(&ras->live_set, def);
}

void
detect_interrupting_deaths(void *user_data, Oper *use_)
{
	RegAllocState *ras = user_data;
	Oper use = *use_;
	if (!wl_has(&ras->live_set, use)) {
		WorkList *uninterrupted = &ras->uninterrupted;
		FOR_EACH_WL_INDEX(uninterrupted, i) {
			Oper op = uninterrupted->dense[i];
			ras->ever_interrupted[op] = true;
		}
		wl_reset(uninterrupted);
	}
}

void
add_live(void *user_data, Oper *use_)
{
	RegAllocState *ras = user_data;
	Oper use = *use_;
	// Update use count.
	ras->use_cost[use] += 1 << (3 * (ras->mblock->block->depth + 1));
	// Update liveness and add note that this use is uninterrupted for now.
	wl_add(&ras->live_set, use);
	wl_add(&ras->uninterrupted, use);
}

void
calculate_spill_cost(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	WorkList *live_set = &ras->live_set;

	for (Oper b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		ras->mblock = mblock;
		Block *block = mblock->block;
		get_live_out(ras, block, live_set);
		// We currently can't make unspillable those vregs whose live
		// ranges cross basic block boundaries. Make sure we don't mark
		// them unspillable by marking them as "interrupted somewhere"
		// (in this case by basic block boundary).
		FOR_EACH_WL_INDEX(live_set, i) {
			Oper live_across_block = live_set->dense[i];
			ras->ever_interrupted[live_across_block] = true;
		}
		for (Inst *inst = mblock->insts.prev; inst != &mblock->insts; inst = inst->prev) {
			for_each_def(inst, mark_defs_with_uninterrupted_uses_unspillable, ras);
			for_each_use(inst, detect_interrupting_deaths, ras);
			for_each_use(inst, add_live, ras);
		}
	}
}

void
liveness_analysis(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	WorkList *live_set = &ras->live_set;

	wl_init_all_reverse(&ras->block_work_list, mfunction->mblock_cnt);
	Oper b;
	while (wl_take(&ras->block_work_list, &b)) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		Block *block = mblock->block;
		get_live_out(ras, block, live_set);
		fprintf(stderr, "Live out %zu: ", mblock->block->base.index);
		FOR_EACH_WL_INDEX(live_set, i) {
			print_reg(stderr, live_set->dense[i]);
			fprintf(stderr, ", ");
		}
		fprintf(stderr, "\n");
		// process the block back to front, updating live_set in the
		// process
		for (Inst *inst = mblock->insts.prev; inst != &mblock->insts; inst = inst->prev) {
			live_step(live_set, mfunction, inst);
		}
		if (!wl_eq(live_set, &ras->live_in[b])) {
			WorkList tmp = ras->live_in[b];
			ras->live_in[b] = *live_set;
			*live_set = tmp;
			FOR_EACH_BLOCK_PRED(block, pred) {
				wl_add(&ras->block_work_list, (*pred)->mblock->index);
			}
		}
	}
}

void
build_interference_graph(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	WorkList *live_set = &ras->live_set;

	for (Oper b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		Block *block = mblock->block;
		get_live_out(ras, block, live_set);
		for (Inst *inst = mblock->insts.prev; inst != &mblock->insts; inst = inst->prev) {
			interference_step(ras, live_set, inst);
			live_step(live_set, mfunction, inst);
		}
	}

	// Physical registers are initialized with infinite degree. This makes
	// sure that simplification doesn't ever see tham transition to
	// non-significant degree and thus pushing them on the stack.
	for (size_t i = 0; i < R__MAX; i++) {
		ras->degree[i] = ras->mfunction->vreg_cnt + ras->reg_avail;
	}
}

bool
is_move_related(RegAllocState *ras, Oper i)
{
	//fprintf(stderr, "Is move related ");
	//print_reg(stderr, i);
	//fprintf(stderr, "\n");
	//Inst **moves = garena_array(&ras->gmoves, Inst *);
	GArena *gmove_list = &ras->move_list[i];
	Oper *move_list = garena_array(gmove_list, Oper);
	size_t move_cnt = garena_cnt(gmove_list, Oper);
	for (size_t i = 0; i < move_cnt; i++) {
		Oper move_index = move_list[i];
		//Inst *move = moves[move_index];
		//fprintf(stderr, "Moved in \t");
		//print_inst(stderr, ras->mfunction, move);
		//fprintf(stderr, "\n");
		if (wl_has(&ras->active_moves_wl, move_index) || wl_has(&ras->moves_wl, move_index)) {
			return true;
		}
	}
	//fprintf(stderr, "Not move related\n");
	return false;
}


void
for_each_adjacent(RegAllocState *ras, Oper op, void (*fun)(RegAllocState *ras, Oper neighbour))
{
	assert(op >= R__MAX);
	GArena *gadj_list = &ras->adj_list[op];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t i = 0; i < adj_cnt; i++) {
		Oper neighbour = adj_list[i];
		if (wl_has(&ras->stack, neighbour) || is_alias(ras, neighbour)) {
			continue;
		}
		fun(ras, neighbour);
	}
}

void
for_each_move(RegAllocState *ras, Oper u, void (*fun)(RegAllocState *ras, Oper u, Oper m, Inst *move))
{
	Inst **moves = garena_array(&ras->gmoves, Inst *);
	GArena *gmove_list = &ras->move_list[u];
	Oper *move_list = garena_array(gmove_list, Oper);
	size_t move_cnt = garena_cnt(gmove_list, Oper);
	for (size_t i = 0; i < move_cnt; i++) {
		Oper move_index = move_list[i];
		if (wl_has(&ras->active_moves_wl, move_index) || wl_has(&ras->moves_wl, move_index)) {
			fun(ras, u, move_index, moves[move_index]);
		}
	}
}

bool
is_precolored(RegAllocState *ras, Oper op)
{
	return op < R__MAX;
}

bool
is_trivially_colorable(RegAllocState *ras, Oper op)
{
	return ras->degree[op] < ras->reg_avail;
}

bool
is_significant(RegAllocState *ras, Oper op)
{
	return ras->degree[op] >= ras->reg_avail;
}

void
initialize_worklists(RegAllocState *ras)
{
	size_t move_cnt = garena_cnt(&ras->gmoves, Inst *);
	size_t old_move_capacity = ras->move_capacity;
	if (ras->move_capacity == 0) {
		ras->move_capacity = 16;
	}
	while (ras->move_capacity < move_cnt) {
		ras->move_capacity += ras->move_capacity;
	}
	if (old_move_capacity < ras->move_capacity) {
		wl_grow(&ras->moves_wl, ras->move_capacity);
		wl_grow(&ras->active_moves_wl, ras->move_capacity);
	}
	wl_reset(&ras->moves_wl);
	wl_init_all(&ras->moves_wl, move_cnt);
	wl_reset(&ras->active_moves_wl);

	size_t vreg_cnt = ras->mfunction->vreg_cnt;
	for (size_t i = R__MAX; i < vreg_cnt; i++) {
		GArena *gadj_list = &ras->adj_list[i];
		size_t adj_cnt = garena_cnt(gadj_list, Oper);
		assert(adj_cnt == ras->degree[i]);
		if (is_significant(ras, i)) {
			wl_add(&ras->spill_wl, i);
			fprintf(stderr, "Starting in spill ");
			print_reg(stderr, i);
			fprintf(stderr, " (%zu)\n", (size_t) ras->degree[i]);
		} else if (is_move_related(ras, i)) {
			fprintf(stderr, "Starting in freeze ");
			print_reg(stderr, i);
			wl_add(&ras->freeze_wl, i);
			fprintf(stderr, " (%zu)\n", (size_t) ras->degree[i]);
		} else {
			wl_add(&ras->simplify_wl, i);
			fprintf(stderr, "Starting in simplify ");
			print_reg(stderr, i);
			fprintf(stderr, " (%zu)\n", (size_t) ras->degree[i]);
		}
	}
}

double
spill_metric(RegAllocState *ras, Oper i)
{
	if (ras->unspillable[i]) {
		return 0.0;
	}
	double cost = (double) ras->degree[i] / (ras->def_cost[i] + ras->use_cost[i]);
	fprintf(stderr, "Spill cost for ");
	print_reg(stderr, i);
	fprintf(stderr, " degree: %"PRIu32", defs: %zu, uses: %zu, unspillable: %d, cost: %f\n", ras->degree[i], (size_t) ras->def_cost[i], (size_t) ras->use_cost[i], (int) ras->unspillable[i], cost);
	return cost;
}

void
enable_move(RegAllocState *ras, Oper u, Oper m, Inst *move)
{
	(void) u;
	if (wl_remove(&ras->active_moves_wl, m)) {
		fprintf(stderr, "Enabling move: \t");
		print_inst(stderr, ras->mfunction, move);
		fprintf(stderr, "\n");
		wl_add(&ras->moves_wl, m);
	}
}

void
enable_moves_for_one(RegAllocState *ras, Oper op)
{
	for_each_move(ras, op, enable_move);
}

void
decrement_degree(RegAllocState *ras, Oper op)
{
	fprintf(stderr, "Removing interference with ");
	print_reg(stderr, op);
	fprintf(stderr, "\n");
	assert(ras->degree[op] > 0);
	ras->degree[op]--;
	if (is_trivially_colorable(ras, op)) {
		fprintf(stderr, "%zu %zu\n", (size_t) op, (size_t) R__MAX);
		assert(op >= R__MAX);
		enable_moves_for_one(ras, op);
		for_each_adjacent(ras, op, enable_moves_for_one);
		wl_remove(&ras->spill_wl, op);
		//fprintf(stderr, "Move from spill to %s ", is_move_related(ras, op) ? "freeze" : "simplify");
		//print_reg(stderr, op);
		//fprintf(stderr, "\n");
		if (is_move_related(ras, op)) {
			wl_add(&ras->freeze_wl, op);
		} else {
			wl_add(&ras->simplify_wl, op);
		}
	}
}

void
freeze_move(RegAllocState *ras, Oper u, Oper m, Inst *move)
{
	fprintf(stderr, "freezing in: \t");
	print_inst(stderr, ras->mfunction, move);
	fprintf(stderr, "\n");
	if (!wl_remove(&ras->active_moves_wl, m)) {
		assert(wl_remove(&ras->moves_wl, m));
	}
	Oper op1 = get_alias(ras, move->ops[0]);
	Oper op2 = get_alias(ras, move->ops[1]);
	assert(u == op1 || u == op2);
	Oper v = op1 != u ? op1 : op2;
	if (!is_move_related(ras, v) && is_trivially_colorable(ras, v)) {
		fprintf(stderr, "Move from freeze to simplify in freeze ");
		print_reg(stderr, v);
		fprintf(stderr, "\n");
		assert(wl_remove(&ras->freeze_wl, v));
		wl_add(&ras->simplify_wl, v);
	}
}

void
freeze_moves(RegAllocState *ras, Oper u)
{
	fprintf(stderr, "Freezing moves of ");
	print_reg(stderr, u);
	fprintf(stderr, "\n");
	for_each_move(ras, u, freeze_move);
}

void
freeze_one(RegAllocState *ras, Oper i)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->moves_wl));

	fprintf(stderr, "Freezing node ");
	print_reg(stderr, i);
	fprintf(stderr, "\n");

	wl_add(&ras->simplify_wl, i);
	freeze_moves(ras, i);
}

void
simplify_one(RegAllocState *ras, Oper i)
{
	assert(!is_alias(ras, i));
	fprintf(stderr, "Pushing ");
	print_reg(stderr, i);
	fprintf(stderr, "\n");

	wl_add(&ras->stack, i);
	for_each_adjacent(ras, i, decrement_degree);
}

void
choose_and_spill_one(RegAllocState *ras)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->moves_wl));
	assert(!wl_empty(&ras->spill_wl));

	fprintf(stderr, "Potential spill\n");

	Oper candidate = OPER_MAX;
	double max = 0.0;
	WorkList *spill_wl = &ras->spill_wl;
	FOR_EACH_WL_INDEX(spill_wl, j) {
		Oper i = spill_wl->dense[j];
		double curr = spill_metric(ras, i);
		// Prefer for spill either more beneficial candidates (with
		// bigger metric) or "earlier" vregs ("smaller index"). This
		// comes in handy for spilling callee saved registers, where we
		// want to spill `rbx` first, since encoding it is (sometimes)
		// shorter.
		if (curr > max || (curr == max && i < candidate)) {
			max = curr;
			candidate = i;
		}
	}

	fprintf(stderr, "Choosing for spill ");
	print_reg(stderr, candidate);
	fprintf(stderr, "\n");
	assert(candidate != OPER_MAX);
	assert(max > 0.0);

	wl_remove(&ras->spill_wl, candidate);
	wl_add(&ras->simplify_wl, candidate);
	freeze_moves(ras, candidate);
}

void
add_to_worklist(RegAllocState *ras, Oper op)
{
	if (!is_precolored(ras, op) && !is_move_related(ras, op) && is_trivially_colorable(ras, op)) {
		fprintf(stderr, "Move from freeze to simplify ");
		print_reg(stderr, op);
		fprintf(stderr, "\n");
		wl_remove(&ras->freeze_wl, op);
		wl_add(&ras->simplify_wl, op);
	}
}

size_t
significant_neighbour_cnt(RegAllocState *ras, Oper op)
{
	size_t n = 0;
	assert(op >= R__MAX);
	GArena *gadj_list = &ras->adj_list[op];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t j = 0; j < adj_cnt; j++) {
		Oper t = adj_list[j];
		if (wl_has(&ras->stack, t) || is_alias(ras, t)) {
			continue;
		}
		n += is_significant(ras, t);
	}
	return n;
}

bool
ok(RegAllocState *ras, Oper t, Oper r)
{
	return is_trivially_colorable(ras, t) || is_precolored(ras, t) || are_interfering(ras, t, r);
}

bool
precolored_coalesce_heuristic(RegAllocState *ras, Oper u, Oper v)
{
	assert(v >= R__MAX);
	GArena *gadj_list = &ras->adj_list[v];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t j = 0; j < adj_cnt; j++) {
		Oper t = adj_list[j];
		if (wl_has(&ras->stack, t) || is_alias(ras, t)) {
			continue;
		}
		if (!ok(ras, t, u)) {
			return false;
		}
	}
	return true;
}

bool
conservative_coalesce_heuristic(RegAllocState *ras, Oper u, Oper v)
{
	size_t n = significant_neighbour_cnt(ras, u) + significant_neighbour_cnt(ras, v);
	return n < ras->reg_avail;
}

bool
are_coalesceble(RegAllocState *ras, Oper u, Oper v)
{
	if (u < R__MAX) {
		return precolored_coalesce_heuristic(ras, u, v);
	} else {
		return conservative_coalesce_heuristic(ras, u, v);
	}
}

void
combine(RegAllocState *ras, Oper u, Oper v)
{
	fprintf(stderr, "Combining " );
	print_reg(stderr, u);
	fprintf(stderr, " and " );
	print_reg(stderr, v);
	fprintf(stderr, "\n");

	assert(v >= R__MAX);
	if (!wl_remove(&ras->freeze_wl, v)) {
		assert(wl_remove(&ras->spill_wl, v));
	}
	assert(!wl_has(&ras->simplify_wl, v));

	// Set `v` as alias of `u`. Caller should already pass canonical `u`
	// and `v`, which are not aliases themselves.
	ras->alias[v] = u;

	// Add moves of `v` to `u`.
	Oper *other_moves = garena_array(&ras->move_list[v], Oper);
	size_t other_move_cnt = garena_cnt(&ras->move_list[v], Oper);
	for (size_t i = 0; i < other_move_cnt; i++) {
		// NOTE: would deduplication be beneficial?
		garena_push_value(&ras->move_list[u], Oper, other_moves[i]);
	}

	// Add edges of `v` to `u`.
	GArena *gadj_list = &ras->adj_list[v];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t i = 0; i < adj_cnt; i++) {
		Oper t = adj_list[i];
		if (wl_has(&ras->stack, t) || is_alias(ras, t)) {
			continue;
		}
		// Add `u` as a neighbour to `v`'s neighbour `t`.
		add_interference(ras, u, t);
		// Since we coalesce `u` and `v`, we should remove `v` as a
		// neighbour. The important thing that we want to achieve is
		// actually decrement of `t`'s degree, which might make it
		// trivially colorable.
		//
		// We can get away with not removing `v` from adjacency list of
		// `u`, because aliased registers are skipped or resolve by
		// those iterating over them.
		decrement_degree(ras, t);
	}

	if (is_significant(ras, u) && wl_remove(&ras->freeze_wl, u)) {
		fprintf(stderr, "Move combined ");
		print_reg(stderr, u);
		fprintf(stderr, " from freeze to spill\n");
		wl_add(&ras->spill_wl, u);
	}
}

void
coalesce_move(RegAllocState *ras, Oper m)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->simplify_wl));
	MFunction *mfunction = ras->mfunction;

	Inst **moves = garena_array(&ras->gmoves, Inst *);
	Inst *move = moves[m];
	fprintf(stderr, "Coalescing: \t");
	print_inst(stderr, mfunction, move);
	fprintf(stderr, "\n");

	Oper u = get_alias(ras, move->ops[0]);
	Oper v = get_alias(ras, move->ops[1]);
	if (v < R__MAX) {
		Oper tmp = u;
		u = v;
		v = tmp;
	}

	if (u == v) {
		// already coalesced
		fprintf(stderr, "Already coalesced: \t");
		print_inst(stderr, mfunction, move);
		fprintf(stderr, "\n");
		add_to_worklist(ras, u);
	} else if (v < R__MAX || are_interfering(ras, u, v)) {
		// constrained
		fprintf(stderr, "Constrained: \t");
		print_inst(stderr, mfunction, move);
		fprintf(stderr, "\n");
		add_to_worklist(ras, u);
		add_to_worklist(ras, v);
	} else if (are_coalesceble(ras, u, v)) {
		// coalesce
		combine(ras, u, v);
		add_to_worklist(ras, u);
	} else {
		fprintf(stderr, "Moving to active: \t");
		print_inst(stderr, mfunction, move);
		fprintf(stderr, "\n");
		wl_add(&ras->active_moves_wl, m);
	}
}

bool
assign_registers(RegAllocState *ras)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->spill_wl));
	assert(wl_empty(&ras->freeze_wl));
	assert(wl_empty(&ras->moves_wl));

	bool have_spill = false;
	MFunction *mfunction = ras->mfunction;

	// Physical registers are assigned themselves.
	for (size_t i = 0; i < R__MAX; i++) {
		ras->reg_assignment[i] = i;
	}

	Oper u;
	while (wl_take_back(&ras->stack, &u)) {
		assert(u >= R__MAX);
		fprintf(stderr, "Popping ");
		print_reg(stderr, u);
		fprintf(stderr, "\n");
		Oper used = 0;
		// If this one neighbours with some node that
		// has already color allocated (i.e. not on the
		// the stack) and it is not spilled (i.e. not R_NONE), make sure we
		// don't use the same register.
		GArena *gadj_list = &ras->adj_list[u];
		Oper *adj_list = garena_array(gadj_list, Oper);
		size_t adj_cnt = garena_cnt(gadj_list, Oper);
		for (size_t j = 0; j < adj_cnt; j++) {
			Oper neighbour = get_alias(ras, adj_list[j]);
			if (!wl_has(&ras->stack, neighbour) && ras->reg_assignment[neighbour] != R_NONE) {
				used |= 1 << (ras->reg_assignment[neighbour] - 1);
			}
		}


		Inst **moves = garena_array(&ras->gmoves, Inst *);
		GArena *gmove_list = &ras->move_list[u];
		Oper *move_list = garena_array(gmove_list, Oper);
		size_t move_cnt = garena_cnt(gmove_list, Oper);

		Oper reg = 0;
		for (size_t m = 0; m < move_cnt; m++) {
			Inst *move = moves[move_list[m]];
			Oper op1 = get_alias(ras, move->ops[0]);
			Oper op2 = get_alias(ras, move->ops[1]);
			assert(u == op1 || u == op2);
			Oper v = op1 != u ? op1 : op2;
			Oper v_reg = ras->reg_assignment[v];
			// This check for "has already been assigned" also
			// handles (skips) coalesced moves, i.e.
			//     mov t27, t27
			if (v_reg && (used & (1 << (v_reg - 1))) == 0) {
				fprintf(stderr, "Preferring ");
				print_reg(stderr, v_reg);
				fprintf(stderr, " for ");
				print_reg(stderr, u);
				fprintf(stderr, " due to ");
				print_reg(stderr, v);
				fprintf(stderr, "\n");
				reg = v_reg;
				goto done;
			}
		}

		for (size_t ri = 1; ri <= ras->reg_avail; ri++) {
			size_t mask = 1 << (ri - 1);
			if ((used & mask) == 0) {
				reg = ri;
				break;
			}
		}
		if (reg == 0) {
			fprintf(stderr, "Out of registers at ");
			print_reg(stderr, u);
			fprintf(stderr, "\n");
			ras->to_spill[u] = mfunction->stack_space;
			assert(mfunction->stack_space < 240);
			mfunction->stack_space += 8;
			have_spill = true;
		}
		done:
		ras->reg_assignment[u] = reg;
		fprintf(stderr, "allocated ");
		print_reg(stderr, u);
		fprintf(stderr, " to ");
		print_reg(stderr, reg);
		fprintf(stderr, "\n");
	}
	for (size_t i = 0; i < mfunction->vreg_cnt; i++) {
		if (is_alias(ras, i)) {
			fprintf(stderr, "Coalesced ");
			print_reg(stderr, i);
			fprintf(stderr, " to ");
			print_reg(stderr, get_alias(ras, i));
			fprintf(stderr, "\n");
		}
	}
	return !have_spill;
}

// Move all arguments and callee saved registers to temporaries at the
// start of the function. Then restore callee saved registers at the end
// of the function.

// Make all caller saved registers interfere with calls.


void
reg_alloc_function(RegAllocState *ras, MFunction *mfunction)
{
	print_mfunction(stderr, mfunction);

	reg_alloc_state_init_for_function(ras, mfunction);

	for (;;) {
		reg_alloc_state_reset(ras);
		liveness_analysis(ras);
		build_interference_graph(ras);
		calculate_spill_cost(ras);
		initialize_worklists(ras);

		Oper i;
	simplify:
		while (wl_take_back(&ras->simplify_wl, &i)) {
			simplify_one(ras, i);
		}
		if (wl_take(&ras->moves_wl, &i)) {
			coalesce_move(ras, i);
			goto simplify;
		}
		if (wl_take_back(&ras->freeze_wl, &i)) {
			freeze_one(ras, i);
			goto simplify;
		}
		if (!wl_empty(&ras->spill_wl)) {
			choose_and_spill_one(ras);
			goto simplify;
		}

		if (assign_registers(ras)) {
			break;
		}
		rewrite_program(ras);
	}

	// Fixup stack space amount reserved at the start of the function
	if (mfunction->make_stack_space) {
		IIMM(mfunction->make_stack_space) = mfunction->stack_space;
	}
	apply_reg_assignment(ras);
}