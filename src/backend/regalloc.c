#include "../utils/arena.h"
#include "../utils/worklist.h"
#include "../utils/bitset.h"
#include "../utils/utils.h"
#include "inst.h"
#include "x86-64/x86-64.h"

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
	Oper reg_avail;
	Oper first_vreg;

	// Did this function have any spills yet?
	// (Used to apply coalescing on first potential spill).
	bool had_spill;

	// Final register allocation
	Oper *reg_assignment;

	Oper *to_spill;
	Oper *alias;

	// Spill cost related
	u16 *def_cost;
	u16 *use_cost;
	u16 *move_cost;
	WorkList unspillable; // set of unspillable vregs

	// Degrees of nodes.
	u32 *degree;

	// Interference Graph
	BitSet matrix; // bit map (u8/bool per vreg)
	GArena *adj_list;

	WorkList live_set;
	WorkList uninterrupted;
	WorkList ever_interrupted; // set of vregs which are interrupted at least once
	WorkList block_work_list;
	WorkList *live_in;

	// Worklists for the different register allocation phases
	WorkList spill_wl;
	WorkList freeze_wl;
	WorkList simplify_wl;
	WorkList active_moves_wl;
	WorkList inactive_moves_wl;
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
		.first_vreg = R__MAX,
	};
	return ras;
}

void add_interference(RegAllocState *ras, Oper u, Oper v);

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
		GROW_ARRAY(ras->move_cost, ras->vreg_capacity);
		wl_grow(&ras->unspillable, ras->vreg_capacity);
		GROW_ARRAY(ras->degree, ras->vreg_capacity);
		bs_grow(&ras->matrix, ras->vreg_capacity * ras->vreg_capacity);
		GROW_ARRAY(ras->adj_list, ras->vreg_capacity);
		ZERO_ARRAY(&ras->adj_list[old_vreg_capacity], ras->vreg_capacity - old_vreg_capacity);
		wl_grow(&ras->live_set, ras->vreg_capacity);
		wl_grow(&ras->uninterrupted, ras->vreg_capacity);
		wl_grow(&ras->ever_interrupted, ras->vreg_capacity);
		for (size_t i = 0; i < old_block_capacity; i++) {
			wl_grow(&ras->live_in[i], ras->vreg_capacity);
		}
		wl_grow(&ras->spill_wl, ras->vreg_capacity);
		wl_grow(&ras->freeze_wl, ras->vreg_capacity);
		wl_grow(&ras->simplify_wl, ras->vreg_capacity);
		//wl_grow(&ras->active_moves_wl, ras->vreg_capacity);
		//wl_grow(&ras->inactive_moves_wl, ras->vreg_capacity);
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
	ZERO_ARRAY(ras->move_cost, ras->mfunction->vreg_cnt);
	wl_reset(&ras->unspillable);
	ZERO_ARRAY(ras->degree, ras->mfunction->vreg_cnt);
	bs_reset(&ras->matrix, ras->N);
	for (size_t i = 0; i < ras->mfunction->vreg_cnt; i++) {
		garena_restore(&ras->adj_list[i], 0);
	}
	wl_reset(&ras->live_set);
	wl_reset(&ras->uninterrupted);
	wl_reset(&ras->ever_interrupted);
	wl_reset(&ras->block_work_list);
	for (size_t i = 0; i < ras->mfunction->mblock_cnt; i++) {
		wl_reset(&ras->live_in[i]);
	}
	wl_reset(&ras->spill_wl);
	wl_reset(&ras->freeze_wl);
	wl_reset(&ras->simplify_wl);
	//wl_reset(&ras->active_moves_wl);
	//wl_reset(&ras->inactive_moves_wl);
	wl_reset(&ras->stack);
	garena_restore(&ras->gmoves, 0);
	for (size_t i = 0; i < ras->mfunction->vreg_cnt; i++) {
		garena_restore(&ras->move_list[i], 0);
	}

	// Add interferences among physical registers.
	for (Oper u = 1; u < ras->first_vreg; u++) {
		for (Oper v = u + 1; v < ras->first_vreg; v++) {
			add_interference(ras, u, v);
		}
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
	FREE_ARRAY(ras->move_cost, ras->vreg_capacity);
	wl_free(&ras->unspillable);
	FREE_ARRAY(ras->degree, ras->vreg_capacity);
	bs_free(&ras->matrix, ras->vreg_capacity);
	for (size_t i = 0; i < ras->vreg_capacity; i++) {
		garena_free(&ras->adj_list[i]);
	}
	FREE_ARRAY(ras->adj_list, ras->vreg_capacity);
	wl_free(&ras->live_set);
	wl_free(&ras->uninterrupted);
	wl_free(&ras->ever_interrupted);
	wl_reset(&ras->block_work_list);
	wl_free(&ras->block_work_list);
	for (size_t i = 0; i < ras->block_capacity; i++) {
		wl_free(&ras->live_in[i]);
	}
	FREE_ARRAY(ras->live_in, ras->block_capacity);
	wl_free(&ras->spill_wl);
	wl_free(&ras->freeze_wl);
	wl_free(&ras->simplify_wl);
	wl_free(&ras->active_moves_wl);
	wl_free(&ras->inactive_moves_wl);
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

	// But need to set that this function didn't have yet any spills.
	ras->had_spill = false;
}

static bool
is_physical(RegAllocState *ras, Oper u)
{
	return u < ras->first_vreg;
}

static bool
is_significant(RegAllocState *ras, Oper u)
{
	return ras->degree[u] >= ras->reg_avail;
}


static bool
is_alias(RegAllocState *ras, Oper u)
{
	return ras->alias[u] != u;
}

static Oper
get_alias(RegAllocState *ras, Oper u)
{
	while (u != ras->alias[u]) {
		u = ras->alias[u];
	}
	return u;
}

static Oper
bitmatrix_index(RegAllocState *ras, Oper u, Oper v)
{
	if (v < u) {
		Oper tmp = v;
		v = u;
		u = tmp;
	}
	return u * ras->n + v;
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
	Oper index = bitmatrix_index(ras, u, v);
	return bs_test(&ras->matrix, index);
}

void
add_interference(RegAllocState *ras, Oper u, Oper v)
{
	assert(u < ras->mfunction->vreg_cnt);
	assert(v < ras->mfunction->vreg_cnt);
	if (u == v || are_interfering(ras, u, v)) {
		return;
	}
	Oper index = bitmatrix_index(ras, u, v);
	assert(!bs_test(&ras->matrix, index));
	bs_set(&ras->matrix, index);
	// Only populate adjacency lists for vregs. Adjacency lists for physical
	// regs would be too large. We don't actually need them - color
	// assigning needs only neighbours of vregs (since we have to choose a
	// color distinct from neighbours), and for coalescing heuristic we use
	// George's test, which doesn't use adjacency lists, unlike Briggs'
	// test (which we use for vregs).
	if (!is_physical(ras, u)) {
		garena_push_value(&ras->adj_list[u], Oper, v);
	}
	if (!is_physical(ras, v)) {
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
	wl_remove(live_set, *oper);
}

void
add_to_set(void *user_data, Oper *oper)
{
	WorkList *live_set = user_data;
	wl_add(live_set, *oper);
}

void
live_step(WorkList *live_set, MFunction *mfunction, Inst *inst)
{
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

static bool
is_move(Inst *inst)
{
	// NOTE: This is x86-64 specific, and should be replaced if we ever
	// support multiple architectures.
	return IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Cr;
}

void
add_move(RegAllocState *ras, Inst *inst)
{
	Oper dest = inst->ops[0];
	Oper src = inst->ops[1];
	if (dest == src) {
		// If this move is already coalesced (when coalescing
		// was applied for the first potential spill), we get a move to
		// itself instruction. Peepholer will definitely remove it, but
		// we won't do anything useful with it anyways, so just remove
		// it.
		inst->prev->next = inst->next;
		inst->next->prev = inst->prev;
		return;
	}
	size_t index = garena_cnt(&ras->gmoves, Inst *);
	garena_push_value(&ras->gmoves, Inst *, inst);
	garena_push_value(&ras->move_list[dest], Oper, index);
	garena_push_value(&ras->move_list[src], Oper, index);
}

void
interference_step(RegAllocState *ras, WorkList *live_set, Inst *inst)
{
	// Special handling of moves:
	// 1) We don't want to introduce interference between move source and
	//    destination.
	// 2) We want to note all moves and for all nodes the moves they are
	//    contained in, because we want to try to coalesce the moves later.
	if (is_move(inst)) {
		// Remove uses from live to prevent interference between move
		// destination and source.
		for_each_use(inst, remove_from_set, live_set);

		// Accumulate moves.
		add_move(ras, inst);
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

	// Update the liveness for this instruction.
	live_step(live_set, ras->mfunction, inst);
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
	ras->to_spill[vreg] = 0;
	return vreg;
}

bool
is_to_be_spilled(RegAllocState *ras, Oper t)
{
	// NOTE: We make sure that even `to_spill` is in bounds even for vregs
	// introduced for spill code, see `get_fresh_vreg_for_spill` above.
	//
	// `to_spill[t]` = 0 => not spilled
	return ras->to_spill[t] != 0;
}

Oper
spill_displacement(RegAllocState *ras, Oper t)
{
	// `to_spill[t]` = 0 => not spilled
	// `to_spill[t]` > 0 => spilled, displacement is `to_spill[t]`
	return ras->to_spill[t];
}

void
insert_loads_of_spilled(void *user_data, Oper *src)
{
	SpillState *ss = user_data;
	RegAllocState *ras = ss->ras;
	if (!is_to_be_spilled(ras, *src)) {
		return;
	}
	Oper temp = get_fresh_vreg_for_spill(ras);
	ras->to_spill[temp] = ras->to_spill[*src];
	Oper disp = spill_displacement(ras, *src);
	Inst *load = create_load_with_disp(ras->arena, temp, R_RBP, disp);
	prepend_inst(ss->inst, load);

	*src = temp;
}

void
insert_stores_of_spilled(void *user_data, Oper *dest)
{
	SpillState *ss = user_data;
	RegAllocState *ras = ss->ras;
	if (!is_to_be_spilled(ras, *dest)) {
		return;
	}
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

	Oper disp = spill_displacement(ras, *dest);
	Inst *store = create_store_with_disp(ras->arena, R_RBP, disp, temp);
	append_inst(ss->inst, store);

	// Advance the current instruction pointer to the store instruction.
	// This means that if we insert multiple stores for a single
	// instruction, we insert them in the right order and additionally skip
	// the store instructions below where we iterate over all instructions.
	ss->inst = store;

	*dest = temp;
}

// Tries to special case spills of move (copy) instructions, which can often get
// rid of the copy instruction. Returns whether inserting loads and stores
// should be skipped.
void
spill_move(RegAllocState *ras, Inst *inst)
{
	Oper dest = inst->ops[0];
	Oper src = inst->ops[1];
	bool spill_dest = is_to_be_spilled(ras, dest);
	bool spill_src = is_to_be_spilled(ras, src);
	if (spill_dest && spill_src) {
		Oper dest_disp = spill_displacement(ras, dest);
		Oper src_disp = spill_displacement(ras, src);
		// If this would be essentially:
		//    mov [rbp+X], [rbp+X]
		// we can just get rid of the copy.
		if (dest_disp == src_disp) {
			remove_inst(inst);
		}
		// Otherwise we want:
		// mov temp, [rbp+Y]
		// mov [rbp+X], temp
		Oper temp = get_fresh_vreg_for_spill(ras);
		Inst *load = create_load_with_disp(ras->arena, temp, R_RBP, src_disp);
		Inst *store = create_store_with_disp(ras->arena, R_RBP, dest_disp, temp);
		prepend_inst(inst, load);
		append_inst(inst, store);
		remove_inst(inst);
	} else if (spill_dest) {
		inst->mode = M_Mr;
		IREG(inst) = src;
		IBASE(inst) = R_RBP;
		IDISP(inst) = spill_displacement(ras, dest);
	} else if (spill_src) {
		inst->mode = M_CM;
		IREG(inst) = dest;
		IBASE(inst) = R_RBP;
		IDISP(inst) = spill_displacement(ras, src);
	}
}

// Add spill code.
void
rewrite_program(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	SpillState ss_ = {
		.ras = ras,
		.spill_start = mfunction->vreg_cnt,
	}, *ss = &ss_;
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		// NOTE: Beware subtlety ahead:
		// If we insert new store instructions, we want to skip and not
		// investigate them. For this we iterate with `ss->inst`, which
		// is advanced every time a new store instruction is inserted.
		for (Inst *inst = mblock->insts.next; inst != &mblock->insts; inst = ss->inst->next) {
			ss->inst = inst;
			if (is_move(inst)) {
				spill_move(ras, inst);
				continue;
			}
			// Add loads for all spilled uses.
			for_each_use(inst, insert_loads_of_spilled, ss);
			// Add stores for all spilled defs.
			for_each_def(inst, insert_stores_of_spilled, ss);
		}
	}

	dump_mfunction_after_pass(mfunction, "spill insertion");
}

void
apply_reg_assignment(RegAllocState *ras)
{
	MFunction *mfunction = ras->mfunction;
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		for (Inst *inst = mblock->insts.next; inst != &mblock->insts; inst = inst->next) {
			// TODO: different number of register slots per target
			// TODO: store number of registers in mode
			ModeDescriptor *mode = &mode_descs[inst->mode];
			size_t end = mode->use_end > mode->def_end ? mode->use_end : mode->def_end;
			for (size_t i = 0; i < end; i++) {
				inst->ops[i] = ras->reg_assignment[get_alias(ras, inst->ops[i])];
			}
		}
	}

	dump_mfunction_after_pass(mfunction, "register assignment");
}

void
apply_coalescing(RegAllocState *ras)
{
	// Copy the current state of aliasing into register assignemt and then
	// apply it with the function above.
	COPY_ARRAY(ras->reg_assignment, ras->alias, ras->mfunction->vreg_cnt);
	apply_reg_assignment(ras);
	// Since `assign_registers` expects the register assignment to be zeroed
	// out, we reset it.
	ZERO_ARRAY(ras->reg_assignment, ras->mfunction->vreg_cnt);
}


u16
cost_in_depth(u64 depth)
{
	return 1 << (3 * depth);
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
	if (wl_remove(&ras->uninterrupted, def) && !wl_has(&ras->ever_interrupted, def)) {
		wl_add(&ras->unspillable, def);
	}
	ras->def_cost[def] += cost_in_depth(ras->mblock->block->depth);
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
			Oper u = uninterrupted->dense[i];
			wl_add(&ras->ever_interrupted, u);
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
	ras->use_cost[use] += cost_in_depth(ras->mblock->block->depth);
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
		ras->mblock = mblock;
		Block *block = mblock->block;
		get_live_out(ras, block, live_set);
		// We currently can't make unspillable those vregs whose live
		// ranges cross basic block boundaries. Make sure we don't mark
		// them unspillable by marking them as "interrupted somewhere"
		// (in this case by basic block boundary).
		FOR_EACH_WL_INDEX(live_set, i) {
			Oper live_across_block = live_set->dense[i];
			wl_add(&ras->ever_interrupted, live_across_block);
		}
		for (Inst *inst = mblock->insts.prev; inst != &mblock->insts; inst = inst->prev) {
			for_each_def(inst, mark_defs_with_uninterrupted_uses_unspillable, ras);
			for_each_use(inst, detect_interrupting_deaths, ras);
			for_each_use(inst, add_live, ras);
			if (is_move(inst)) {
				u16 cost = cost_in_depth(block->depth);
				ras->move_cost[inst->ops[0]] += cost;
				ras->move_cost[inst->ops[1]] += cost;
			}
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
		Block *block = mblock->block;
		get_live_out(ras, block, live_set);
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
		Block *block = mblock->block;
		get_live_out(ras, block, live_set);
		for (Inst *inst = mblock->insts.prev; inst != &mblock->insts; inst = inst->prev) {
			interference_step(ras, live_set, inst);
			live_step(live_set, mfunction, inst);
		}
	}
}

void
for_each_adjacent(RegAllocState *ras, Oper u, void (*fun)(RegAllocState *ras, Oper adj))
{
	// We don't keep adjacency lists for physical registers, assert that we
	// don't try to access them.
	assert(!is_physical(ras, u));

	GArena *gadj_list = &ras->adj_list[u];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t i = 0; i < adj_cnt; i++) {
		Oper adj = adj_list[i];
		if (wl_has(&ras->stack, adj) || is_alias(ras, adj)) {
			continue;
		}
		fun(ras, adj);
	}
}

size_t
for_each_move(RegAllocState *ras, Oper u, void (*fun)(RegAllocState *ras, Oper u, Oper m, Inst *move))
{
	Inst **moves = garena_array(&ras->gmoves, Inst *);
	GArena *gmove_list = &ras->move_list[u];
	Oper *move_list = garena_array(gmove_list, Oper);
	size_t move_cnt = garena_cnt(gmove_list, Oper);
	size_t cnt = 0;
	for (size_t i = 0; i < move_cnt; i++) {
		Oper move_index = move_list[i];
		if (wl_has(&ras->inactive_moves_wl, move_index) || wl_has(&ras->active_moves_wl, move_index)) {
			fun(ras, u, move_index, moves[move_index]);
			cnt++;
		}
	}
	return cnt;
}

void
move_related_callback(RegAllocState *ras, Oper u, Oper m, Inst *move)
{
	// Nothing to do. A node is move related if there is at least one move
	// in the move worklist or active moves worklist, and this is decided by
	// the return value of the iterator.
	(void) ras;
	(void) u;
	(void) m;
	(void) move;
}

bool
is_move_related(RegAllocState *ras, Oper u)
{
	// Node is move related if the callback is called at least once.
	// NOTE: We could make this faster by keeping number of moves that are
	// not yet given up (frozen) and not coalesced. But the bookkeeping is
	// not as straightforward.
	return for_each_move(ras, u, move_related_callback) > 0;
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
		wl_grow(&ras->active_moves_wl, ras->move_capacity);
		wl_grow(&ras->inactive_moves_wl, ras->move_capacity);
	}
	wl_reset(&ras->active_moves_wl);
	wl_init_all(&ras->active_moves_wl, move_cnt);
	wl_reset(&ras->inactive_moves_wl);

	size_t vreg_cnt = ras->mfunction->vreg_cnt;
	for (Oper u = ras->first_vreg; u < vreg_cnt; u++) {
		GArena *gadj_list = &ras->adj_list[u];
		size_t adj_cnt = garena_cnt(gadj_list, Oper);
		assert(adj_cnt == ras->degree[u]);
		if (is_significant(ras, u)) {
			wl_add(&ras->spill_wl, u);
		} else if (is_move_related(ras, u)) {
			wl_add(&ras->freeze_wl, u);
		} else {
			wl_add(&ras->simplify_wl, u);
		}
	}
}

double
spill_metric(RegAllocState *ras, Oper u)
{
	if (wl_has(&ras->unspillable, u)) {
		return 1 / 0.0;
	}
	Oper cost = 2 * ras->def_cost[u] + 2 * ras->use_cost[u] - ras->move_cost[u];
	return (double) cost / ras->degree[u];
}

void
enable_move(RegAllocState *ras, Oper u, Oper m, Inst *move)
{
	(void) u;
	if (wl_remove(&ras->inactive_moves_wl, m)) {
		wl_add(&ras->active_moves_wl, m);
	}
}

void
enable_moves_for_one(RegAllocState *ras, Oper u)
{
	for_each_move(ras, u, enable_move);
}

void
decrement_degree(RegAllocState *ras, Oper u)
{
	assert(ras->degree[u] > 0);
	if (ras->degree[u]-- == ras->reg_avail) {
		assert(!is_physical(ras, u));
		enable_moves_for_one(ras, u);
		for_each_adjacent(ras, u, enable_moves_for_one);
		if (wl_has(&ras->freeze_wl, u)) {
			// If we are decrementing degree of a move related node,
			// it becoming insignificant doesn't change it's status,
			// because it should remain in the freeze worklist until
			// all the moves are processed.
			return;
		}
		assert(wl_remove(&ras->spill_wl, u));
		if (is_move_related(ras, u)) {
			wl_add(&ras->freeze_wl, u);
		} else {
			wl_add(&ras->simplify_wl, u);
		}
	}
}

void
freeze_move(RegAllocState *ras, Oper u, Oper m, Inst *move)
{
	if (!wl_remove(&ras->inactive_moves_wl, m)) {
		assert(wl_remove(&ras->active_moves_wl, m));
	}
	Oper op1 = get_alias(ras, move->ops[0]);
	Oper op2 = get_alias(ras, move->ops[1]);
	assert(u == op1 || u == op2);
	Oper v = op1 != u ? op1 : op2;
	if (!is_move_related(ras, v) && !is_significant(ras, v)) {
		assert(wl_remove(&ras->freeze_wl, v));
		wl_add(&ras->simplify_wl, v);
	}
}

void
freeze_moves(RegAllocState *ras, Oper u)
{
	for_each_move(ras, u, freeze_move);
}

void
freeze_one(RegAllocState *ras, Oper u)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->active_moves_wl));

	wl_add(&ras->simplify_wl, u);
	freeze_moves(ras, u);
}

void
simplify_one(RegAllocState *ras, Oper u)
{
	assert(!is_alias(ras, u));

	wl_add(&ras->stack, u);
	for_each_adjacent(ras, u, decrement_degree);
}

void
choose_and_spill_one(RegAllocState *ras)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->active_moves_wl));
	assert(!wl_empty(&ras->spill_wl));

	if (!ras->had_spill) {
		apply_coalescing(ras);
		ras->had_spill = true;
	}

	Oper candidate = OPER_MAX;
	double max = 1 / 0.0;
	WorkList *spill_wl = &ras->spill_wl;
	FOR_EACH_WL_INDEX(spill_wl, j) {
		Oper u = spill_wl->dense[j];
		double curr = spill_metric(ras, u);
		// Prefer for spill either more beneficial candidates (with
		// smaller metric) or "earlier" vregs ("smaller index"). This
		// comes in handy for spilling callee saved registers, where we
		// want to spill `rbx` first, since encoding it is (sometimes)
		// shorter.
		if (curr < max || (curr == max && u < candidate)) {
			max = curr;
			candidate = u;
		}
	}

	assert(candidate != OPER_MAX);
	assert(max < 1 / 0.0);

	wl_remove(&ras->spill_wl, candidate);
	wl_add(&ras->simplify_wl, candidate);
	freeze_moves(ras, candidate);
}

void
decrement_move_cnt(RegAllocState *ras, Oper u)
{
	if (!is_move_related(ras, u) && !is_significant(ras, u)) {
		assert(!is_physical(ras, u));
		wl_remove(&ras->freeze_wl, u);
		wl_add(&ras->simplify_wl, u);
	}
}

size_t
significant_neighbour_cnt(RegAllocState *ras, Oper u)
{
	size_t n = 0;
	assert(u >= ras->first_vreg);
	GArena *gadj_list = &ras->adj_list[u];
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
george_heuristic(RegAllocState *ras, Oper u, Oper v)
{
	assert(v >= ras->first_vreg);
	GArena *gadj_list = &ras->adj_list[v];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t j = 0; j < adj_cnt; j++) {
		Oper t = adj_list[j];
		if (wl_has(&ras->stack, t) || is_alias(ras, t)) {
			continue;
		}
		if (is_significant(ras, t) && !are_interfering(ras, t, u)) {
			return false;
		}
	}
	return true;
}

bool
briggs_heuristic(RegAllocState *ras, Oper u, Oper v)
{
	size_t n = significant_neighbour_cnt(ras, u) + significant_neighbour_cnt(ras, v);
	return n < ras->reg_avail;
}

bool
are_coalesceble(RegAllocState *ras, Oper u, Oper v)
{
	// At this point `u` may be precolored (physical register) and `v`
	// definitely isn't. This means that `u`'s list of neighbours may not be
	// available.
	bool coalescable = george_heuristic(ras, u, v);
	if (!coalescable && !is_physical(ras, u)) {
		coalescable = briggs_heuristic(ras, u, v);;
	}
	return coalescable;
}

void
combine(RegAllocState *ras, Oper u, Oper v)
{
	assert(v >= ras->first_vreg);
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

	// Add costs of `v` to `u`.
	ras->def_cost[u] += ras->def_cost[v];
	ras->use_cost[u] += ras->use_cost[v];
	ras->move_cost[u] += ras->move_cost[v];

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
		wl_add(&ras->spill_wl, u);
	}
}

void
coalesce_move(RegAllocState *ras, Oper m)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->simplify_wl));

	Inst **moves = garena_array(&ras->gmoves, Inst *);
	Inst *move = moves[m];

	Oper u = get_alias(ras, move->ops[0]);
	Oper v = get_alias(ras, move->ops[1]);
	if (v < u) {
		Oper tmp = u;
		u = v;
		v = tmp;
	}

	if (u == v) {
		// already coalesced
		decrement_move_cnt(ras, u);
	} else if (is_physical(ras, v) || are_interfering(ras, u, v)) {
		// constrained
		decrement_move_cnt(ras, u);
		decrement_move_cnt(ras, v);
	} else if (are_coalesceble(ras, u, v)) {
		// coalesce
		combine(ras, u, v);
		decrement_move_cnt(ras, u);
	} else {
		wl_add(&ras->inactive_moves_wl, m);
	}
}

Oper
find_register_for(RegAllocState *ras, Oper u)
{
	assert(u >= ras->first_vreg);
	Oper used = 0;
	// If this one neighbours with some node that
	// has already color allocated (i.e. not on the
	// the stack) and it is not spilled (i.e. not R_NONE), make sure we
	// don't use the same register.
	GArena *gadj_list = &ras->adj_list[u];
	Oper *adj_list = garena_array(gadj_list, Oper);
	size_t adj_cnt = garena_cnt(gadj_list, Oper);
	for (size_t j = 0; j < adj_cnt; j++) {
		Oper v = get_alias(ras, adj_list[j]);
		if (wl_has(&ras->stack, v) || is_to_be_spilled(ras, v)) {
			continue;
		}
		used |= 1U << ras->reg_assignment[v];
	}

	Inst **moves = garena_array(&ras->gmoves, Inst *);
	GArena *gmove_list = &ras->move_list[u];
	Oper *move_list = garena_array(gmove_list, Oper);
	size_t move_cnt = garena_cnt(gmove_list, Oper);
	for (size_t m = 0; m < move_cnt; m++) {
		Inst *move = moves[move_list[m]];
		Oper op1 = get_alias(ras, move->ops[0]);
		Oper op2 = get_alias(ras, move->ops[1]);
		assert(u == op1 || u == op2);
		Oper v = op1 != u ? op1 : op2;
		// skip also coalesced moves (mov t27, t27)
		if (u == v || are_interfering(ras, u, v) || wl_has(&ras->stack, v) || is_to_be_spilled(ras, v)) {
			continue;
		}
		Oper reg = ras->reg_assignment[v];
		if ((used & (1U << reg)) == 0) {
			return reg;
		}
	}

	for (size_t reg = 1; reg <= ras->reg_avail; reg++) {
		size_t mask = 1 << reg;
		if ((used & mask) == 0) {
			return reg;
		}
	}

	return R_NONE;
}

void
spill_virtual_register(RegAllocState *ras, Oper u)
{
	ras->to_spill[u] = mfunction_reserve_stack_space(ras->mfunction, 8, 8);
	assert(-ras->to_spill[u] < 512);
}

bool
assign_registers(RegAllocState *ras)
{
	assert(wl_empty(&ras->simplify_wl));
	assert(wl_empty(&ras->spill_wl));
	assert(wl_empty(&ras->freeze_wl));
	assert(wl_empty(&ras->active_moves_wl));

	bool have_spill = false;

	// Physical registers are assigned themselves.
	for (size_t i = 0; i < ras->first_vreg; i++) {
		ras->reg_assignment[i] = i;
	}

	Oper u;
	while (wl_take_back(&ras->stack, &u)) {
		Oper reg = find_register_for(ras, u);

		if (reg == R_NONE) {
			spill_virtual_register(ras, u);
			have_spill = true;
			continue;
		}

		ras->reg_assignment[u] = reg;
	}

	return !have_spill;
}

void
simplify(RegAllocState *ras)
{
	Oper i;
simplify:
	while (wl_take_back(&ras->simplify_wl, &i)) {
		simplify_one(ras, i);
	}
	if (wl_take(&ras->active_moves_wl, &i)) {
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
}

void
reg_alloc_function(RegAllocState *ras, MFunction *mfunction)
{
	reg_alloc_state_init_for_function(ras, mfunction);
	for (;;) {
		reg_alloc_state_reset(ras);
		liveness_analysis(ras);
		build_interference_graph(ras);
		calculate_spill_cost(ras);
		initialize_worklists(ras);
		simplify(ras);
		if (assign_registers(ras)) {
			break;
		}
		rewrite_program(ras);
	}
	apply_reg_assignment(ras);
}
