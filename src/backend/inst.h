#pragma once

#include "../utils/utils.h"
#include "../middleend/ir.h"

typedef struct Inst Inst;
struct Inst {
	Inst *next;
	Inst *prev;
	u8 kind;
	u8 subkind;
	u8 mode; // index into ModeDescriptor array
	bool writes_flags;
	bool reads_flags;
	bool flags_observed;
	Oper ops[];
};

#define IK(inst) ((inst)->kind)
#define IS(inst) ((inst)->subkind)
#define IM(inst) ((inst)->mode)
#define IRF(inst) ((inst)->reads_flags)
#define IWF(inst) ((inst)->writes_flags)
#define IOF(inst) ((inst)->flags_observed)

typedef struct {
	u8 def_start;
	u8 def_end;
	u8 use_start;
	u8 use_end;
	bool use_cnt_given_by_arg_cnt;
	bool def_cnt_given_by_arg_cnt;
	Oper *extra_defs;
	Oper *extra_uses;
} ModeDescriptor;




struct MBlock {
	Block *block;
	size_t index;
	// `insts.next` and `insts.prev` are respectively the head and tail of
	// circular doubly linked list of instructions
	Inst insts;
};

struct MFunction {
	Function *func;
	GArena *labels;
	MBlock **mblocks;
	size_t mblock_cnt;
	size_t stack_space;
	size_t vreg_cnt;
	Inst *make_stack_space;

	// use/def info
	Inst **only_def; // Inst * with the only definition of a vreg, if applicable
	u8 *def_count;
	u8 *use_count;
	u8 *block_use_count;
};

MFunction *mfunction_create(Arena *arena, Function *function, GArena *labels);
void mfunction_free(MFunction *mfunction);
Oper mfunction_reserve_stack_space(MFunction *mfunction, size_t size, size_t alignment);
void mfunction_finalize_stack(MFunction *mfunction);
void print_mfunction(FILE *f, MFunction *mfunction);
void dump_mfunction_after_pass(MFunction *mfunction, const char *pass_name);


MBlock *mblock_create(Arena *arena, Block *block);

void remove_inst(Inst *inst);
void prepend_inst(Inst *pos, Inst *new);
void append_inst(Inst *pos, Inst *new);


void for_each_def(Inst *inst, void (*fun)(void *user_data, Oper *def), void *user_data);
void for_each_use(Inst *inst, void (*fun)(void *user_data, Oper *use), void *user_data);

void increment_count(void *user_data, Oper *oper);
void decrement_count(void *user_data, Oper *oper);

void calculate_def_use_info(MFunction *mfunction);
