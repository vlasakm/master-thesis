#pragma once

#include "utils.h"
#include "ir.h"

typedef struct Inst Inst;
struct Inst {
	Inst *next;
	Inst *prev;
	u8 kind;
	u8 subkind;
	u8 mode; // index into InsFormat
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
} InsFormat;




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
void print_mfunction(FILE *f, MFunction *mfunction);

MBlock *mblock_create(Arena *arena, Block *block);

void for_each_def(Inst *inst, void (*fun)(void *user_data, Oper *def), void *user_data);
void for_each_use(Inst *inst, void (*fun)(void *user_data, Oper *use), void *user_data);
