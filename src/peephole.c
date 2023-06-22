#include "utils.h"
#include "inst.h"
#include "x86-64.h"

bool
try_replace_by_immediate(MFunction *mfunction, Inst *inst, Oper o)
{
	Inst *def = mfunction->only_def[o];
	if (!def) {
		return false;
	}
	assert(mfunction->def_count[o] == 1);
	if (IK(def) != IK_MOV || IS(def) != MOV || IM(def) != M_CI) {
		return false;
	}
	if (!pack_into_oper(get_imm64(def), &IIMM(inst))) {
		return false;
	}
	if (--mfunction->use_count[IREG(def)] == 0) {
		assert(--mfunction->def_count[IREG(def)] == 0);
		def->prev->next = def->next;
		def->next->prev = def->prev;
	}
	return true;
}

bool
try_combine_memory(MFunction *mfunction, Inst *inst)
{
	Inst *def = mfunction->only_def[IBASE(inst)];
	if (!def) {
		return false;
	}
	assert(mfunction->def_count[IBASE(inst)] == 1);
	if (IK(def) != IK_MOV || IS(def) != LEA) {
		return false;
	}
	// If this isn't RIP-relative addressing, and base isn't RBP, then we
	// bail out, if the definition may be ambigous.
	if (IBASE(def) != R_NONE && IBASE(def) != R_RBP && mfunction->def_count[IBASE(def)] > 1) {
		return false;
	}
	if (IINDEX(inst)) {
		// We could try harder to support some combinations, but we
		// currently don't. E.g. if only has one index or both have same
		// index and both scales are 1 (making the combined scale 2),
		// etc.
		return false;
	}
	if (IBASE(def) == R_NONE) {
		// Assert that RIP-relative addressing doesn't have an index.
		assert(IINDEX(def) == R_NONE);
	}
	// If the current instruction is RIP-relative or it has a scale, then we
	// also don't do anything currently.
	if (IBASE(inst) == R_NONE || ISCALE(inst) != 0) {
		return false;
	}
	// Try to add together the displacements. If they don't fit into 32
	// bits, then we bail out.
	u64 disp = sext_imm32(IDISP(inst)) + sext_imm32(IDISP(def));
	if (!pack_into_oper(disp, &IDISP(inst))) {
		return false;
	}
	IBASE(inst) = IBASE(def);
	// NOTE: ISCALE essentially copies ILABEL in case of rip relative
	// addressing
	ISCALE(inst) = ISCALE(def);
	IINDEX(inst) = IINDEX(def);
	if (--mfunction->use_count[IREG(def)] == 0) {
		assert(--mfunction->def_count[IREG(def)] == 0);
		def->prev->next = def->next;
		def->next->prev = def->prev;
	}
	return true;
}

bool
try_combine_label(MFunction *mfunction, Inst *inst)
{
	Inst *def = mfunction->only_def[IREG(inst)];
	if (!def) {
		return false;
	}
	assert(mfunction->def_count[IREG(inst)] == 1);
	// We are looking for rip relative addressing (i.e. IBASE == R_NONE),
	// but also without any other displacement other than the label (i.e.
	// IDISP == 0).
	if (IK(def) != IK_MOV || IS(def) != LEA || IBASE(def) != R_NONE || IDISP(def) != 0) {
		return false;
	}
	ILABEL(inst) = ILABEL(def);
	if (--mfunction->use_count[IREG(def)] == 0) {
		def->prev->next = def->next;
		def->next->prev = def->prev;
	}
	return true;
}

void
peephole(MFunction *mfunction, Arena *arena, bool last_pass)
{
	(void) arena;
	u8 *use_cnt = mfunction->use_count;
	u8 *def_cnt = mfunction->def_count;
	Inst **defs = mfunction->only_def;
	u8 *block_use_cnt = mfunction->block_use_count;
	print_str(stderr, mfunction->func->name);
	fprintf(stderr, "\n");
	for (size_t b = 0; b < mfunction->mblock_cnt; b++) {
		MBlock *mblock = mfunction->mblocks[b];
		if (!mblock) {
			continue;
		}
		Inst *inst = mblock->insts.next;
		while (inst != &mblock->insts) {
			print_inst(stderr, mfunction, inst);
			fprintf(stderr, "\n");
			fflush(stderr);
			// mov rax, rax
			// =>
			// [deleted]
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Cr && IREG(inst) == IREG2(inst)) {
				use_cnt[IREG(inst)]--;
				def_cnt[IREG(inst)]--;
				inst->prev->next = inst->next;
				inst->next->prev = inst->prev;
				goto next;
			}

			// mov t13, ... (where t13 is not used further)
			// =>
			// deleted
			//
			// xor t14, t14 (where t14 is not used further)
			// =>
			// deleted
			if ((IM(inst) == M_CI || IM(inst) == M_Cr || IM(inst) == M_CM || IM(inst) == M_Cn) && use_cnt[IREG(inst)] == 0) {
				def_cnt[IREG(inst)]--;
				for_each_use(inst, decrement_count, use_cnt);
				inst->prev->next = inst->next;
				inst->next->prev = inst->prev;
				goto next;
			}

			// cmp rax, 0
			// =>
			// test rax, rax
			if (IK(inst) == IK_BINALU && IS(inst) == G1_CMP && IM(inst) == M_ri && IIMM(inst) == 0) {
				use_cnt[IREG(inst)]++;
				IS(inst) = G1_TEST;
				IM(inst) = M_rr;
				IREG2(inst) = IREG(inst);
				continue;
			}

			// test/cmp ..., ... (and no flags observed)
			// =>
			// [deleted]
			if (IK(inst) == IK_BINALU && (IS(inst) == G1_TEST || IS(inst) == G1_CMP) && !IOF(inst)) {
				for_each_use(inst, decrement_count, use_cnt);
				inst->prev->next = inst->next;
				inst->next->prev = inst->prev;
				goto next;
			}

			// mov t20, 0 (and flags not observed)
			// =>
			// xor t20, t20 (sets flags, but noone will read them)
			if (false && IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_CI && get_imm64(inst) == 0 && !IOF(inst)) {
				// the second occurence doesn't count as use
				IK(inst) = IK_BINALU;
				IS(inst) = G1_XOR;
				IM(inst) = M_Cn;
				IWF(inst) = true;
				IREG2(inst) = IREG(inst);
				continue;
			}

			// add rax, 0 (and flags not observed)
			// =>
			// [deleted]
			//
			// add rax, 0 (and flags observed)
			// =>
			// test rax, rax
			if (IK(inst) == IK_BINALU && IM(inst) == M_Ri && (((IS(inst) == G1_ADD || IS(inst) == G1_SUB || IS(inst) == G1_OR || IS(inst) == G1_XOR) && IIMM(inst) == 0) || (IS(inst) == G1_IMUL && IIMM(inst) == 1))) {
				if (IOF(inst)) {
					IK(inst) = IK_BINALU;
					IS(inst) = G1_TEST;
					IM(inst) = M_rr;
					IREG2(inst) = IREG(inst);
				} else {
					inst->prev->next = inst->next;
					inst->next->prev = inst->prev;
				}
				goto next;
			}

			// add ..., 1 (and flags not observed)
			// =>
			// inc ...
			// Probably not worth it.
			// https://www.agner.org/optimize/microarchitecture.pdf
			if (false) {}

			if (last_pass && IK(inst) == IK_ENTRY) {
				inst->prev->next = inst->next;
				inst->next->prev = inst->prev;
				goto next;
			}

			Inst *prev = inst->prev;

			// lea t32, [rbp-16] // IK_MOV ANY M_C*
			// mov t14, t32
			// =>
			// lea t14, [rbp-16]
			//
			// mov t27, 1
			// mov t18, t27
			// =>
			// mov t18, 1
			if (IK(inst) == IK_MOV && IM(inst) == M_Cr && IK(prev) != IK_CMOVCC && (IM(prev) == M_CI || IM(prev) == M_Cr || IM(prev) == M_CM) && IREG(prev) == IREG2(inst) && use_cnt[IREG(prev)] == 1) {
				def_cnt[IREG(prev)]--;
				use_cnt[IREG(prev)]--;
				IREG(prev) = IREG(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				prev->next = inst->next;
				inst = prev;
				continue;
			}

			// mov t12, 8
			// add t11, t12
			// =>
			//|mov t12, 8|
			// add t11, 8
			if (IK(inst) == IK_BINALU && (IM(inst) == M_Rr || IM(inst) == M_rr) && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && IREG(prev) == IREG2(inst) && pack_into_oper(get_imm64(prev), &IIMM(inst))) {
				inst->mode = IM(inst) == M_Rr ? M_Ri : M_ri;
				IREG2(inst) = R_NONE;
				if (--use_cnt[IREG(prev)] == 0) {
					--def_cnt[IREG(prev)];
					inst->prev = prev->prev;
					prev->prev->next = inst;
				}
				inst = inst;
				continue;
			}

			// mov t34, 3
			// mov [t14], t34
			// =>
			//|mov t34, 3|
			// mov [t14], 3
			if (IK(inst) == IK_MOV && IS(inst) != LEA && IM(inst) == M_Mr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && IREG(prev) == IREG(inst) && pack_into_oper(get_imm64(prev), &IIMM(inst))) {
				IM(inst) = M_Mi;
				if (--use_cnt[IREG(prev)] == 0) {
					--def_cnt[IREG(prev)];
					inst->prev = prev->prev;
					prev->prev->next = inst;
				}
				inst = inst;
				continue;
			}

			// lea t25, [rbp-24]
			// mov t26, [t25]
			// =>
			// mov t26, [rbp-24]
			if (IK(inst) == IK_MOV && IS(inst) != LEA && IM(inst) == M_CM && IINDEX(inst) == R_NONE && ISCALE(inst) == 0 && IDISP(inst) == 0 && IK(prev) == IK_MOV && IS(prev) == LEA && IM(prev) == M_CM && IBASE(inst) == IREG(prev) && use_cnt[IREG(prev)] == 1) {
				def_cnt[IREG(prev)]--;
				use_cnt[IREG(prev)]--;
				IS(prev) = IS(inst);
				IREG(prev) = IREG(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// lea t26, [rbp-24]
			// mov [t26], t25
			// =>
			// mov [rbp-24], t25
			if (IK(inst) == IK_MOV && IS(inst) != LEA && (IM(inst) == M_Mr || IM(inst) == M_Mi) && IINDEX(inst) == R_NONE && ISCALE(inst) == 0 && IDISP(inst) == 0 && IK(prev) == IK_MOV && IS(prev) == LEA && IM(prev) == M_CM && IBASE(inst) == IREG(prev) && use_cnt[IREG(prev)] == 1) {
				def_cnt[IREG(prev)]--;
				use_cnt[IREG(prev)]--;
				copy_memory(inst, prev);
				inst->prev = prev->prev;
				prev->prev->next = inst;
				continue;
			}

			// mov rcx, [global1]
			// add rax, rcx
			// =>
			// add rax, [global1]
			if (IK(inst) == IK_BINALU && IM(inst) == M_Rr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CM && IREG2(inst) == IREG(prev) && IREG(inst) != IREG2(inst) && use_cnt[IREG(prev)] == 1) {
				def_cnt[IREG(prev)]--;
				use_cnt[IREG(prev)]--;
				IM(prev) = M_RM;
				IK(prev) = IK(inst);
				IS(prev) = IS(inst);
				IREG(prev) = IREG(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// mov t13, [rbp-16]
			// cmp t13, 10
			// =>
			// cmp [rbp-16], 10
			if (IK(inst) == IK_BINALU && IM(inst) == M_ri && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CM) {
				IM(inst) = M_Mi;
				ISCALE(inst) = ISCALE(prev);
				IINDEX(inst) = IINDEX(prev);
				IBASE(inst) = IBASE(prev);
				IDISP(inst) = IDISP(prev);
				inst->prev = prev->prev;
				prev->prev->next = inst;
				inst = inst;
			}


			// mov rax, 1
			// add rax, 2
			// =>
			// mov rax, 3
			if (IK(inst) == IK_BINALU && IM(inst) == M_Ri && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && IREG(inst) == IREG(prev)) {
				def_cnt[IREG(inst)]--;
				use_cnt[IREG(inst)]--;
				u64 value = get_imm64(prev);
				u64 right = sext_imm32(IIMM(inst));
				// Let's just say that any kind of overflow is
				// undefined behaviour and not complicate this
				// piece of code.
				switch (IS(inst)) {
				case G1_ADD:  value += right; break;
				case G1_OR:   value |= right; break;
				case G1_AND:  value &= right; break;
				case G1_SUB:  value -= right; break;
				case G1_XOR:  value ^= right; break;
				case G1_IMUL: value *= right; break;
				default: goto skip;
				}
				set_imm64(prev, value);
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			skip:;
			}

			// mov rcx, 5
			// neg rcx ; W
			// =>
			// mov rcx, -5
			if (IK(inst) == IK_UNALU && IM(inst) == M_R && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && IREG(inst) == IREG(prev)) {
				def_cnt[IREG(inst)]--;
				use_cnt[IREG(inst)]--;
				u64 value = get_imm64(prev);
				switch (IS(inst)) {
				case G3_NEG: value = -value; break;
				case G3_NOT: value = ~value; break;
				default: UNREACHABLE();
				}
				set_imm64(prev, value);
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// mov t43, 4
			// imul t43, t19 ; W
			// =>
			// mov t43, t19
			// imul t43, 4
			if (IK(inst) == IK_BINALU && g1_is_commutative(IS(inst)) && IM(inst) == M_Rr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_CI && pack_into_oper(get_imm64(prev), &IIMM(inst))) {
				IM(prev) = M_Cr;
				IREG2(prev) = IREG2(inst);
				IM(inst) = M_Ri;
				continue;
			}

			if (IK(inst) == IK_BINALU && IS(inst) == G1_IMUL && IM(inst) == M_Ri) {
				Oper reg = IREG(inst);
				Oper imm = IIMM(inst);
				Oper base;
				Oper index;
				Oper scale;
				switch (imm) {
				case 2: base = reg; index = reg; scale = 0; break;
				case 3: base = reg; index = reg; scale = 1; break;
				case 5: base = reg; index = reg; scale = 2; break;
				case 9: base = reg; index = reg; scale = 3; break;
				default:
					if (!(imm & (imm - 1))) {
						IK(inst) = IK_SHIFT;
						IS(inst) = G2_SHL;
						scale = 0;
						Oper tmp = 1;
						while (tmp != imm) {
							tmp += tmp;
							scale++;
						}
						IIMM(inst) = scale;
						continue;
					} else {
						goto skip_const_mul;
					}
				}
				IK(inst) = IK_MOV;
				IS(inst) = LEA;
				IM(inst) = M_CM;
				IWF(inst) = false;
				IBASE(inst) = base;
				IINDEX(inst) = index;
				ISCALE(inst) = scale;
				IDISP(inst) = 0;
				continue;
			skip_const_mul:;
			}

			// lea t14, [rbp-16]
			// add t14, 8
			// =>
			// lea t14, [rbp-8]
			if (IK(inst) == IK_BINALU && IS(inst) == G1_ADD && IM(inst) == M_Ri && IK(prev) == IK_MOV && IS(prev) == LEA && IREG(prev) == IREG(inst)) {
				def_cnt[IREG(inst)]--;
				use_cnt[IREG(inst)]--;
				IDISP(prev) += IIMM(inst);
				prev->next = inst->next;
				inst->next->prev = prev;
				prev->next = inst->next;
				inst = prev;
				continue;
			}

			// mov [G], t27
			// mov t28, [G]
			// =>
			// mov [G], t27
			// mov t28, t27
			if (IK(inst) == IK_MOV && IS(inst) != LEA && IM(inst) == M_CM && IK(prev) == IK_MOV && IS(prev) != LEA && IM(prev) == M_Mr && is_memory_same(inst, prev)) {
				use_cnt[IREG(prev)]++;
				IS(inst) = MOV;
				IM(inst) = M_Cr;
				IREG2(inst) = IREG(prev);
				inst = inst;
				continue;
			}

			// lea rax, [rbp-8]
			// mov qword [rax], 3
			// =>
			// mov qword [rbp-8], 3
			if (IK(inst) == IK_MOV && IS(inst) != LEA && (IM(inst) == M_Mi || IM(inst) == M_Mr) && IK(prev) == IK_MOV && IS(prev) == LEA && IINDEX(prev) == R_NONE && ISCALE(prev) == 0 && IBASE(inst) == IREG(prev) && use_cnt[IREG(prev)] == 1) {
				IBASE(inst) = IBASE(prev);
				IDISP(inst) += IDISP(prev);
				inst->prev = prev->prev;
				prev->prev->next = inst;
				inst = inst;
				continue;
			}

			// add t17, 8
			// mov qword [t17], 5
			// =>
			// mov qword [t17+8], 5
			// NOTE: only valid if t17 is not used anywhere
			if (IK(inst) == IK_MOV && IS(inst) != LEA && (IM(inst) == M_Mi || IM(inst) == M_Mr) && IK(prev) == IK_BINALU && IS(prev) == G1_ADD && IM(prev) == M_Ri && IBASE(inst) == IREG(prev) && use_cnt[IBASE(inst)] == 2) {
				def_cnt[IBASE(inst)]--;
				use_cnt[IBASE(inst)]--;
				IDISP(inst) += IIMM(prev);
				inst->prev = prev->prev;
				prev->prev->next = inst;
				inst = inst;
				continue;
			}

			Inst *pprev = prev->prev;

			// CP
			// mov t35, 8
			// mov t14, t34
			// add t14, t35
			// =>
			// mov t14, t34
			// add t14, 8
			if (false && IK(inst) == IK_BINALU && IM(inst) == M_Rr && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_Cr && IK(pprev) == IK_MOV && IS(pprev) == MOV && IM(pprev) == M_CI && IREG(pprev) == IREG2(inst) && use_cnt[IREG2(inst)] == 1 && pack_into_oper(get_imm64(pprev), &IIMM(inst))) {
				def_cnt[IREG2(inst)]--;
				use_cnt[IREG2(inst)]--;
				IM(inst) = M_Ri;
				pprev->prev->next = prev;
				prev->prev = pprev->prev;
				inst = prev;
				continue;
			}

			// CP
			// mov t22, [H]
			// mov t23, ...
			// add t23, t22
			// =>
			// mov t23, ...
			// add t23, [H]
			if (IK(inst) == IK_BINALU && IM(inst) == M_Rr && IK(prev) == IK_MOV && IS(prev) == MOV && IREG(prev) == IREG(inst) && IK(pprev) == IK_MOV && IS(pprev) == MOV && IREG(pprev) == IREG2(inst) && use_cnt[IREG(pprev)] == 1 && def_cnt[IREG(inst)] == 2 && ((IM(pprev) == M_CI && pack_into_oper(get_imm64(pprev), &IIMM(pprev))) || IM(pprev) == M_Cr || IM(pprev) == M_CM)) {
				// We made sure that def_cnt of t23 is 2, which
				// is the two definitions we see in this
				// peephole. This should guarantee us, that t23
				// isn't in any way connected to definition of
				// of [H] (because then there would be an
				// additional definition).
				def_cnt[IREG(pprev)]--;
				use_cnt[IREG(pprev)]--;
				IK(pprev) = IK(inst);
				IS(pprev) = IS(inst);
				copy_flags(pprev, inst);
				switch (IM(pprev)) {
				case M_CI: IM(pprev) = M_Ri; break;
				case M_Cr: IM(pprev) = M_Rr; break;
				case M_CM: IM(pprev) = M_RM; break;
				default: UNREACHABLE();
				}
				IREG(pprev) = IREG(inst);
				pprev->prev->next = prev;
				prev->prev = pprev->prev;
				prev->next = pprev;
				pprev->prev = prev;
				pprev->next = inst->next;
				inst->next->prev = pprev;
				inst = pprev;
				continue;
			}

			// imul t50, t21, 8 ; W
			// lea t32, [t18+t50]
			// =>
			// lea t32, [t18+8*t50]
			if (mode_has_memory(IM(inst)) && !is_rip_relative(inst) && IINDEX(inst) != R_NONE && IK(prev) == IK_IMUL3 && IM(prev) == M_Cri && IREG(prev) == IINDEX(inst) && ISCALE(inst) == 0 && use_cnt[IREG(prev)] == 1) {
				switch (IIMM(prev)) {
				case 1: ISCALE(inst) = 0; break;
				case 8: ISCALE(inst) = 3; break;
				default: goto skip_imul3;
				}
				use_cnt[IREG(prev)]--;
				IINDEX(inst) = IREG2(prev);
				inst->prev = pprev;
				pprev->next = inst;
				inst = inst;
				continue;
			skip_imul3:;
			}

			Inst *ppprev = pprev->prev;

			// mov [rbp-16], t18
			// mov t21, [rbp-16]
			// add t21, t19 ; W
			// mov [rbp-16], t21
			// => (due to a previous optimization)
        		// mov [rbp-16], t18
        		// mov t21, t18
        		// add t21, t19 ; W
        		// mov [rbp-16], t21
			// =>
			// mov t21, t18
			// add t21, t19 ; W
			// mov [rbp-16], t21
			if (IK(inst) == IK_MOV && IS(inst) != LEA && IM(inst) == M_Mr && IK(prev) == IK_BINALU && IM(prev) == M_Rr && IREG(prev) == IREG(inst) && IK(pprev) == IK_MOV && IS(pprev) == MOV && IM(pprev) == M_Cr && IREG(pprev) == IREG(inst) && IK(ppprev) == IK_MOV && IS(ppprev) != LEA && IM(ppprev) == M_Mr && IREG(ppprev) == IREG2(pprev) && is_memory_same(inst, ppprev)) {
				ppprev->prev->next = pprev;
				pprev->prev = ppprev->prev;
				inst = pprev;
				continue;
			}

			// mov rax, [rbp-24]
			// add rax, 1
			// mov [rbp-24], rax
			// =>
			// add [rbp-24], 1
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Mr && ((IK(prev) == IK_BINALU && (IM(prev) == M_Ri || IM(prev) == M_Rr)) || (IK(prev) == IK_UNALU && IM(prev) == M_R) || (IK(prev) == IK_MOV && IS(prev) == LEA && IM(prev) == M_CM)) && IK(pprev) == IK_MOV && IS(pprev) == MOV && IM(pprev) == M_CM && IREG(prev) == IREG(pprev) && IREG(inst) == IREG(prev) && is_memory_same(pprev, inst)) {
				if (IK(prev) == IK_MOV) { // lea
					if (IREG(prev) != IBASE(prev) || IBASE(prev) == R_NONE || ISCALE(prev) != 0) {
						goto skip_mem_arith;
					}
					if (IDISP(prev) != 0 && IINDEX(prev) != R_NONE) {
						goto skip_mem_arith;
					}
					IK(prev) = IK_BINALU;
					IS(prev) = G1_ADD;
					if (IDISP(prev)) {
						IM(prev) = M_Ri;
						IIMM(prev) = IDISP(prev);
					} else if (IINDEX(prev)) {
						IM(prev) = M_Rr;
						IREG2(prev) = IINDEX(prev);
					}
				}
				switch (IM(prev)) {
				case M_Ri: IM(prev) = M_Mi; break;
				case M_Rr: IM(prev) = M_Mr; break;
				case M_R:  IM(prev) = M_M;  break;
				case M_CM: IM(prev) = M_Mi; break;
				default: UNREACHABLE();
				}
				copy_memory(prev, inst);
				prev->prev = pprev->prev;
				pprev->prev->next = prev;
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			skip_mem_arith:;
			}

			// imul t36, t44 ; W
			// test t36, t36 ; WO
			// =>
			// imul t36, t44 ; WO
			if (IK(inst) == IK_BINALU && (IS(inst) == G1_CMP || IS(inst) == G1_TEST) && IM(inst) == M_rr && IREG(inst) == IREG2(inst) && IWF(prev) && ((IK(prev) == IK_BINALU && (IM(prev) == M_Rr || IM(prev) == M_Ri || IM(prev) == M_RM)) || (IK(prev) == IK_UNALU && IM(prev) == M_R)) && IREG(prev) == IREG(inst)) {
				IOF(prev) = true;
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

			// setg t28
			// test t28, t28
			// jz .BB3
			// =>
			// jng .BB2
			if ((IK(inst) == IK_JCC || IK(inst) == IK_CMOVCC || IK(inst) == IK_SETCC) && IS(inst) == CC_Z && IK(prev) == IK_BINALU && IS(prev) == G1_TEST && IM(prev) == M_rr && IREG(prev) == IREG2(prev) && IK(pprev) == IK_SETCC && IREG(prev) == IREG(pprev)) {
				def_cnt[IREG(pprev)]--;
				use_cnt[IREG(pprev)] -= 3; // (2 for test, 1 for setcc)
				IS(inst) = cc_invert(IS(pprev));
				pprev->prev->next = inst;
				inst->prev = pprev->prev;
				// Go back before the flags are set and look for
				// optimization opportunities. For example for
				// the rest of the following pattern:
				// xor t28, t28 ; W
				// cmp t27, t41 ; WO
				// setg t28 ; R
				while (IRF(inst) || IOF(inst)) {
					inst = inst->prev;
				}
				continue;
			}

			// ... t32, CONST
			// ...
			// mov t14, t32
			// =>
			//|... t32, ...|
			// mov t14, CONST
			if (IK(inst) == IK_MOV && IS(inst) == MOV && IM(inst) == M_Cr && try_replace_by_immediate(mfunction, inst, IREG2(inst))) {
				IM(inst) = M_CI;
				set_imm64(inst, IIMM(inst));
				continue;
			}

			// ... t32, CONST
			// ...
			// add t14, t32
			// =>
			//|... t32, ...|
			// add t14, CONST
			if (IK(inst) == IK_BINALU && (IM(inst) == M_Rr || IM(inst) == M_rr) && try_replace_by_immediate(mfunction, inst, IREG2(inst))) {
				assert(IM(inst) == M_rr || inst->writes_flags);
				IM(inst) = IM(inst) == M_Rr ? M_Ri : M_ri;
				continue;
			}

			// ... t32, CONST
			// ...
			// mov [t14], t32
			// =>
			//|... t32, ...|
			// mov [t14], CONST
			if (IK(inst) == IK_MOV && IS(inst) != LEA && IM(inst) == M_Mr && try_replace_by_immediate(mfunction, inst, IREG2(inst))) {
				IM(inst) = M_Mi;
				continue;
			}

			// lea t19, [t18+3]
			// ...
			// lea t20, [t19+4]
			// =>
			// lea t20, [t18+7]
			if (IK(inst) == IK_MOV && IS(inst) == LEA && try_combine_memory(mfunction, inst)) {
				continue;
			}

			// mov t18, 3
			// ...
			// lea t19, [t18+7]
			// =>
			// mov t19, 10
			if (IK(inst) == IK_MOV && IS(inst) == LEA && try_replace_by_immediate(mfunction, inst, IBASE(inst))) {
				// At this point we know that this isn't
				// RIP-relative addressing, since IBASE was
				// found to have unique definition to immediate.
				IDISP(inst) += IIMM(inst);
				IIMM(inst) = 0;
				if (IINDEX(inst) != R_NONE) {
					IBASE(inst) = IINDEX(inst);
				} else {
					IS(inst) = MOV;
					IM(inst) = M_CI;
					set_imm64(inst, IDISP(inst));
				}
				continue;
			}

			// mov rax, 1
			// ...
			// lea rcx, [rcx+rax]
			// =>
			// lea rcx, [rcx+1]
			//
			// mov rax, 1
			// lea rax, [rdi+8*rax]
			// =>
			// lea rax, [rdi+8]
			if (IK(inst) == IK_MOV && IS(inst) == LEA && try_replace_by_immediate(mfunction, inst, IINDEX(inst))) {
				IINDEX(inst) = R_NONE;
				IDISP(inst) += IIMM(inst) << ISCALE(inst);
				IIMM(inst) = 0;
				continue;
			}

			// mov t25, 1
			// ...
			// push t25
			// =>
			// push 1
			if (IK(inst) == IK_PUSH && IM(inst) == M_r && try_replace_by_immediate(mfunction, inst, IREG(inst))) {
				IM(inst) = M_I;
				continue;
			}

			// lea t25, [rbp-24]
			// ...
			// mov t26, [t25]
			// =>
			// mov t26, [rbp-24]
			if (IK(inst) == IK_MOV && IS(inst) != LEA && IM(inst) == M_CM && try_combine_memory(mfunction, inst)) {
				continue;
			}

			// lea t25, [rbp-24]
			// ...
			// mov [t25], t24
			// =>
			// mov [rbp-24], t24
			if (IK(inst) == IK_MOV && IS(inst) != LEA && (IM(inst) == M_Mr || IM(inst) == M_Mi) && try_combine_memory(mfunction, inst)) {
				continue;
			}

			// lea t53, [rbp-32]
			// ...
			// add t35, [t53+8]
			// =>
			// add t35, [rbp-24]
			if (((IK(inst) == IK_BINALU && (IM(inst) == M_RM || IM(inst) == M_Mr)) || (IK(inst) == IK_UNALU && IM(inst) == M_M)) && try_combine_memory(mfunction, inst)) {
				continue;
			}

			// lea rax, [one]
			// call rax
			//=>
			// call one
			if (IK(inst) == IK_CALL && IM(inst) == M_rCALL && try_combine_label(mfunction, inst)) {
				IM(inst) = M_LCALL;
				continue;
			}

			// mov t26, t18
			// add t26, t34 ; W (no flags observed)
			// =>
			// lea t26, [t18+t34]
			if (IK(inst) == IK_BINALU && IS(inst) == G1_ADD && (IM(inst) == M_Rr || IM(inst) == M_Ri) && IK(prev) == IK_MOV && IS(prev) == MOV && IM(prev) == M_Cr && IREG(prev) == IREG(inst) && def_cnt[IREG(inst)] == 2) {
				use_cnt[IREG(inst)]--;
				def_cnt[IREG(inst)]--;
				defs[IREG(inst)] = prev;
				IS(prev) = LEA;
				IM(prev) = M_CM;
				IBASE(prev) = IREG2(prev);
				ISCALE(prev) = 0;
				if (IM(inst) == M_Rr) {
					IINDEX(prev) = IREG2(inst);
					IDISP(prev) = 0;
				} else {
					IINDEX(prev) = R_NONE;
					IDISP(prev) = IIMM(inst);
				}
				prev->next = inst->next;
				inst->next->prev = prev;
				inst = prev;
				continue;
			}

		next:
			inst = inst->next;
		}

		if (b == mfunction->mblock_cnt - 1) {
			break;
		}

		Oper next_block_index;
		MBlock *next = NULL;
		size_t i;
		for (i = b + 1; i < mfunction->mblock_cnt; i++) {
			next = mfunction->mblocks[i];
			if (next) {
				next_block_index = next->block->base.index;
				break;
			}
		}
		if (!next) {
			continue;
		}
		Inst *last = mblock->insts.prev;
		Inst *prev = last->prev;

		//     jge .BB3
		//     jmp .BB4
		// .BB3:
		// =>
		//     jl .BB4
		// .BB3:
		if (IK(last) == IK_JUMP && IK(prev) == IK_JCC && ILABEL(prev) == next->block->base.index) {
			IS(prev) = cc_invert(IS(prev));
			ILABEL(prev) = ILABEL(last);
			last->prev->next = last->next;
			last->next->prev = last->prev;
			block_use_cnt[next_block_index]--;
			last = last->prev;
		}

		//     jmp .BB5
		// .BB5:
		// =>
		// .BB5:
		if (IK(last) == IK_JUMP && ILABEL(last) == next->block->base.index) {
			last->prev->next = last->next;
			last->next->prev = last->prev;
			block_use_cnt[next_block_index]--;
			last = last->prev;
		}

		// 	jz .L4 ; R
		// 	mov rdx, rsi
		// .L4:
		// =>
		//      cmovnz rdx, rsi
		if (IK(last) == IK_MOV && IS(last) == MOV && IM(last) == M_Cr && IK(prev) == IK_JCC && ILABEL(prev) == next->block->base.index) {
			IK(last) = IK_CMOVCC;
			IS(last) = cc_invert(IS(prev));
			prev->prev->next = prev->next;
			prev->next->prev = prev->prev;
			block_use_cnt[next_block_index]--;
		}

		if (last_pass && block_use_cnt[next->block->base.index] == 0) {
			// If there is no reference to the next block (as
			// label), we can just merge it into the current one.
			mfunction->mblocks[i] = NULL;
			last->next = next->insts.next;
			next->insts.next->prev = last;
			next->insts.prev->next = &mblock->insts;
			mblock->insts.prev = next->insts.prev;
			inst = last;
			goto next;
		}
	}
}
