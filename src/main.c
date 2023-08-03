#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <setjmp.h>
#include <errno.h>
#include <unistd.h>

#include "utils/utils.h"
#include "utils/arena.h"
#include "utils/str.h"

#include "frontend/c/parser.h"

#include "middleend/ir.h"
#include "middleend/passes.h"

#include "backend/inst.h"
#include "backend/regalloc.h"
#include "backend/x86-64/x86-64.h"

typedef struct {
	bool assemble;
	bool link;
	char *output_file;
	char *input_file;
	bool number_values;
	bool peephole;
	bool linux_freestanding;
} Config;

bool linux_freestanding;

typedef struct Error Error;
struct Error {
	Error *next;
	char *kind;
	const u8 *pos;
	u8 *msg;
};

typedef struct {
	Arena arena;
	Str source;
	Error *error_head;
	Error *error_tail;
	jmp_buf loc;
} ErrorContext;

void
error_context_init(ErrorContext *ec)
{
	arena_init(&ec->arena);
	ec->source = (Str) {0};
	ec->error_head = NULL;
	ec->error_tail = NULL;
}

static void
verror(ErrorContext *ec, const u8 *pos, char *kind, bool fatal, const char *fmt, va_list ap)
{
	Error *error = arena_alloc(&ec->arena, sizeof(*error));
	error->msg = arena_vaprintf(&ec->arena, fmt, ap);
	error->pos = pos;
	error->kind = kind;
	error->next = NULL;
	if (ec->error_tail) {
		ec->error_tail->next = error;
	}
	ec->error_tail = error;
	if (!ec->error_head) {
		ec->error_head = error;
	}
	if (fatal) {
		longjmp(ec->loc, 1);
	}
}

static void
parser_verror(void *user_data, const u8 *err_pos, const char *msg, va_list ap)
{
	ErrorContext *ec = user_data;
	verror(ec, err_pos, "parse", true, msg, ap);
}

Module *
parse_source(ErrorContext *ec, Arena *arena, Str source)
{
	size_t arena_start = arena_save(arena);
	GArena scratch;
	garena_init(&scratch);
	ec->source = source;
	Module *module = parse(arena, &scratch, source, parser_verror, ec);
	garena_free(&scratch);

	if (!module) {
		arena_restore(arena, arena_start);
		longjmp(ec->loc, 1);
	}

	if (DUMP) {
		fprintf(stderr, "After parsing:\n");
		print_module(stderr, module);
		fprintf(stderr, "\n\n");
	}

	return module;
}

static void PRINTF_LIKE(2)
argument_error(ErrorContext *ec, const char *msg, ...)
{
	va_list ap;
	va_start(ap, msg);
	verror(ec, NULL, "argument", true, msg, ap);
	va_end(ap);
}

static Str
read_file(ErrorContext *ec, Arena *arena, const char *name)
{
	errno = 0;
	FILE *f = fopen(name, "rb");
	if (!f) {
		argument_error(ec, "Failed to open file '%s': %s", name, strerror(errno));
	}
	if (fseek(f, 0, SEEK_END) != 0) {
		argument_error(ec, "Failed seek in file '%s': %s", name, strerror(errno));
	}
	long tell = ftell(f);
	if (tell < 0) {
		argument_error(ec, "Failed to ftell a file '%s': %s", name, strerror(errno));
	}
	size_t fsize = (size_t) tell;
	assert(fseek(f, 0, SEEK_SET) == 0);
	u8 *buf = arena_alloc(arena, fsize);
	size_t read;
	if ((read = fread(buf, 1, fsize, f)) != fsize) {
		if (feof(f)) {
			fsize = read;
		} else {
			argument_error(ec, "Failed to read file '%s'", name);
		}
	}
	assert(fclose(f) == 0);
	return (Str) { .str = buf, .len = fsize };
}

void
print_runtime(FILE *f)
{
	fputs("\
	syscall:\n\
		mov rax, rdi\n\
		mov rdi, rsi\n\
		mov rsi, rdx\n\
		mov rdx, rcx\n\
		mov r10, r8\n\
		mov r8, r9\n\
		mov r9, [rsp+8]\n\
		syscall\n\
		ret\n\
	\n\
		global _start\n\
	_start:\n\
		xor rbp, rbp\n\
		mov rdi, [rsp]\n\
		lea rsi, [rsp+8]\n\
		call main\n\
		mov rdi, rax\n\
		mov rax, 60\n\
		syscall\n\
	", f);
}

void
print_nasm(FILE *f, Module *module)
{
	fprintf(f, "\tdefault rel\n\n");

	fprintf(f, "\tsection .data\n");
	for (size_t i = 0; i < module->global_cnt; i++) {
		Global *global = module->globals[i];
		if (global->init) {
			//printf("\talign 8\n");
			print_str(f, global->name);
			fprintf(f, ":\n");
			fprintf(f, "\tdq\t");
			print_value(f, global->init);
			fprintf(f, "\n");
		}
	}
	for (size_t i = 0; i < module->string_cnt; i++) {
		StringLiteral *string = module->strings[i];
		fprintf(f, "$str%zu:\n", i);
		fprintf(f, "\tdb\t`");
		print_str(f, string->str);
		fprintf(f, "`,0\n");
	}
	fprintf(f, "\n");

	fprintf(f, "\tsection .bss\n");
	for (size_t i = 0; i < module->global_cnt; i++) {
		Global *global = module->globals[i];
		Oper size = type_size(pointer_child(global->base.type));
		Oper count = size;
		if (!global->init) {
			//fprintf(f, "\talign 8\n");
			print_str(f, global->name);
			fprintf(f, ":\n");
			fprintf(f, "\tresb\t%"PRIu32"\n", count);
		}
	}
	fprintf(f, "\n");

	fprintf(f, "\tsection .text\n");
	fprintf(f, "\n");

	for (size_t i = 0; i < module->function_cnt; i++) {
		Function *function = module->functions[i];
		fprintf(f, "\n");
		if (function_is_fully_defined(function)) {
			fprintf(f, "\tglobal ");
			print_str(f, function->name);
			fprintf(f, "\n");
			print_mfunction(f, function->mfunction);
		} else {
			fprintf(f, "\textern ");
			print_str(f, function->name);
			fprintf(f, "\n");
		}
	}
	//*/
}

void
module_pipeline(Module *module, Arena *arena, Config *c)
{
	RegAllocState *ras = reg_alloc_state_create(arena);

	for (size_t i = 0; i < module->function_cnt; i++) {
		Function *function = module->functions[i];
		// Skip external functions
		if (!function_is_fully_defined(function)) {
			continue;
		}

		// Middle end
		index_values(function, R__MAX);
		merge_blocks(arena, function);
		thread_jumps(arena, function);
		if (c->number_values) {
			value_numbering(arena, function);
		}

		// Lowering
		split_critical_edges(arena, function);
		single_exit(arena, function);
		deconstruct_ssa(arena, function);
		translate_function(arena, &module->labels, function);

		// Back end
		MFunction *mfunction = function->mfunction;
		if (c->peephole) {
			peephole(mfunction, arena, false);
		}
		reg_alloc_function(ras, mfunction);
		mfunction_finalize_stack(mfunction);
		if (c->peephole) {
			peephole(mfunction, arena, true);
		} else {
			cleanup(mfunction);
		}
	}
	reg_alloc_state_free(ras);
}

void
module_free(Module *module)
{
	for (size_t i = 0; i < module->function_cnt; i++) {
		Function *function = module->functions[i];
		for (size_t b = 0; b < function->block_cap; b++) {
			Block *block = function->blocks[b];
			free(block->preds_);
		}
		free(function->blocks);
		FREE_ARRAY(function->post_order, function->block_cap);
		mfunction_free(function->mfunction);
	}
	garena_free(&module->labels);
}

int DUMP;

int
main(int argc, char **argv)
{
	Arena arena_;
	Arena *arena = &arena_;
	arena_init(arena);

	ErrorContext ec;
	error_context_init(&ec);

	if (setjmp(ec.loc) != 0) {
		goto end;
	}

	char *dump_env_var = getenv("DUMP");
	DUMP = dump_env_var && dump_env_var[0] != '\0';

	Config c_ = {
		.assemble = true,
		.link = true,
		.output_file = "a.out",
		.number_values = true,
		.peephole = true,
		.linux_freestanding = false,
	}, *c = &c_;
	for (int i = 1; i < argc; i++) {
		char *arg = argv[i];
		if (strcmp(arg, "-S") == 0) {
			c->assemble = false;
			c->link = false;
		} else if (strcmp(arg, "-c") == 0) {
			c->link = false;
		} else if (strcmp(arg, "-o") == 0) {
			c->output_file = argv[++i];
		} else if (strncmp(arg, "-f", 2) == 0) {
			arg += 2;
			bool toggle = true;
			if (strncmp(arg, "no-", 3) == 0) {
				arg += 3;
				toggle = false;
			}
			if (strcmp(arg, "number-values") == 0) {
				c->number_values = toggle;
			} else if (strcmp(arg, "peephole") == 0) {
				c->peephole = toggle;
			} else if (strcmp(arg, "linux-freestanding") == 0) {
				c->linux_freestanding = linux_freestanding = toggle;
			} else {
				argument_error(&ec, "Unknown flag -f%s%s", toggle ? "" : "no-", arg);
			}
		} else if (strncmp(arg, "-", 1) == 0) {
			argument_error(&ec, "Unknown flag %s", arg);
		} else {
			if (c->input_file) {
				argument_error(&ec, "Multiple files not supported");
			}
			c->input_file = arg;
		}
	}

	if (!c->input_file) {
		argument_error(&ec, "Expected input file name");
	}

	FILE *f_asm = NULL;
	FILE *f_obj = NULL;
	char asm_file[] = "/tmp/tinybackend.XXXXXX";
	char obj_file[] = "/tmp/tinybackend.XXXXXX";
	if (c->assemble) {
		int fd = mkstemp(asm_file);
		f_asm = fdopen(fd, "wb");
		if (c->link) {
			int fd = mkstemp(obj_file);
			f_obj = fdopen(fd, "wb");
		}
	} else {
		f_asm = fopen(c->output_file, "wb");
	}

	Str source = read_file(&ec, arena, c->input_file);
	Module *module = parse_source(&ec, arena, source);

	module_pipeline(module, arena, c);
	print_nasm(f_asm, module);
	if (c->linux_freestanding) {
		print_runtime(f_asm);
	}
	fflush(f_asm);
	module_free(module);

	if (c->assemble) {
		char *obj = c->output_file;
		if (c->link) {
			obj = obj_file;
		}
		char *nasm_cmd = (void *) arena_aprintf(arena, "nasm -f elf64 -o \"%s\" \"%s\"", obj, &asm_file[0]);
		system(nasm_cmd);
	}
	if (c->link) {
		char *extra_flags = "";
		if (c->linux_freestanding) {
			extra_flags = "-nolibc -nostdlib";
		}
		char *gcc_cmd = (void *) arena_aprintf(arena,  "gcc %s -o \"%s\" \"%s\"", extra_flags, c->output_file, obj_file);
		system(gcc_cmd);
	}

	if (f_asm) {
		fclose(f_asm);
		unlink(asm_file);
	}
	if (f_obj) {
		fclose(f_obj);
		unlink(obj_file);
	}

end:
	for (Error *err = ec.error_head; err; err = err->next) {
		if (!err->pos) {
			fprintf(stderr, "%s error: %s\n", err->kind, err->msg);
			continue;
		}
		const u8 *line_start = ec.source.str;
		size_t line = 0;
		const u8 *pos = ec.source.str;
		for (; pos < err->pos; pos++) {
			if (*pos == '\n') {
				line_start = pos + 1;
				line++;
			}
		}
		size_t col = pos - line_start;
		const u8 *source_end = ec.source.str + ec.source.len;
		const u8 *line_end = pos;
		for (; line_end < source_end && *line_end != '\n'; line_end++) {}
		fprintf(stderr, "[%zu:%zu]: %s error: %s\n", line + 1, col + 1, err->kind, err->msg);
		fprintf(stderr, "  %.*s\n", (int) (line_end - line_start), line_start);
		fprintf(stderr, "  %*s\n", (int) (pos - line_start + 1), "^");
	}

	arena_free(&ec.arena);
	arena_free(arena);
	return ec.error_head ? EXIT_FAILURE : EXIT_SUCCESS;
}
