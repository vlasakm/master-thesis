#include <stdio.h>
#include <setjmp.h>
#include <errno.h>

#include "utils.h"
#include "arena.h"
#include "str.h"
#include "x86-64.h"
#include "inst.h"
#include "parser.h"
#include "regalloc.h"

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
	verror(ec, err_pos, "parse", false, msg, ap);
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

	Function **functions = NULL;
	size_t function_cnt = 0;

	if (argc < 2) {
		goto end;
	}

	Str source = read_file(&ec, arena, argv[1]);
	Module *module = parse_source(&ec, arena, source);
	functions = module->functions;
	function_cnt = module->function_cnt;

	RegAllocState *ras = reg_alloc_state_create(arena);
	GArena labels = {0};

	fprintf(stderr, "Globals:\n");
	print_globals(stderr, module);
	fprintf(stderr, "\n");
	for (size_t i = 0; i < function_cnt; i++) {
		if (!function_is_fully_defined(functions[i])) {
			continue;
		}
		index_values(functions[i], R__MAX);
		print_function(stderr, functions[i]);
		merge_blocks(arena, functions[i]);
		print_function(stderr, functions[i]);
		thread_jumps(arena, functions[i]);
		print_function(stderr, functions[i]);
		value_numbering(arena, functions[i]);
		print_function(stderr, functions[i]);
		print_function(stderr, functions[i]);
		split_critical_edges(arena, functions[i]);
		print_function(stderr, functions[i]);
		single_exit(arena, functions[i]);
		print_function(stderr, functions[i]);
		///*
		deconstruct_ssa(arena, functions[i]);
		print_function(stderr, functions[i]);
		translate_function(arena, &labels, functions[i]);
		print_mfunction(stderr, functions[i]->mfunction);
		calculate_def_use_info(functions[i]->mfunction);
		peephole(functions[i]->mfunction, arena, false);
		print_mfunction(stderr, functions[i]->mfunction);
		reg_alloc_function(ras, functions[i]->mfunction);
		print_mfunction(stderr, functions[i]->mfunction);
		calculate_def_use_info(functions[i]->mfunction);
		mfunction_finalize_stack(functions[i]->mfunction);
		peephole(functions[i]->mfunction, arena, true);
		print_mfunction(stderr, functions[i]->mfunction);
		//*/
		//peephole(functions[i]->mfunc, arena);
	}

	///*
	reg_alloc_state_free(ras);

	printf("\tdefault rel\n\n");

	printf("\tsection .data\n");
	for (size_t i = 0; i < module->global_cnt; i++) {
		Global *global = module->globals[i];
		if (global->init) {
			//printf("\talign 8\n");
			print_str(stdout, global->name);
			printf(":\n");
			printf("\tdq\t");
			print_value(stdout, global->init);
			printf("\n");
		}
	}
	for (size_t i = 0; i < module->string_cnt; i++) {
		StringLiteral *string = module->strings[i];
		printf("$str%zu:\n", i);
		printf("\tdb\t`");
		print_str(stdout, string->str);
		printf("`,0\n");
	}
	printf("\n");

	printf("\tsection .bss\n");
	for (size_t i = 0; i < module->global_cnt; i++) {
		Global *global = module->globals[i];
		Oper size = type_size(pointer_child(global->base.type));
		Oper count = size / type_size(&TYPE_INT);
		if (!global->init) {
			//printf("\talign 8\n");
			print_str(stdout, global->name);
			printf(":\n");
			printf("\tresq\t%"PRIu32"\n", count);
		}
	}
	printf("\n");

	printf("\tsection .text\n");
	printf("\n");
	/*
	printf("syscall:\n\
	mov rax, rdi\n\
	mov rdi, rsi\n\
	mov rsi, rdx\n\
	mov rdx, rcx\n\
	mov r10, r8\n\
	mov r8, r9\n\
	mov r9, [rsp+8]\n\
	syscall\n\
	ret\n");
	printf("\n");
	printf("\tglobal _start\n");
	printf("_start:\n");
	printf("\txor rbp, rbp\n");
	printf("\tand rsp, -16\n");
	printf("\tcall main\n");
	printf("\tmov rdi, rax\n");
	printf("\tmov rax, 60\n");
	printf("\tsyscall\n");
	// TODO: argc, argv
	*/

	for (size_t i = 0; i < function_cnt; i++) {
		Function *function = functions[i];
		printf("\n");
		if (function_is_fully_defined(function)) {
			printf("\tglobal ");
			print_str(stdout, functions[i]->name);
			printf("\n");
			print_mfunction(stdout, functions[i]->mfunction);
		} else {
			printf("\textern ");
			print_value(stdout, &functions[i]->base);
			printf("\n");
		}
	}
	//*/

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

	for (size_t i = 0; i < function_cnt; i++) {
		Function *function = functions[i];
		for (size_t b = 0; b < function->block_cap; b++) {
			Block *block = function->blocks[b];
			free(block->preds_);
		}
		free(function->blocks);
		FREE_ARRAY(function->post_order, function->block_cap);
		mfunction_free(function->mfunction);
	}
	garena_free(&labels);

	arena_free(&ec.arena);
	arena_free(arena);
	return ec.error_head ? EXIT_FAILURE : EXIT_SUCCESS;
}
