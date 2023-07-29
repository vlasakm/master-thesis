# vim: ft=meson sw=8 noet
project(
	'tcg',
	'c',
	version: '0.1',
	default_options: [
		'c_std=c11',
		'warning_level=2',
	]
)

cflags = [
	'-Wdouble-promotion',
	'-Wno-unused-parameter',
	'-Wno-unused-function',
	'-Wno-sign-compare',
	'-Wno-sign-conversion',
	'-Wno-self-assign',
]

if get_option('buildtype') == 'debug'
	cflags += [
		'-g3',
	]
endif

cc = meson.get_compiler('c')

add_project_arguments(
	cc.get_supported_arguments(cflags),
	language: 'c',
)

exe = executable('tcg',
	sources: files(
		'src/utils/arena.c',
		'src/utils/worklist.c',
		'src/utils/str.c',
		'src/utils/table.c',
		'src/utils/environment.c',
		'src/utils/bitset.c',
		'src/utils/utils.c',

		'src/frontend/c/parser.c',

		'src/middleend/type.c',
		'src/middleend/ir.c',

		'src/middleend/passes/value_numbering.c',
		'src/middleend/passes/merge_blocks.c',
		'src/middleend/passes/thread_jumps.c',
		'src/middleend/passes/split_critical_edges.c',
		'src/middleend/passes/single_exit.c',
		'src/middleend/passes/deconstruct_ssa.c',

		'src/backend/inst.c',
		'src/backend/regalloc.c',
		'src/backend/x86-64/x86-64.c',
		'src/backend/x86-64/lower.c',
		'src/backend/x86-64/peephole.c',

		'src/main.c',
	),
	include_directories: include_directories(
		'src',
	),
	install: true,
)

test('basic', exe)
