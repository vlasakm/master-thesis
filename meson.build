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
		'src/arena.c',
		'src/worklist.c',
		'src/str.c',
		'src/table.c',
		'src/environment.c',
		'src/utils.c',
		'src/type.c',
		'src/ir.c',
		'src/inst.c',
		'src/regalloc.c',
		'src/parser.c',
		'src/x86-64.c',
		'src/value_numbering.c',
		'src/tcg.c',
	),
	include_directories: include_directories(
		'src',
	),
	install: true,
)

test('basic', exe)
