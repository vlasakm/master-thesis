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
	'-Wno-unused-parameter',
	'-Wno-unused-function',
	'-Wno-sign-compare',
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
		'src/tcg.c',
	),
	include_directories: include_directories(
		'src',
	),
	install: true,
)

test('basic', exe)
