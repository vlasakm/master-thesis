project('tcg', 'c',
  version : '0.1',
  default_options : ['warning_level=3'])

exe = executable('tcg', 'tcg.c', 'arena.c',
  install : true)

test('basic', exe)
