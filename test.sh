#!/bin/bash

[[ -d /tmp/build ]] || meson setup /tmp/build -D b_sanitize=address,undefined
meson compile -C /tmp/build

mkdir -p out obj

for f in tests/*; do
	f=${f##*/};
	f=${f%%.*};
	echo "$f";
	/tmp/build/tcg -S -o out/"$f.asm" tests/"$f.tc"
done

diff -ur --color=always ref/ out/
