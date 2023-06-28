#!/bin/bash

mkdir -p out
cd out

for f in ../*.c; do
	f=${f##*/};
	f=${f%%.*};
	fin="../$f";
	gcc -o "$f-gcc-O0" -O0 "$fin.c"
	gcc -o "$f-gcc-O1" -O1 "$fin.c"
	gcc -o "$f-gcc-O2" -O2 "$fin.c"

	tcg -o "$f-tcg-pv" -fpeephole    -fnumber-values    "$fin.tc" 2>/dev/null
	tcg -o "$f-tcg-v"  -fno-peephole -fnumber-values    "$fin.tc" 2>/dev/null
	tcg -o "$f-tcg-p"  -fpeephole    -fno-number-values "$fin.tc" 2>/dev/null
	tcg -o "$f-tcg-"   -fno-peephole -fno-number-values "$fin.tc" 2>/dev/null

	hyperfine --warmup 4 --runs 20 "./$f-gcc-O0" "./$f-gcc-O1" "./$f-gcc-O2" "./$f-tcg-pv" "./$f-tcg-v" "./$f-tcg-p" "./$f-tcg-" --export-csv "$f.csv"
done
