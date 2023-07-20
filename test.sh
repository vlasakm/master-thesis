#!/bin/bash
# Use:
#
# Run all tests (either works):
#
#     ./test.sh
#     ./test.sh all
#
# Run all test cases through the "asm" test:
#
#     ./test.sh asm
#
# Test with the "asm" test type the tests/const.tc and testse/char.tc files.
# The test compares the asm output of the compiler with the reference (in
# the "ref" directory):
#
#     ./test.sh asm const.tc char.tc
#
# Test with the "output" test type the tests/indexing.tc file.
# The test compares the output of the execution of the compiled program
# with the reference output embedded in the source ".tc" file:
#
#     ./test.sh asm indexing
#
# The script is inspired by https://github.com/kondziu/FMLtest

shopt -s nullglob

# How wide the test name is allowed to be (just aesthetics)
TEXT_WIDTH=74

# Locate this script on disk to use as root.
ROOT_DIR=$(dirname $(readlink -f "$0"))

# Where we build the tcg binary
BUILD_DIR="/tmp/build-tcg"

# Where the tests are
INPUT_DIR="$ROOT_DIR/tests"

# Where the reference assembly outputs are
REF_DIR="$ROOT_DIR/ref"

# Where all output is saved to
OUTPUT_DIR="$ROOT_DIR/out"

# Exit code for this program (succesfull for now)
EXIT_CODE=0

tcg="$BUILD_DIR/tcg"

die() {
	echo "$0: error: $@" >&2
	exit 1
}

print_justified() {
	message="$@"
	printf "%-${TEXT_WIDTH}s" "$message"
}

print_green() {
	echo -e "\e[32m$@\e[0m"
}
print_red() {
	echo -e "\e[31m$@\e[0m"
}
print_yellow() {
	echo -e "\e[33m$@\e[0m"
}

require_tcg() {
	[[ -d "$BUILD_DIR" ]] || meson setup "$BUILD_DIR" -D b_sanitize=address,undefined
	meson compile -C "$BUILD_DIR"
}

asm() {
	expected="$REF_DIR/$test.asm"
	output="$out.asm"
	"$tcg" -S -o "$output" "$input"
}

output() {
	binary="$out"
	output="$out.out"
	expected="$out.expected"
	# Extract the relevant comments from the source file to get expected output
	sed -n 's/[^/]*\/\/ > \(.*\)/\1/p' "$input" > "$expected"

	"$tcg" -o "$binary" "$input" && \
	"$binary" > "$output"
}

run_test() {
	type=$1 # e.g. "asm" or "output"
	test=${2%%.*} # e.g. "arrays" or "arrays.tc" or "arrays.tc.test"

	mkdir -p "$OUTPUT_DIR/$type" || die "failed to create output dir"

	in="$INPUT_DIR/$test"
	out="$OUTPUT_DIR/$type/$test"
	input="$in.tc"
	error_output="$out.err"
	delta="$out.diff"

	[[ -r "$input" ]] || die "Can't read '$input'"

	# Report in
	print_justified "Executing $type test: \"$test\"... "

        # Run the test capturing stdout (to "$output") and stderr
	"$type" 2>"$error_output"
	exit_code=$?

	# Compare output and expected output
	diff -u "$expected" "$output" > "$delta"
	diff_status=$?

	# Compare results, print delta into a file, and report
	if (( $exit_code == 0 && $diff_status == 0 )); then
		if [[ -s "$error_output" ]]; then
			print_yellow "stderr"
			print_yellow "[stderr: \"$error_output\"]"
		else
			print_green "passed"
		fi
	else
		print_red "failed"
		(( $exit_code != 0 )) && print_red "[exit code: $exit_code]"
		[[ -s "$delta" ]] && print_red "[diff: \"$delta\"]"
		[[ -s "$error_output" ]] && print_yellow "[stderr: \"$error_output\"]"
		EXIT_CODE=1
	fi
}

run_tests() {
	type="$1"
	for test in "${tests[@]}"; do
		run_test "$type" "$test"
	done
}

# Read tests in directory with glob into array
tests=("$INPUT_DIR/"*".tc")
tests=("${tests[@]%.tc}") # remove extension
tests=("${tests[@]##*/}") # remove leading path

if [[ $# -eq 0 ]]; then
	test_type="all"
else
	test_type=$1
	shift
fi


case "$test_type" in
all)
	require_tcg

	for suite in asm output; do
		run_tests "$suite"
	done
	;;
*)
	require_tcg
	if [[ $# -gt 0 ]]; then
		tests=("$@")
	fi
	run_tests "$test_type"
	;;
esac

exit "$EXIT_CODE"
