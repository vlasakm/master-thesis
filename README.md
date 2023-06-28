# TinyC x86-64 Backend

`tcg`, an x86-64 backend for
[TinyC](https://gitlab.fit.cvut.cz/NI-GEN/ni-gen-23), written in C11. The
canonical repository is https://github.com/vlasakm/master-thesis.

## Building

`tcg` uses the [Meson](https://mesonbuild.com/) build system. A release build
can be compiled with:

```
meson setup builddir --buildtype release
meson compile -C builddir
```

An `tcg` binary is then built at `builddir/fml`. All build artifacts are
contained in the `builddir` directory (you are free to choose any other name)
and can be safely deleted.

Or more simply:

```
gcc -O2 -o tcg src/one.c
```

Customize compile flags as you like.

## Installation

You can just copy the built file. It's all there is anyway.

Or you can use `meson install` at your own risk.

Additionally be sure to install:

## Dependencies

Build only dependencies:

 - `meson` (+ `python`)
 - `ninja`

Run time dependencies:

 - [`nasm`](https://www.nasm.us/), for assembling support (i.e. not `-S`)
 - [`gcc`](https://gcc.gnu.org/), for linking support (i.e. not `-S`, nor `-c`)

## Usage

The compiler currently accepts TinyC source files as input, and produces either
assembly files (without dependencies), object files (assembled with `nasm`), or
executables (assembled with `nasm` and linked with `gcc`). Additional flags are
available regardless of the output format.

### Output formats

- `-S`, assembly
- `-c`, object file
- (default), executable

### Flags

The `-f` flags can be turned either on or off. Only the non default option is shown below.

- `-o <filename>`, sets output file name. Default: `a.out`
- `-fno-number-values`, disable SSA construction by value numbering.
- `-fno-peephole`, disable peephole optimization (both before and after register allocation).
- `-flinux-freestanding`, provide `syscall` function and don't link with the C library.
