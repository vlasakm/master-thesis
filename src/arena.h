// Arena allocation
// Michal Vlasák, FIT CTU, 2023

#pragma once

#include <stddef.h>
#include <stdalign.h>

// This header defines the API of two different Arena allocators - `Arena` and
// `Garena`. In general arena allocators all "bump allocate" their memory. I.e.
// they have a pointer to chunk of available memory from which they allocate
// sequentially -- when allocation is requested the returned memory is in the
// beginning of the first chunk: former free space pointer is returned and
// new one is formed by incrementing the former by the allocated size ("bumped").
// This is very efficient, because it wastes no space on metadata and the code
// for allocation is very fast.
// metadata
//
// The problem is that since individual allocations are not tracked, it is not
// possible to arbitrarily free allocations. But it is possible to deallocate
// _all_ the memory at once. This may seem too restricting, but in fact a lot of
// problem domains generate a lot of temporary objects and then get rid of all
// of them (e.g. a web server serving a single request).
//
// Another problem with arena allocation is what to do when they exhaust the
// free memory. There are a few options:
//
//  (1) Abort, since the memory is exhausted. Easy to do, makes sense e.g. for
//     microcontrollers with limited amount or memory, or programs with known
//     upper bound on memory consumption.
//
//  (2) Allocate a new chunk of memory to be used in addition to the old one (old
//     allocations are kept in old chunk(s). New allocations are  performed in a
//     new chunk). This has the advantage that all pointers to previously
//     allocated data are kept valid, the disadvantage is that the memory is no
//     longer contiguous.
//
//  (3) Allocate a new (bigger) chunk memory and _move_ the old allocations to
//      the new space. New allocations will be made in the rest of the new space.
//      This is dual to the previous approach, pointers to previous allocations
//      an be invalidated on every allocation, but the memory is kept contiguous
//      at all times.
//
//  (4) Extend the current chunk by allocating the memory immediately following
//      it. This is a refinement that has advantages of both of the previous
//      approaches, while having none of their limitations. The problem is
//      achieving it. On modern systems it can be due to the use of virtual
//      memory.
//
// There are many great resources on Arenas and associated topics, I can
// recommend at the very least:
//
//  - https://www.rfleury.com/p/untangling-lifetimes-the-arena-allocator
//  - https://www.gingerbill.org/article/2019/02/01/memory-allocation-strategies-001/
//  - https://en.wikipedia.org/wiki/Region-based_memory_management

// This particular arena implementation is the approach (2). No pointers are ever
// invalidated. The chunks are allocated with `malloc` and freed with `free`.
// The current allocation position (even across chunks) can be saved and
// restored, so not all allocated memory has to be deallocated at once. But the
// "stack" principle still has to be obeyed.
//
// The `Arena` struct is defined in this header but should be regarded as an
// implementation detail. `arena_` functions should be used for all manipulation
// with the arena.
typedef struct Arena Arena;

// `arena_init` and `arena_destroy` are called on to initialize and deinitialize
// an Arena.

void arena_init(Arena *arena);
void arena_destroy(Arena *arena);

// `arena_alloc` allocates a piece of memory of particular `size`.
void *arena_alloc(Arena *arena, size_t size);

// Save current allocation position and restore to a previous allocation
// position. Saves should be paired with respective restores (the stack
// principle).
size_t arena_save(Arena *arena);
void arena_restore(Arena *arena, size_t pos);



// The `GArena` ("growable arena") is an implementation of the approach (3).
// When free space is exhausted new bigger chunk is allocated and old objects
// are moved to it. Thus pointers returned by this allocator have to be used
// carefully.
//
// Despite this limitation, with careful use (see the below macros), growable
// arena essentially is a dynamic array and different parts of it can even
// store different types of objects. The utility functions below are public,
// but are only used in private parts of the parser and currently undocumented.
typedef struct GArena GArena;

void garena_init(GArena *arena);
void garena_destroy(GArena *arena);

void *garena_alloc(GArena *arena, size_t size, size_t alignment);

size_t garena_save(GArena *arena);
void *garena_restore(GArena *arena, size_t pos);


#define move_to_arena(arena, garena, start, type) \
	move_to_arena_((arena), (garena), (start), alignof(type))
void *move_to_arena_(Arena *arena, GArena *garena, size_t start, size_t alignment);


void *garena_mem(GArena *arena);
void *garena_from(GArena *arena, size_t start, size_t alignment);

#define garena_cnt(arena, type) \
	garena_cnt_from_((arena), 0, sizeof(type))

#define garena_cnt_from(arena, start, type) \
	garena_cnt_from_((arena), (start), sizeof(type))

size_t garena_cnt_from_(GArena *arena, size_t start, size_t elem_size);

#define garena_push(arena, type) \
	((type *)garena_alloc((arena), sizeof(type), alignof(type)))

#define garena_push_value(arena, type, value) \
	do { \
		type tmp_pushed_ = (value); \
		*garena_push((arena), type) = tmp_pushed_; \
	} while (0)



// PRIVATE IMPLEMENTATION DETAILS

typedef struct ArenaChunk ArenaChunk;
struct Arena {
	ArenaChunk *current;
	size_t prev_size_sum;
};

struct ArenaChunk {
	size_t size;
	size_t pos;
	ArenaChunk *prev;
	// Allocated chunk memory follows.
};

struct GArena {
	unsigned char *mem;
	size_t pos;
	size_t capacity;
};
