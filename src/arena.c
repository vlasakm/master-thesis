// Arena allocation
// Michal Vlasák, FIT CTU, 2023

#include "arena.h"
#include "stdlib.h"
#include "stdint.h"
#include "string.h"
#include "stdarg.h"
#include "assert.h"
#include "stdio.h"

#include "utils.h"

static size_t
align(size_t pos, size_t alignment)
{
	return (pos + (alignment - 1)) & ~(alignment - 1);
}

static ArenaChunk sentinel = {0};

void
arena_init(Arena *arena)
{
	ArenaChunk *chunk = &sentinel;
	arena->current = chunk;
	arena->prev_size_sum = 0;
}

void *
arena_alloc(Arena *arena, size_t size)
{
	size_t pos = align(arena->current->pos, 8);
	size_t current_size = arena->current->size;
	if (pos + size > current_size) {
		arena->prev_size_sum += current_size;
		size_t new_size = size + (current_size ? current_size * 2 : 1024);
		ArenaChunk *new = malloc(new_size);
		new->size = new_size;
		new->prev = arena->current;
		arena->current = new;
		pos = align(sizeof(ArenaChunk), 8);
		ASAN_POISON_MEMORY_REGION(((u8 *) new) + pos, new_size - pos);
	}
	arena->current->pos = pos + size;
	ASAN_UNPOISON_MEMORY_REGION(((u8 *) arena->current) + pos, size);
	return ((u8 *) arena->current) + pos;
}

size_t
arena_save(Arena *arena)
{
	return arena->prev_size_sum + arena->current->pos;
}

void
arena_restore(Arena *arena, size_t pos)
{
	ArenaChunk *chunk = arena->current;
	while (pos < arena->prev_size_sum) {
		ArenaChunk *prev = chunk->prev;
		free(chunk);
		chunk = prev;
		arena->prev_size_sum -= chunk->size;
	}
	chunk->pos = pos - arena->prev_size_sum;
	ASAN_POISON_MEMORY_REGION(((u8 *) chunk) + chunk->pos, chunk->size - chunk->pos);
	arena->current = chunk;
}

void
arena_free(Arena *arena)
{
	arena_restore(arena, 0);
	if (arena->current != &sentinel) {
		free(arena->current);
		arena->current = &sentinel;
	}
}

u8 *
arena_vaprintf(Arena *arena, const char *fmt, va_list ap)
{
	va_list ap_orig;
	// save original va_list (vprintf changes it)
	va_copy(ap_orig, ap);

	size_t available = arena->current->size - arena->current->pos;
	void *mem = ((u8 *) arena->current) + arena->current->pos;
	ASAN_UNPOISON_MEMORY_REGION(mem, available);
	int len = vsnprintf(mem, available, fmt, ap);
	assert(len >= 0);
	len += 1; // terminating null
	if ((size_t) len <= available) {
		arena->current->pos += (size_t) len;
		ASAN_POISON_MEMORY_REGION(((u8 *) arena->current) + arena->current->pos, available - len);
	} else {
		mem = arena_alloc(arena, (size_t) len);
		vsnprintf(mem, (size_t) len, fmt, ap_orig);
	}
	va_end(ap_orig);
	return mem;
}




void
garena_init(GArena *arena)
{
	arena->mem = NULL;
	arena->pos = 0;
	arena->capacity = 0;
}

void
garena_free(GArena *arena)
{
	FREE_ARRAY(arena->mem, arena->capacity);
}

void *
garena_alloc(GArena *arena, size_t size, size_t alignment)
{
	size_t pos = align(arena->pos, alignment);
	if (pos + size > arena->capacity) {
		arena->capacity = arena->capacity ? arena->capacity * 2 : size * 8;
		GROW_ARRAY(arena->mem, arena->capacity);
		ASAN_POISON_MEMORY_REGION(arena->mem, arena->capacity);
	}
	arena->pos = pos + size;
	ASAN_UNPOISON_MEMORY_REGION(arena->mem, arena->pos);
	return &arena->mem[pos];
}

size_t
garena_save(GArena *arena)
{
	return arena->pos;
}

void *
garena_restore(GArena *arena, size_t pos)
{
	arena->pos = pos;
	ASAN_POISON_MEMORY_REGION(arena->mem + arena->pos, arena->capacity - arena->pos);
	return &arena->mem[pos];
}

void *
garena_mem(GArena *arena)
{
	return arena->mem;
}

size_t
garena_cnt_from_(GArena *arena, size_t start, size_t elem_size)
{
	return (arena->pos - start) / elem_size;
}

void *
garena_from(GArena *arena, size_t start, size_t alignment)
{
	size_t pos = align(start, alignment);
	return &arena->mem[pos];
}

void *
move_to_arena_(Arena *arena, GArena *garena, size_t start, size_t alignment)
{
	size_t size = garena->pos - start;
	if (size == 0) {
		return NULL;
	}
	void *old = garena_from(garena, start, alignment);
	void *new = arena_alloc(arena, size);
	memcpy(new, old, size);
	garena_restore(garena, start);
	return new;
}
