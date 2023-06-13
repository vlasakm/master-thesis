#pragma once

#include <stddef.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdbool.h>
#include <stdarg.h>

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef int8_t  i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;

typedef u32 Oper;
#define OPER_MAX UINT32_MAX

#define container_of(member_ptr, type, member) \
	((type *) ((u8 *)(1 ? (member_ptr) : &((type *) 0)->member) - offsetof(type, member)))

#define GROW_ARRAY(array, new_count) \
	do { \
		(array) = realloc((array), (new_count) * sizeof((array)[0])); \
	} while(0)

#define ZERO_ARRAY(array, count) \
	do { \
		memset((array), 0, (count) * sizeof((array)[0])); \
	} while(0)

#define COPY_ARRAY(dest, src, count) \
	do { \
		memcpy((dest), (src), (count) * sizeof((1 ? (dest) : (src))[0])); \
	} while(0)

#define FREE_ARRAY(array, count) \
	do { \
		(void) (count); \
		free((array)); \
	} while(0)

#define ARRAY_LEN(arr) (sizeof((arr)) / sizeof((arr)[0]))

#ifdef __GNUC__
#define PRINTF_LIKE(n) __attribute__((__format__(__printf__, n, n + 1)))
#else
#define PRINTF_LIKE(n)
#endif



// ASAN integeration

#ifndef __has_feature
#define __has_feature(x) 0
#endif

#if defined(__SANITIZE_ADDRESS__) || __has_feature(address_sanitizer)
// https://github.com/google/sanitizers/wiki/AddressSanitizerManualPoisoning
void __asan_poison_memory_region(void const volatile *addr, size_t size);
void __asan_unpoison_memory_region(void const volatile *addr, size_t size);
#define ASAN_POISON_MEMORY_REGION(addr, size) \
	__asan_poison_memory_region((addr), (size))
#define ASAN_UNPOISON_MEMORY_REGION(addr, size) \
	__asan_unpoison_memory_region((addr), (size))
#else
#define ASAN_POISON_MEMORY_REGION(addr, size) \
	((void) (addr), (void) (size))
#define ASAN_UNPOISON_MEMORY_REGION(addr, size) \
	((void) (addr), (void) (size))
#endif



#define USE_VALGRIND


size_t align(size_t pos, size_t alignment);

#define UNREACHABLE() unreachable(__FILE__, __LINE__)
_Noreturn void unreachable(char *file, size_t line);

#define NOT_IMPLEMENTED(what) not_implemented((what), __FILE__, __LINE__)
_Noreturn void not_implemented(char *what, char *file, size_t line);
