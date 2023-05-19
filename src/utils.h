#pragma once

#include <stddef.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdbool.h>

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef int8_t  i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;

typedef i32 Oper;
#define OPER_MAX INT32_MAX

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

#define USE_VALGRIND

#define UNREACHABLE() unreachable(__FILE__, __LINE__)
_Noreturn void unreachable(char *file, size_t line);
