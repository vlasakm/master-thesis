#pragma once

#include <stddef.h>
#include <stdbool.h>

#include "utils.h"
#include "str.h"
#include "arena.h"

typedef enum {
	TY_VOID,
	TY_INT,
	TY_POINTER,
	TY_FUNCTION,
	TY_STRUCT,
} TypeKind;

typedef struct {
	TypeKind kind;
} Type;

typedef struct {
	Type base;
	Type *child;
} PointerType;

typedef struct {
	Str name;
	Type *type;
} Parameter;

typedef struct {
	Type base;
	Type *ret_type;
	size_t param_cnt;
	Parameter *params;
} FunctionType;

typedef struct {
	Str name;
	Type *type;
	size_t offset;
} Field;

typedef struct {
	Type base;
	size_t size;
	size_t field_cnt;
	Field *fields;
} StructType;

extern Type TYPE_VOID;
extern Type TYPE_INT;

size_t type_size(Type *type);

Type * type_pointer(Arena *arena, Type *child);

bool type_is_pointer(Type *pointer_type);

Type *pointer_child(Type *pointer_type);

Type * type_function(Arena *arena, Type *ret_type, Parameter *parameters, size_t param_cnt);

bool type_is_function(Type *type);

bool type_is_function_compatible(Type *type);

FunctionType * type_as_function(Type *type);

size_t type_function_param_cnt(Type *type);

Type *type_struct(Arena *arena, Field *fields, size_t field_cnt);

bool types_compatible(Type *a, Type *b);

void print_type(FILE *f, Type *type);
