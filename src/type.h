#pragma once

#include <stddef.h>
#include <stdbool.h>

#include "utils.h"
#include "str.h"
#include "arena.h"

typedef enum {
	TY_VOID,
	TY_CHAR,
	TY_INT,
	TY_POINTER,
	TY_ARRAY,
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
	Type base;
	Type *child;
	size_t size;
} ArrayType;

typedef struct {
	Str name;
	Type *type;
} Parameter;

typedef struct {
	Type base;
	bool vararg;
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
	bool complete;
	size_t size;
	size_t alignment;
	size_t field_cnt;
	Field *fields;
} StructType;

extern Type TYPE_VOID;
extern Type TYPE_INT;
extern Type TYPE_CHAR;
extern PointerType TYPE_CHAR_PTR;
extern PointerType TYPE_VOID_PTR;

size_t type_size(Type *type);
size_t type_alignment(Type *type);

bool type_is_numeric(Type *type);

bool type_is_integral(Type *type);

Type *type_pointer(Arena *arena, Type *child);

bool type_is_pointer(Type *pointer_type);

Type *pointer_child(Type *pointer_type);

Type *type_array(Arena *arena, Type *child, size_t size);

bool type_is_array(Type *type);

Type *type_function(Arena *arena, Type *ret_type, Parameter *parameters, size_t param_cnt, bool vararg);

bool type_is_function(Type *type);

bool type_is_function_compatible(Type *type);

FunctionType *type_as_function(Type *type);

size_t type_function_param_cnt(Type *type);

Type *type_function_return_type(Type *type);

Type *type_struct(Arena *arena, Field *fields, size_t field_cnt);
Type *type_struct_forward(Arena *arena);
Type *type_struct_define(Type *struct_type, Field *fields, size_t field_cnt);

bool type_is_struct(Type *type);
StructType *type_as_struct(Type *type);

bool type_is_complete(Type *type);

bool types_compatible(Type *a, Type *b);

void print_type(FILE *f, Type *type);
