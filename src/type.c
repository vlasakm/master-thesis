#include "type.h"

Type TYPE_VOID = { .kind = TY_VOID };
Type TYPE_INT = { .kind = TY_INT };

size_t
type_size(Type *type)
{
	switch (type->kind) {
	case TY_VOID: return 0;
	case TY_INT:  return 8;
	case TY_POINTER:
		return 8;
	case TY_FUNCTION:
		UNREACHABLE();
		break;
	case TY_STRUCT:
		return ((StructType *) type)->size;
	}
	UNREACHABLE();
}

Type *
type_pointer(Arena *arena, Type *child)
{
	PointerType *ptr_type = arena_alloc(arena, sizeof(*ptr_type));
	ptr_type->base.kind = TY_POINTER;
	ptr_type->child = child;
	return &ptr_type->base;
}

bool
type_is_pointer(Type *pointer_type)
{
	return pointer_type->kind == TY_POINTER;
}

Type *
pointer_child(Type *pointer_type)
{
	assert(type_is_pointer(pointer_type));
	return ((PointerType *) pointer_type)->child;
}

Type *
type_function(Arena *arena, Type *ret_type, Parameter *parameters, size_t param_cnt)
{
	FunctionType *fun_type = arena_alloc(arena, sizeof(*fun_type));
	fun_type->base.kind = TY_FUNCTION;
	fun_type->ret_type = ret_type;
	fun_type->params = parameters;
	fun_type->param_cnt = param_cnt;
	return &fun_type->base;
}

bool
type_is_function(Type *type)
{
	return type->kind == TY_FUNCTION;
}

bool
type_is_function_compatible(Type *type)
{
	if (type_is_function(type)) {
		return true;
	}
	if (type_is_pointer(type) && type_is_function(pointer_child(type))) {
		return true;
	}
	return false;
}

FunctionType *
type_as_function(Type *type)
{
	if (type_is_function(type)) {
		return (FunctionType *) type;
	}
	if (type_is_pointer(type)) {
		type = pointer_child(type);
		assert(type_is_function(type));
		return (FunctionType *) type;
	}
	assert(false);
}

size_t
type_function_param_cnt(Type *type)
{
	FunctionType *fun_type = type_as_function(type);
	return fun_type->param_cnt;
}

Type *
type_struct(Arena *arena, Field *fields, size_t field_cnt)
{
	StructType *struct_type = arena_alloc(arena, sizeof(*struct_type));
	struct_type->base.kind = TY_STRUCT;
	struct_type->fields = fields;
	struct_type->field_cnt = field_cnt;

	// TODO: alignment
	size_t offset = 0;

	for (size_t i = 0; i < field_cnt; i++) {
		// TODO: align
		fields[i].offset = offset;
		offset += type_size(fields[i].type);
	}

	struct_type->size = offset;

	return &struct_type->base;
}

bool
types_compatible(Type *a, Type *b)
{
	if (a == b) {
		return true;
	} else if (type_is_pointer(a) && type_is_pointer(b)) {
		return types_compatible(pointer_child(a), pointer_child(b));
	}
	return false;
}