#include "type.h"

Type TYPE_VOID = { .kind = TY_VOID };
Type TYPE_INT = { .kind = TY_INT };
Type TYPE_CHAR = { .kind = TY_CHAR };
PointerType TYPE_CHAR_PTR = { .base = { .kind = TY_POINTER, }, .child = &TYPE_CHAR };

size_t
type_size(Type *type)
{
	switch (type->kind) {
	case TY_VOID: return 0;
	case TY_CHAR: return 1;
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

size_t
type_alignment(Type *type)
{
	switch (type->kind) {
	case TY_VOID:
	case TY_CHAR:
	case TY_INT:
	case TY_POINTER:
		return type_size(type);
	case TY_FUNCTION:
		UNREACHABLE();
		break;
	case TY_STRUCT:
		return ((StructType *) type)->alignment;
	}
	UNREACHABLE();
}

bool
type_is_numeric(Type *type)
{
	switch (type->kind) {
	case TY_INT:
	case TY_CHAR:
		return true;
	default:
		return false;
	}
}

bool
type_is_integral(Type *type)
{
	switch (type->kind) {
	case TY_INT:
	case TY_CHAR:
		return true;
	default:
		return false;
	}
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
	if (!type_is_pointer(pointer_type)) {
		return &TYPE_VOID;
	}
	return ((PointerType *) pointer_type)->child;
}

Type *
type_function(Arena *arena, Type *ret_type, Parameter *parameters, size_t param_cnt, bool vararg)
{
	FunctionType *fun_type = arena_alloc(arena, sizeof(*fun_type));
	fun_type->base.kind = TY_FUNCTION;
	fun_type->ret_type = ret_type;
	fun_type->params = parameters;
	fun_type->param_cnt = param_cnt;
	fun_type->vararg = vararg;
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
type_function_return_type(Type *type)
{
	FunctionType *fun_type = type_as_function(type);
	return fun_type->ret_type;
}

Type *
type_struct(Arena *arena, Field *fields, size_t field_cnt)
{
	StructType *struct_type = arena_alloc(arena, sizeof(*struct_type));
	struct_type->base.kind = TY_STRUCT;
	struct_type->fields = fields;
	struct_type->field_cnt = field_cnt;

	size_t offset = 0;
	size_t max_alignment = 0;

	for (size_t i = 0; i < field_cnt; i++) {
		size_t field_align = type_alignment(fields[i].type);
		if (field_align > max_alignment) {
			max_alignment = field_align;
		}
		offset = align(offset, field_align);
		fields[i].offset = offset;
		offset += type_size(fields[i].type);
	}

	struct_type->size = offset;
	struct_type->alignment = max_alignment;

	return &struct_type->base;
}

Type *
type_struct_forward(Arena *arena)
{
	StructType *struct_type = arena_alloc(arena, sizeof(*struct_type));
	struct_type->base.kind = TY_STRUCT;
	struct_type->fields = NULL;
	struct_type->field_cnt = 0;
	return &struct_type->base;
}

Type *
type_struct_define(Type *type, Field *fields, size_t field_cnt)
{
	assert(type_is_struct(type));
	StructType *struct_type = (StructType *) type;
	struct_type->fields = fields;
	struct_type->field_cnt = field_cnt;

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
type_is_struct(Type *type)
{
	return type->kind == TY_STRUCT;
}

StructType *
type_as_struct(Type *type)
{
	assert(type_is_struct(type));
	return (StructType *) type;
}

bool
type_is_complete(Type *type)
{
	if (type->kind == TY_STRUCT) {
		return ((StructType *) type)->fields != NULL;
	}
	return true;
}

bool
types_compatible(Type *a, Type *b)
{
	if (a == b) {
		return true;
	} else if (type_is_pointer(a) && type_is_pointer(b)) {
		Type *x = pointer_child(a);
		Type *y = pointer_child(b);
		if (x->kind == TY_VOID || y->kind == TY_VOID) {
			return true;
		}
		return types_compatible(pointer_child(a), pointer_child(b));
	} else if (a->kind == TY_FUNCTION && b->kind == TY_FUNCTION) {
		FunctionType *x = (void *) a;
		FunctionType *y = (void *) b;
		if (!types_compatible(x->ret_type, y->ret_type)) {
			return false;
		}
		if (x->param_cnt != y->param_cnt) {
			return false;
		}
		for (size_t i = 0; i < x->param_cnt; i++) {
			if (!types_compatible(x->params[i].type, y->params[i].type)) {
				return false;
			}
		}
		return true;
	} else if (a->kind == TY_CHAR && b->kind == TY_INT) {
		// NOTE: This is here for stores to char. We don't need more,
		// but this should ideally be improved if more flexibility is
		// needed.
		return true;
	}
	return false;
}

void
print_type(FILE *f, Type *type)
{
	switch (type->kind) {
	case TY_VOID:
		fprintf(f, "void");
		break;
	case TY_CHAR:
		fprintf(f, "char");
		break;
	case TY_INT:
		fprintf(f, "int");
		break;
	case TY_POINTER:
		fprintf(f, "*");
		print_type(f, pointer_child(type));
		break;
	case TY_FUNCTION: {
		FunctionType *ft = type_as_function(type);
		fprintf(f, "(");
		for (size_t i = 0; i < ft->param_cnt; i++) {
			if (i != 0) {
				fprintf(f, ", ");
			}
			print_type(f, ft->params[i].type);
		}
		fprintf(f, ") -> ");
		print_type(f, ft->ret_type);
		break;
	}
	case TY_STRUCT: {
		fprintf(f, "{ ");
		StructType *st = (StructType *) type;
		for (size_t i = 0; i < st->field_cnt; i++) {
			if (i != 0) {
				fprintf(f, ", ");
			}
			print_type(f, st->fields[i].type);
		}
		fprintf(f, " }");
	}
	}
}
