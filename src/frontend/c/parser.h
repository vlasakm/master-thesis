#pragma once

#include "../../utils/utils.h"
#include "../../utils/arena.h"
#include "../../utils/str.h"
#include "../../middleend/ir.h"

Module *parse(Arena *arena, GArena *scratch, Str source, void (*error_callback)(void *user_data, const u8 *err_pos, const char *msg, va_list ap), void *user_data);
