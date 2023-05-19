#include <stdio.h>

#include "utils.h"

_Noreturn void
unreachable(char *file, size_t line)
{
	fprintf(stderr, "ERROR: unreachable code reached at %s:%zu\n", file, line);
	exit(EXIT_FAILURE);
}
