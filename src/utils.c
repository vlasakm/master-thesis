#include <stdio.h>

#include "utils.h"

_Noreturn void
unreachable(char *file, size_t line)
{
	fprintf(stderr, "ERROR: unreachable code reached at %s:%zu\n", file, line);
	exit(EXIT_FAILURE);
}

_Noreturn void
not_implemented(char *what, char *file, size_t line)
{
	fprintf(stderr, "NOT IMPLEMENTED: %s at %s:%zu\n", what, file, line);
	exit(EXIT_FAILURE);
}
