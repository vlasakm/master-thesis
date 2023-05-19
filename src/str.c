#include "str.h"

bool
str_eq(Str a, Str b)
{
	return a.len == b.len && memcmp(a.str, b.str, a.len) == 0;
}

int
str_cmp(Str a, Str b)
{
	int cmp = memcmp(a.str, b.str, a.len < b.len ? a.len : b.len);
	return cmp == 0 ? (a.len > b.len) - (b.len > a.len) : cmp;
}

void
print_str(FILE *f, Str s)
{
	fwrite(s.str, 1, s.len, f);
}

// FNV-1a hash
// http://www.isthe.com/chongo/tech/comp/fnv/
u64
str_hash(Str id)
{
	u64 h = UINT64_C(14695981039346656037);
	for (size_t i = 0; i < id.len; i++) {
		// beware of unwanted sign extension!
		h ^= id.str[i];
		h *= UINT64_C(1099511628211);
	}
	return h;
}
