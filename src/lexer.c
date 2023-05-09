typedef struct {
	const u8 *pos;
	const u8 *end;
} Lexer;

typedef enum {
	LS_START,
	LS_IDENTIFIER,
	LS_NUMBER,
	LS_STRING,
	LS_STRING_ESC,

	LS_PLUS,
	LS_MINUS,
	LS_LESS,
	LS_GREATER,
	LS_EQUAL,
	LS_BANG,
	LS_AMP,
	LS_BAR,
	LS_DOT,
	LS_DOT_DOT,
	LS_SLASH,
	LS_LINE_COMMENT,
	LS_BLOCK_COMMENT,
	LS_BLOCK_COMMENT_STAR,
} LexState;

typedef enum {
	ASSOC_LEFT,
	ASSOC_RIGHT,
} Associativity;

#define TOKENS(KW, PU, OT) \
	/* token            repr             nud + prec   led + prec + assoc */ \
	OT(NUMBER,          "a number",      literal,   0, lefterr,  99, LEFT)  \
	OT(IDENTIFIER,      "an identifier", ident,     0, lefterr,  99, LEFT)  \
	OT(STRING,          "a string",      literal,   0, lefterr,  99, LEFT)  \
	                                                                        \
	PU(PLUS,            "+",             unop,     14, binop,    12, LEFT)  \
	PU(PLUS_PLUS,       "++",            pre,      14, post,     15, LEFT)  \
	PU(MINUS,           "-",             unop,     14, binop,    12, LEFT)  \
	PU(MINUS_MINUS,     "--",            pre,      14, post,     15, LEFT)  \
	PU(RARROW,          "->",            nullerr,   0, member,   15, LEFT)  \
	PU(LESS,            "<",             nullerr,   0, cmp,      10, LEFT)  \
	PU(LESS_EQUAL,      "<=",            nullerr,   0, cmp,      10, LEFT)  \
	PU(LESS_LESS,       "<<",            nullerr,   0, binop,    11, LEFT)  \
	PU(GREATER,         ">",             nullerr,   0, cmp,      10, LEFT)  \
	PU(GREATER_EQUAL,   ">=",            nullerr,   0, cmp,      10, LEFT)  \
	PU(GREATER_GREATER, ">>",            nullerr,   0, binop,    11, LEFT)  \
	PU(EQUAL,           "=",             nullerr,   0, assign,    2, RIGHT) \
	PU(EQUAL_EQUAL,     "==",            nullerr,   0, cmp,       9, LEFT)  \
	PU(BANG,            "!",             lognot,   14, lefterr,  99, LEFT)  \
	PU(BANG_EQUAL,      "!=",            nullerr,   0, cmp,       9, LEFT)  \
	PU(AMP,             "&",             addr,     14, binop,     8, LEFT)  \
	PU(AMP_AMP,         "&&",            nullerr,   0, shortcirc, 5, LEFT)  \
	PU(BAR,             "|",             nullerr,   0, binop,     6, LEFT)  \
	PU(BAR_BAR,         "||",            nullerr,   0, shortcirc, 4, LEFT)  \
	PU(DOT,             ".",             nullerr,   0, member,   15, LEFT)  \
	PU(DOT_DOT_DOT,     "...",           nullerr,   0, lefterr,  99, LEFT)  \
	PU(SLASH,           "/",             nullerr,   0, binop,    13, LEFT)  \
	                                                                        \
	PU(LPAREN,          "(",             paren,     0, call,     15, LEFT)  \
	PU(RPAREN,          ")",             nullerr,   0, stop,      0, LEFT)  \
	PU(LBRACKET,        "[",             nullerr,   0, indexing, 15, LEFT)  \
	PU(RBRACKET,        "]",             nullerr,   0, stop,      0, LEFT)  \
	PU(LBRACE,          "{",             nullerr,   0, lefterr,  99, LEFT)  \
	PU(RBRACE,          "}",             nullerr,   0, lefterr,  99, LEFT)  \
	PU(COLON,           ":",             nullerr,   0, lefterr,  99, LEFT)  \
	PU(SEMICOLON,       ";",             empty,     0, stop,      0, LEFT)  \
	PU(COMMA,           ",",             nullerr,   0, seq,       1, LEFT)  \
	PU(TILDE,           "~",             unop,     14, lefterr,  99, LEFT)  \
	PU(HAT,             "^",             nullerr,   0, binop,     7, LEFT)  \
	PU(ASTERISK,        "*",             deref,    14, binop,    13, LEFT)  \
	/*PU(QUESTION_MARK,   "?",             nullerr,   0, ternop,    3, RIGHT)*/ \
	PU(PERCENT,         "%",             nullerr,   0, binop,    13, LEFT)  \
	                                                                        \
	KW(BREAK,           "break",         nullerr,   0, lefterr,  99, LEFT)  \
	KW(CASE,            "case",          nullerr,   0, lefterr,  99, LEFT)  \
	KW(CAST,            "cast",          cast,     14, lefterr,  99, LEFT)  \
	KW(CHAR,            "char",          nullerr,   0, lefterr,  99, LEFT)  \
	KW(CONTINUE,        "continue",      nullerr,   0, lefterr,  99, LEFT)  \
	KW(DEFAULT,         "default",       nullerr,   0, lefterr,  99, LEFT)  \
	KW(DO,              "do",            nullerr,   0, lefterr,  99, LEFT)  \
	KW(DOUBLE,          "double",        nullerr,   0, lefterr,  99, LEFT)  \
	KW(ELSE,            "else",          nullerr,   0, lefterr,  99, LEFT)  \
	KW(FOR,             "for",           nullerr,   0, lefterr,  99, LEFT)  \
	KW(IF,              "if",            nullerr,   0, lefterr,  99, LEFT)  \
	KW(INT,             "int",           nullerr,   0, lefterr,  99, LEFT)  \
	KW(RETURN,          "return",        nullerr,   0, lefterr,  99, LEFT)  \
	KW(STRUCT,          "struct",        nullerr,   0, lefterr,  99, LEFT)  \
	KW(SWITCH,          "switch",        nullerr,   0, lefterr,  99, LEFT)  \
	KW(TYPEDEF,         "typedef",       nullerr,   0, lefterr,  99, LEFT)  \
	KW(VOID,            "void",          nullerr,   0, lefterr,  99, LEFT)  \
	KW(WHILE,           "while",         nullerr,   0, lefterr,  99, LEFT)  \
	                                                                        \
	OT(EOF,             "end of input",  nullerr,   0, lefterr,   0, LEFT)  \
	OT(ERROR,           "lex error",     nullerr,   0, lefterr,  99, LEFT)

typedef enum {
	#define TOK_ENUM(tok, ...) TK_##tok,
	TOKENS(TOK_ENUM, TOK_ENUM, TOK_ENUM)
	#undef TOK_ENUM
} TokenKind;

static const char *tok_repr[] = {
	#define TOK_STR(tok, str, ...) "'"str"'",
	#define TOK_STR_OTHER(tok, str, ...) str,
	TOKENS(TOK_STR, TOK_STR, TOK_STR_OTHER)
	#undef TOK_STR
	#undef TOK_STR_OTHER
};

static struct {
	const char *str;
	TokenKind tok;
} keywords[] = {
	#define TOK_KW(tok, str, ...) { str, TK_##tok },
	#define TOK_OTHER(tok, str, ...)
	TOKENS(TOK_KW, TOK_OTHER, TOK_OTHER)
	#undef TOK_KW
	#undef TOK_OTHER
};

typedef struct {
	TokenKind kind;
	Str str;
} Token;

Lexer
lex_create(Str source)
{
	return (Lexer) {
		.pos = source.str,
		.end = source.str + source.len,
	};
}

#define ALPHA '_': case 'a': case 'b': case 'c': case 'd': case 'e': case 'f': case 'g': case 'h': case 'i': case 'j': case 'k': case 'l': case 'm': case 'n': case 'o': case 'p': case 'q': case 'r': case 's': case 't': case 'v': case 'u': case 'w': case 'x': case 'y': case 'z': case 'A': case 'B': case 'C': case 'D': case 'E': case 'F': case 'G': case 'H': case 'I': case 'J': case 'K': case 'L': case 'M': case 'N': case 'O': case 'P': case 'Q': case 'R': case 'S': case 'T': case 'V': case 'U': case 'W': case 'X': case 'Y': case 'Z'

#define DIGIT '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9'

static void
lex_next(Lexer *lexer, Token *token)
{
	LexState state = LS_START;
	TokenKind tok = TK_ERROR;
	int end_offset = 0;
	const u8 *start = lexer->pos;
	size_t length;
	while (lexer->pos != lexer->end) {
		u8 c = *lexer->pos;
		switch (state) {
		case LS_START: switch (c) {
			case ' ': case '\t': case '\n': case '\r': start += 1; break;
			case ALPHA: state = LS_IDENTIFIER; break;
			case DIGIT: state = LS_NUMBER; break;
			case '+': state = LS_PLUS; break;
			case '-': state = LS_MINUS; break;
			case '<': state = LS_LESS; break;
			case '>': state = LS_GREATER; break;
			case '=': state = LS_EQUAL; break;
			case '!': state = LS_BANG; break;
			case '&': state = LS_AMP; break;
			case '|': state = LS_BAR; break;
			case '.': state = LS_DOT; break;
			case '/': state = LS_SLASH; break;
			case '(': tok = TK_LPAREN; goto done;
			case ')': tok = TK_RPAREN; goto done;
			case '[': tok = TK_LBRACKET; goto done;
			case ']': tok = TK_RBRACKET; goto done;
			case '{': tok = TK_LBRACE; goto done;
			case '}': tok = TK_RBRACE; goto done;
			case ':': tok = TK_COLON; goto done;
			case ';': tok = TK_SEMICOLON; goto done;
			case ',': tok = TK_COMMA; goto done;
			case '~': tok = TK_TILDE; goto done;
			case '^': tok = TK_HAT; goto done;
			case '*': tok = TK_ASTERISK; goto done;
			case '%': tok = TK_PERCENT; goto done;
			default:  tok = TK_ERROR; goto done;
		} break;
		case LS_IDENTIFIER: switch (c) {
			case ALPHA: case DIGIT: break;
			default: tok = TK_IDENTIFIER; goto prev_done;
		} break;
		case LS_NUMBER: switch (c) {
			case DIGIT: break;
			default: tok = TK_NUMBER; goto prev_done;
		} break;
		case LS_STRING: switch (c) {
			case '"': tok = TK_STRING; end_offset = -1; goto done;
			case '\\': state = LS_STRING_ESC; break;
		} break;
		case LS_STRING_ESC: switch (c) {
			case 'n': case 't': case 'r': case '~': case '"': case '\\': state = LS_STRING; break;
			default: goto err;
		} break;
		case LS_PLUS: switch(c) {
			case '+': tok = TK_PLUS_PLUS; goto done;
			default: tok = TK_PLUS; goto prev_done;
		} break;
		case LS_MINUS: switch(c) {
			case '-': tok = TK_MINUS_MINUS; goto done;
			case '>': tok = TK_RARROW; goto done;
			default: tok = TK_MINUS; goto prev_done;
		} break;
		case LS_LESS: switch(c) {
			case '<': tok = TK_LESS_LESS; goto done;
			case '=': tok = TK_LESS_EQUAL; goto done;
			default: tok = TK_LESS; goto prev_done;
		} break;
		case LS_GREATER: switch(c) {
			case '>': tok = TK_GREATER_GREATER; goto done;
			case '=': tok = TK_GREATER_EQUAL; goto done;
			default: tok = TK_GREATER; goto prev_done;
		} break;
		case LS_EQUAL: switch (c) {
			case '=': tok = TK_EQUAL_EQUAL; goto done;
			default: tok = TK_EQUAL; goto prev_done;
		} break;
		case LS_BANG: switch (c) {
			case '=': tok = TK_BANG_EQUAL; goto done;
			default: tok = TK_BANG; goto prev_done;
		} break;
		case LS_AMP: switch (c) {
			case '&': tok = TK_AMP_AMP; goto done;
			default: tok = TK_AMP; goto prev_done;
		} break;
		case LS_BAR: switch (c) {
			case '|': tok = TK_BAR_BAR; goto done;
			default: tok = TK_BAR; goto prev_done;
		} break;
		case LS_DOT: switch (c) {
			case '.': state = LS_DOT_DOT; break;
			default: tok = TK_DOT; goto prev_done;
		} break;
		case LS_DOT_DOT: switch (c) {
			case '.': tok = TK_DOT_DOT_DOT; goto done;
			default: goto err;
		} break;
		case LS_SLASH: switch (c) {
			case '/': state = LS_LINE_COMMENT; start += 2; break;
			case '*': state = LS_BLOCK_COMMENT; start += 2; break;
			default: tok = TK_SLASH; goto prev_done;
		} break;
		case LS_LINE_COMMENT: switch (c) {
			// Also works with CR LF
			case '\n': state = LS_START; start = lexer->pos + 1; break;
		} break;
		case LS_BLOCK_COMMENT: switch (c) {
			case '*': state = LS_BLOCK_COMMENT_STAR; break;
		} break;
		case LS_BLOCK_COMMENT_STAR: switch (c) {
			case '*': break;
			case '/': state = LS_START; start = lexer->pos + 1; break;
			default: state = LS_BLOCK_COMMENT; break;
		} break;
		}

		lexer->pos += 1;
	}

	switch (state) {
		case LS_START: tok = TK_EOF; goto prev_done;
		case LS_IDENTIFIER: tok = TK_IDENTIFIER; goto prev_done;
		case LS_NUMBER: tok = TK_NUMBER; goto prev_done;
		case LS_STRING: goto err;
		case LS_STRING_ESC: goto err;
		case LS_PLUS: tok = TK_PLUS; goto prev_done;
		case LS_MINUS: tok = TK_MINUS; goto prev_done;
		case LS_LESS: tok = TK_LESS; goto prev_done;
		case LS_GREATER: tok = TK_GREATER; goto prev_done;
		case LS_EQUAL: tok = TK_EQUAL; goto prev_done;
		case LS_BANG: tok = TK_BANG; goto prev_done;
		case LS_AMP: tok = TK_AMP; goto prev_done;
		case LS_BAR: tok = TK_BAR; goto prev_done;
		case LS_DOT: tok = TK_DOT; goto prev_done;
		case LS_DOT_DOT: goto err;
		case LS_SLASH: tok = TK_SLASH; goto prev_done;
		case LS_LINE_COMMENT: tok = TK_EOF; goto prev_done;
		case LS_BLOCK_COMMENT: goto err;
		case LS_BLOCK_COMMENT_STAR: goto err;
	}

done:
	lexer->pos += 1;
prev_done:
err:
	length = lexer->pos - start + end_offset;
	if (tok == TK_IDENTIFIER) {
		for (size_t i = 0; i < sizeof(keywords) / sizeof(keywords[0]); i++) {
			if (strlen(keywords[i].str) == length && memcmp((const char*) start, keywords[i].str, length) == 0) {
				tok = keywords[i].tok;
				break;
			}
		}
	}
	token->kind = tok;
	token->str.str = start;
	token->str.len = length;
}
