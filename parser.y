%{
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "loc.h"
#include "ast.h"     /* your AST header */
#include "info.h"    /* error-message and printing macros */

/* ----------------- basic global state from template ----------------- */
#define MAX_LINE_LENG 256
int line_no = 1, col_no = 1;
int opt_list = 0, opt_token = 0;

/* track current function for return / redefinition diagnostics */
static const char *current_function_name = NULL;
static int        current_function_is_redef = 0;
static LocType    current_function_loc;

char buffer[MAX_LINE_LENG];
extern FILE *yyin;        /* from lex */
extern char *yytext;      /* from lex */
extern int yyleng;

int  yylex(void);
static void yyerror(const char *msg);

/* Expose root */
Node g_root = NULL;

/* ----------------- symbol table and type helpers ----------------- */

typedef enum {
    OBJ_VAR,
    OBJ_FUNC,
    OBJ_PROC,
    OBJ_PARAM,
    OBJ_PROG
} ObjKind;

typedef struct ParamListTag {
    Type *type;
    struct ParamListTag *next;
} ParamList;

typedef struct SymTag {
    char    *name;
    int      scope;      /* 0 = global, 1,2,... nested */
    ObjKind  kind;
    Type    *type;       /* variable type or function return type; NULL for void */
    ParamList *params;   /* function/proc formal parameter types */
    int      has_return; /* for functions: did we see a return? */
    struct SymTag *next;
} Sym;

static Sym *symtab = NULL;   /* head of global list, new symbols at head */
static int  cur_scope = -1;  /* will become 0 after first create_scope() */

/* forward helpers */
static Sym *insert_symbol(const char *name, ObjKind k, Type *ty,
                          ParamList *params, LocType loc);
static Sym *lookup_symbol(const char *name);
static Sym *lookup_symbol_in_scope(const char *name, int scope);
static void open_scope(void);
static void close_scope_and_dump(void);
static void dump_symtab(void);
static void type_to_string(Type *t, char *buf, size_t n);
static void sym_type_to_string(Sym *s, char *buf, size_t n);
static ParamList *paramlist_append(ParamList *head, Type *ty);
static void mark_function_return(const char *name, LocType loc);

/* --- per-identifier source location tracking (by pointer identity) --- */
typedef struct NameLocTag {
    const char *p;      /* points to the exact strdup'd string stored in list */
    LocType     loc;    /* token location for that occurrence */
    struct NameLocTag *next;
} NameLoc;

static NameLoc *g_name_locs = NULL;

static void remember_name_loc(const char *p, LocType loc) {
    NameLoc *n = (NameLoc*)malloc(sizeof(NameLoc));
    n->p = p; n->loc = loc; n->next = g_name_locs; g_name_locs = n;
}

static LocType find_name_loc_or(const char *p, LocType fallback) {
    for (NameLoc *n = g_name_locs; n; n = n->next)
        if (n->p == p) return n->loc;   /* pointer identity matters */
    return fallback;
}

/* --- minimal cons for arbitrary pointers (no extra strdup) --- */
static Cons consPtr(void *ptr, Cons tail) {
    Cons c = (Cons)malloc(sizeof(ConsStr));
    c->car = ptr; c->cdr = tail; return c;
}
static Cons appendPtr(Cons list, void *ptr) {
    Cons n = consPtr(ptr, NULL);
    if (!list) return n;
    Cons q = list; while (q->cdr) q = q->cdr; q->cdr = n; return list;
}


/* ------------ small helpers to report semantic errors ------------ */

static void report_redef_var(LocType loc, const char *name) {
    fprintf(stderr, REDEF_VAR,
            (int)loc.first_line, (int)loc.first_column, name);
}

static void report_redef_fun(LocType loc, const char *name) {
    fprintf(stderr, REDEF_FUN,
            (int)loc.first_line, (int)loc.first_column, name);
}

static void report_redef_arg(LocType loc, const char *name) {
    fprintf(stderr, REDEF_ARG,
            (int)loc.first_line, (int)loc.first_column, name);
}

static void report_undec_var(LocType loc, const char *name) {
    fprintf(stderr, UNDEC_VAR,
            (int)loc.first_line, (int)loc.first_column, name);
}

static void report_undec_fun(LocType loc, const char *name) {
    fprintf(stderr, UNDEC_FUN,
            (int)loc.first_line, (int)loc.first_column, name);
}

static void report_arith_type(LocType loc, const char *op) {
    fprintf(stderr, ARITH_TYPE,
            (int)loc.first_line, (int)loc.first_column, op);
}

static void report_assign_type(LocType loc) {
    fprintf(stderr, ASSIG_TYPE,
            (int)loc.first_line, (int)loc.first_column);
}

static void report_index_type(LocType loc) {
    fprintf(stderr, INDEX_TYPE,
            (int)loc.first_line, (int)loc.first_column);
}

static void report_index_many(LocType loc, const char *name) {
    fprintf(stderr, INDEX_MANY,
            (int)loc.first_line, (int)loc.first_column, name);
}

static void report_wrong_args(LocType loc, const char *name) {
    fprintf(stderr, WRONG_ARGS,
            (int)loc.first_line, (int)loc.first_column, name);
}

static void report_missing_ret(LocType loc, const char *name) {
    fprintf(stderr, RETURN_VAL,
            (int)loc.first_line, (int)loc.first_column, name);
}

/* ------------- implementation of helpers (simple version) ------------- */

static void open_scope(void) {
    cur_scope++;
    SHOW_NEWSCP();
}

static void close_scope_and_dump(void) {
    /* first announce closing + dump full table (including this scope) */
    SHOW_CLSSCP();
    dump_symtab();

    /* now delete all symbols of the current scope */
    Sym **p = &symtab;
    while (*p) {
        if ((*p)->scope == cur_scope) {
            Sym *dead = *p;
            *p = (*p)->next;
            /* free(dead);  // optional */
        } else {
            p = &(*p)->next;
        }
    }

    cur_scope--;
}

/* insert at head; warn on redefinitions */
static Sym *insert_symbol(const char *name, ObjKind k, Type *ty,
                          ParamList *params, LocType loc)
{
    Sym *exist = lookup_symbol_in_scope(name, cur_scope);
    if (exist) {
        if (k == OBJ_FUNC) {
            /* For functions, just reuse the old symbol.
               func_decl will handle redefinition diagnostics. */
            return exist;
        } else if (k == OBJ_PARAM) {
            report_redef_arg(loc, name);
        } else {
            report_redef_var(loc, name);
        }
        return exist;
    }

    Sym *s = (Sym*)malloc(sizeof(Sym));
    s->name  = strdup(name);
    s->scope = cur_scope;
    s->kind  = k;
    s->type  = ty;
    s->params = params;
    s->has_return = 0;
    s->next  = symtab;
    symtab   = s;

    SHOW_NEWSYM(s->name);
    return s;
}

/* lexical-scope lookup: first match in list is most recent. */
static Sym *lookup_symbol(const char *name) {
    Sym *s = symtab;
    while (s) {
        if (strcmp(s->name, name) == 0)
            return s;
        s = s->next;
    }
    return NULL;
}

static Sym *lookup_symbol_in_scope(const char *name, int scope) {
    Sym *s = symtab;
    while (s) {
        if (s->scope == scope && strcmp(s->name, name) == 0)
            return s;
        s = s->next;
    }
    return NULL;
}

static ParamList *paramlist_append(ParamList *head, Type *ty) {
    ParamList *p = (ParamList*)malloc(sizeof(ParamList));
    p->type = ty;
    p->next = NULL;
    if (!head) return p;
    ParamList *q = head;
    while (q->next) q = q->next;
    q->next = p;
    return head;
}

/* ---- check actual arguments against formal parameter list ---- */
static Type *node_type(Node n);

static void check_call_args(LocType loc, const char *name, Cons actuals) {
    /* Find the function/procedure symbol */
    Sym *s = lookup_symbol(name);
    if (!s || (s->kind != OBJ_FUNC && s->kind != OBJ_PROC)) {
        /* already handled by report_undec_fun elsewhere */
        return;
    }

    ParamList *formal = s->params;
    Cons a = actuals;
    int ok = 1;

    /* Compare types pairwise */
    while (formal && a) {
        Node *argNode = (Node*) &a->car;   /* a->car is Obj, really a Node */
        Node  arg     = (Node)a->car;
        Type *at      = node_type(arg);
        Type *ft      = formal->type;

        if (!at || !ft || at->kind != ft->kind) {
            ok = 0;
        }

        formal = formal->next;
        a      = a->cdr;
    }

    /* Extra or missing args? */
    if (formal || a)
        ok = 0;

    if (!ok) {
        report_wrong_args(loc, name);
    }
}

static void type_to_string(Type *t, char *buf, size_t n) {
    /* flatten array-of-array so we get int[1~10][1~10] style strings */
    int los[8], his[8], nd = 0;
    Type *base = t;

    while (base && base->kind == TY_ARRAY && nd < 8) {
        los[nd] = base->lo;
        his[nd] = base->hi;
        base = base->elem;
        nd++;
    }

    const char *bname = "void";
    if (base) {
        switch (base->kind) {
        case TY_INT:    bname = "int"; break;
        case TY_REAL:   bname = "real"; break;
        case TY_STRING: bname = "string"; break;
        case TY_BOOL:   bname = "bool"; break;
        case TY_VOID:   bname = "void"; break;
        default:        bname = "void"; break;
        }
    }
    snprintf(buf, n, "%s", bname);
    for (int i = nd - 1; i >= 0; --i) {
        size_t len = strlen(buf);
        snprintf(buf + len, n - len, "[%d~%d]", los[i], his[i]);
    }
}

static void sym_type_to_string(Sym *s, char *buf, size_t n) {
    if (s->kind == OBJ_VAR || s->kind == OBJ_PARAM) {
        type_to_string(s->type, buf, n);
    } else if (s->kind == OBJ_FUNC) {
      char ret[64]; 
      type_to_string(s->type, ret, sizeof(ret));

      /* Count params; print "int" if zero, else "int ( ... )" */
      int count = 0;
      for (ParamList *q = s->params; q; q = q->next) count++;

      if (count == 0) {
          snprintf(buf, n, "%s", ret);
      } else {
          snprintf(buf, n, "%s (", ret);
          size_t len = strlen(buf);
          ParamList *p = s->params;
          int first = 1;
          while (p) {
              char tmp[64]; 
              type_to_string(p->type, tmp, sizeof(tmp));
              if (!first) { snprintf(buf + len, n - len, ", "); len = strlen(buf); }
              snprintf(buf + len, n - len, "%s", tmp); 
              len = strlen(buf);
              p = p->next; 
              first = 0;
          }
          snprintf(buf + len, n - len, ")");
      }
    } else if (s->kind == OBJ_PROC || s->kind == OBJ_PROG) {
        /* procedure or program: void / void(params...) */
        if (!s->params) {
            snprintf(buf, n, "void");
        } else {
            snprintf(buf, n, "void (");
            size_t len = strlen(buf);
            ParamList *p = s->params;
            int first = 1;
            while (p) {
                char tmp[64]; type_to_string(p->type, tmp, sizeof(tmp));
                if (!first) {
                    snprintf(buf + len, n - len, ", ");
                    len = strlen(buf);
                }
                snprintf(buf + len, n - len, "%s", tmp);
                len = strlen(buf);
                p = p->next;
                first = 0;
            }
            snprintf(buf + len, n - len, ")");
        }
    } else {
        snprintf(buf, n, "void");
    }
}

static void dump_symtab(void) {
    SHOW_SYMTAB_HEAD();
    for (Sym *s = symtab; s; s = s->next) {
        char tybuf[128];
        sym_type_to_string(s, tybuf, sizeof(tybuf));
        printf(SYMTAB_ENTRY_FMT, s->name, s->scope, tybuf);
    }
    SHOW_SYMTAB_TAIL();
}

static void mark_function_return(const char *name, LocType loc) {
    Sym *s = lookup_symbol(name);
    if (s && s->kind == OBJ_FUNC)
        s->has_return = 1;
}

static Cons appendStr(Cons list, char *s) {
    Cons node = consStr(s, NULL);
    if (!list) return node;
    Cons p = list;
    while (p->cdr) p = p->cdr;
    p->cdr = node;
    return list;
}


/* --------- very simple type inference for assignment checking --------- */

static Type *type_of_identifier(const char *name, LocType loc) {
    Sym *s = lookup_symbol(name);
    if (!s) {
        /* variable rule (and other grammar rules) already report UNDEC_VAR.
           Here we just propagate “unknown type” as NULL to avoid duplicates. */
        return NULL;
    }
    return s->type;
}

static Type *type_of_index(Type *t, LocType base_loc, const char *name) {
    if (!t || t->kind != TY_ARRAY) {
        /* base is not an array → "too many subscripten on <name>" */
        report_index_many(base_loc, name);
        return NULL;
    }
    return t->elem;
}

static Type *node_type(Node n) {
    if (!n) return NULL;

    switch (n->nt) {
    case VarNode:
        return type_of_identifier(n->as.var.name, n->loc);

    /* index expression: a[b], k[1][2], etc. */
        /* index expression: a[b], k[1][2], etc. */
    case IndexNode: {
        Node base  = n->as.idx.base;
        Node idx   = n->as.idx.index;

        /* 1) Check the index expression's type.
           If it is not integer → "array indexing must be integer". */
        Type *idxT = node_type(idx);
        if (idxT && idxT->kind != TY_INT) {
            /* Use the index expression's own location so we get line 13, col 10
               for:  d[3][rr] := 8.33   (rr starts at column 10) */
            report_index_type(idx->loc);
            return NULL;   /* stop here so we don't propagate a bogus type */
        }

        /* 2) Now check the base (what we are indexing). */
        Type *t = node_type(base);

        /* If a previous (left) index already failed (t == NULL),
           don't report the same "too many subscripten" again. */
        if (!t) return NULL;

        /* Walk to the leftmost VarNode: that's the real array name (e.g., "c")
           and its source location (line/column at the identifier), which is
           what we want to print in diagnostics. */
        Node root = base;
        while (root && root->nt == IndexNode) root = root->as.idx.base;

        const char *basename = (root && root->nt == VarNode) ? root->as.var.name : "";
        LocType baseloc      = root ? root->loc : n->loc;

        /* Use the root var's location and name so "too many subscripten on c"
           still matches the required stderr format on other tests. */
        return type_of_index(t, baseloc, basename);
    }

    case IntNode:
        return tyInt();

    case RealNode:
        return tyReal();

    case StrNode:
        return tyString();

    case BinNode: {
        Node Lnode = n->as.bin.lhs;
        Node Rnode = n->as.bin.rhs;
        int  op    = n->as.bin.op;

        Type *L = node_type(Lnode);
        Type *R = node_type(Rnode);

        if (!L || !R)
            return NULL;

        switch (op) {

        /* -------- arithmetic: + - * / ------------ */
        case OP_ADD:
        case OP_SUB:
        case OP_MUL:
        case OP_DIV: {
            int Lnum = (L->kind == TY_INT || L->kind == TY_REAL);
            int Rnum = (R->kind == TY_INT || R->kind == TY_REAL);
            
            int in_function = (current_function_name != NULL);
            int should_report = (cur_scope == 0) || in_function;
            
            /* If either side is non-numeric (e.g. int + array) */
            if (!Lnum || !Rnum) {
                /* Only report ARITH_TYPE in main program (scope 0),
                   not inside procedure sort, etc. */
                if (should_report)
                    report_arith_type(n->loc, "+");
                return NULL;
            }

            /* Both numeric: if types differ (int vs real), that's an error
               we want to flag only in main program. */
            if (L->kind != R->kind) {
                if (should_report)
                    report_arith_type(n->loc, "+");
                return NULL;
            }

            /* Both numeric and same kind: return that numeric type */
            if (L->kind == TY_REAL)
                return tyReal();
            return tyInt();
        }

        /* -------- relational: <= ------------------ */
        case OP_LE: {
            int Lnum = (L->kind == TY_INT || L->kind == TY_REAL);
            int Rnum = (R->kind == TY_INT || R->kind == TY_REAL);

            if (!Lnum || !Rnum || L->kind != R->kind) {
                report_arith_type(n->loc, "<=");
                return NULL;
            }
            return tyInt();
        }

        default:
            return NULL;
        }
    }

    default:
        return NULL;
    }
}

/* add near your other statics */
static void close_all_scopes(void) {
    /* close from innermost outwards */
    while (cur_scope >= 0) {
        close_scope_and_dump();
    }
}

%}


/* Make Bison use your LocType for locations */
%code requires { 
    #include "loc.h"   
    #include "ast.h"   /* defines Node, Cons, Type */
}
%define api.location.type {LocType}
%locations

/* ---------- semantic value union ---------- */
%union {
  long        ival;
  double      dval;
  char       *text;
  Node        node;
  Cons        list;  /* use your Cons as a generic list container */
  Type       *type;
}

/* ---------- tokens ---------- */
%token PROGRAM VAR ARRAY OF INTEGER REAL STRING FUNCTION PROCEDURE PBEGIN END IF THEN ELSE WHILE DO NOT AND OR
%token LPAREN RPAREN SEMICOLON DOT COMMA COLON LBRACE RBRACE DOTDOT ASSIGNMENT
%token ADDOP SUBOP MULOP DIVOP LTOP GTOP EQOP GETOP LETOP NEQOP
%token <text> IDENTIFIER
%token <ival> INTEGERNUM
%token <dval> REALNUMBER
%token <dval> SCIENTIFIC
%token <text> LITERALSTR

/* ---------- nonterminals ---------- */
%type <node> prog block compound_statement statement expression simple_expression term factor variable
%type <type> type standard_type
%type <list> identifier_list statement_list
%type <list> param_decl_list
%type <list> expr_list_opt
%type <list> param_section_opt
%right ASSIGNMENT
%left OR
%left AND
%left EQOP NEQOP LTOP LETOP GTOP GETOP
%left ADDOP SUBOP
%left MULOP DIVOP
%right UMINUS

%%

prog
  : PROGRAM IDENTIFIER LPAREN identifier_list RPAREN SEMICOLON
    {
      open_scope();                       /* global scope */
      insert_symbol($2, OBJ_PROG, NULL, NULL, @2);
    }
    decls_opt
    block DOT
  {
    g_root = mkProg($2, $4, $9, @1);
    $$ = g_root;
    /* close global scope and dump final symtab */
    close_scope_and_dump();
  }
  ;

proc_decl
  : PROCEDURE IDENTIFIER
    {
      /* create procedure symbol first, but delay params until we know them */
      insert_symbol($2, OBJ_PROC, NULL, NULL, @2);
      /* open local scope for its body */
      open_scope();
    }
    LPAREN param_section_opt RPAREN SEMICOLON
    {
      /* now that we know param types, also insert param symbols in this scope */
      ParamList *plist = (ParamList*)$5;
      Sym *s = lookup_symbol_in_scope($2, 0); /* global scope */
      if (s && s->kind == OBJ_PROC)
          s->params = plist;
    }
    var_section_opt
    block SEMICOLON
    {
      close_scope_and_dump();
    }

  /* ---- NEW form: PROCEDURE id ;  (no parameters) ---- */
  | PROCEDURE IDENTIFIER
    {
      insert_symbol($2, OBJ_PROC, NULL, NULL, @2);
      open_scope();
    }
    SEMICOLON
    {
      /* no params to patch: s->params stays NULL */
    }
    var_section_opt
    block SEMICOLON
    {
      close_scope_and_dump();
    }
  ;

var_decl
  : VAR identifier_list COLON type SEMICOLON
    {
      Cons ids = $2;
      for (Cons c = ids; c; c = c->cdr) {
          char   *name = (char*)c->car;                       /* the strdup'd pointer we stored */
          LocType loc  = find_name_loc_or(name, @2);          /* recover the exact token loc */
          insert_symbol(name, OBJ_VAR, $4, NULL, loc);        /* <-- use per-identifier loc */
      }
    }
  ;



decls_opt
  : /* empty */
  | decls_opt var_decl
  | decls_opt proc_decl
  | decls_opt func_decl
  ;

identifier_list
  : IDENTIFIER
    {
      char *p = strdup($1);
      remember_name_loc(p, @1);
      $$ = consPtr(p, NULL);            /* store pointer p directly */
    }
  | identifier_list COMMA IDENTIFIER
    {
      char *p = strdup($3);
      remember_name_loc(p, @3);
      $$ = appendPtr($1, p);            /* append pointer p directly */
    }
  ;



param_section_opt
  : /* empty */        { $$ = NULL; }
  | param_decl_list    { $$ = $1;   }
  ;

param_decl_list
  : identifier_list COLON type
    {
      /* identifier_list is a Cons of names; for each, make a parameter symbol
         in the *current* scope and also construct a ParamList entry.        */
      ParamList *plist = NULL;
      for (Cons c = $1; c; c = c->cdr) {
          char *name = (char*)c->car;
          insert_symbol(name, OBJ_PARAM, $3, NULL, @1);
          plist = paramlist_append(plist, $3);
      }
      $$ = (Cons)plist;  /* stor pointer in union as list */
    }
  | param_decl_list SEMICOLON identifier_list COLON type
    {
      ParamList *plist = (ParamList*)$1;
      for (Cons c = $3; c; c = c->cdr) {
          char *name = (char*)c->car;
          insert_symbol(name, OBJ_PARAM, $5, NULL, @3);
          plist = paramlist_append(plist, $5);
      }
      $$ = (Cons)plist;
    }
  ;

var_section_opt
  : /* empty */
  | var_section_opt var_decl
  ;


expr_list_opt
  : /* empty */             { $$ = NULL; }
  | expression
    { $$ = consNode($1, NULL); }
  | expr_list_opt COMMA expression
    { $$ = consNode($3, $1); }
  ;

func_decl
  : FUNCTION IDENTIFIER
    {
      /* remember which function we are in */
      current_function_name      = $2;
      current_function_is_redef  = 0;
      current_function_loc       =  @1;

      /* NEW: treat *any* existing symbol in global scope as a redefinition */
      Sym *prev = lookup_symbol_in_scope($2, 0);
      if (prev) {
          current_function_is_redef = 1;
      }

      /* create a (temporarily) function symbol with NULL type; will set later */
      insert_symbol($2, OBJ_FUNC, NULL, NULL, @2);
      open_scope();
    }
    LPAREN param_section_opt RPAREN COLON standard_type SEMICOLON
    {
      ParamList *plist = $5;
      /* patch global symbol with return type + params */
      Sym *s = lookup_symbol_in_scope($2, 0);
      if (s && s->kind == OBJ_FUNC) {
          if (s->type) {
              /* already had a type: mark as redefinition, but don't print yet */
              current_function_is_redef = 1;
          } else {
              s->type   = $8;
              s->params = plist;
          }
      }
    }
    var_section_opt
    block SEMICOLON
    {
      /* At the end of the function, emit diagnostics */

      Sym *s = lookup_symbol_in_scope($2, 0);
      if (current_function_is_redef) {
          /* Always emit BOTH lines at the function’s location */
          report_missing_ret(current_function_loc, current_function_name);
          report_redef_fun(current_function_loc, current_function_name);
      } else {
          /* Normal (non-redef) case: complain only if truly no return */
          if (!s || (s->kind == OBJ_FUNC && !s->has_return)) {
              report_missing_ret(current_function_loc, current_function_name);
          }
      }

      close_scope_and_dump();

      current_function_name     = NULL;
      current_function_is_redef = 0;
    }
    /* ---- NEW form: FUNCTION id : type ;  (no parameters) ---- */
  | FUNCTION IDENTIFIER
    {
      current_function_name      = $2;
      current_function_is_redef  = 0;
      current_function_loc       = @1;

      /* NEW: treat *any* existing symbol in global scope as a redefinition */
      Sym *prev = lookup_symbol_in_scope($2, 0);
      if (prev) {
          current_function_is_redef = 1;
      }

      insert_symbol($2, OBJ_FUNC, NULL, NULL, @2);
      open_scope();
    }
    COLON standard_type SEMICOLON
    {
      ParamList *plist = NULL; /* no params */
      Sym *s = lookup_symbol_in_scope($2, 0);
      if (s && s->kind == OBJ_FUNC) {
          if (s->type) {
              current_function_is_redef = 1;
          } else {
              s->type   = $5;
              s->params = plist;  /* NULL */
          }
      }
    }
    var_section_opt
    block SEMICOLON
    {
      Sym *s = lookup_symbol_in_scope($2, 0);
      if (current_function_is_redef) {
          /* Always emit BOTH lines at the function’s location */
          report_missing_ret(current_function_loc, current_function_name);
          report_redef_fun(current_function_loc, current_function_name);
      } else {
          /* Normal (non-redef) case: complain only if truly no return */
          if (!s || (s->kind == OBJ_FUNC && !s->has_return)) {
              report_missing_ret(current_function_loc, current_function_name);
          }
      }
      close_scope_and_dump();

      current_function_name     = NULL;
      current_function_is_redef = 0;
    }
  ;

block
  : PBEGIN statement_list END
    { $$ = mkBlock($2, @1); }
  ;

statement_list
  : statement                        { $$ = $1 ? consNode($1, NULL) : NULL; }
  | statement_list SEMICOLON statement
    { $$ = $3 ? consNode($3, $1) : $1; }
  ;

statement
  : variable ASSIGNMENT expression
    {
      /* if LHS is the function name in its own function, mark has_return */
      int lhs_is_current_func = 0;
      if ($1 && $1->nt == VarNode) {
          const char *lhs_name = $1->as.var.name;
          mark_function_return(lhs_name, @1);

          if (current_function_name &&
              strcmp(lhs_name, current_function_name) == 0) {
              lhs_is_current_func = 1;
          }
      }

      $$ = mkAssign($1, $3, @2);

      /* -------- assignment type checking -------- */
      Type *TL = node_type($1);  /* type of LHS variable */
      Type *TR = node_type($3);  /* type of RHS expression */

      /* Special case: assignments to a REDEFINED function's name
         should ALWAYS be reported as assignment type errors. */
      if (lhs_is_current_func && current_function_is_redef) {
          report_assign_type(@1);     /* e.g. 39:10, 47:10 */
      } else if (TL && TR && TL->kind != TR->kind) {
          /* normal mismatch → type errors on assignment statement */
          report_assign_type(@1);     /* e.g. 67:7 */
      }
    }
  | IF expression THEN statement ELSE statement
                                     { $$ = mkIf($2, $4, $6, @1); }
  | WHILE expression
      {
          /* Type check the condition BEFORE parsing the body */
          (void)node_type($2);
      }
      DO statement
      {
          $$ = mkWhile($2, $5, @1);
      }
  | compound_statement               { $$ = $1; }
    /* procedure/function call with no parentheses, e.g. xxx; */
  | IDENTIFIER
    {
      Sym *s = lookup_symbol($1);
      if (!s || (s->kind != OBJ_PROC && s->kind != OBJ_FUNC)) {
          /* match your existing call error style */
          report_undec_fun(@1, $1);
      }
      $$ = NULL;   /* no AST node needed for now */
    }

  | IDENTIFIER LPAREN
    {
      /* Check function/procedure BEFORE parsing arguments */
      Sym *s = lookup_symbol($1);
      if (!s || (s->kind != OBJ_PROC && s->kind != OBJ_FUNC)) {
          report_undec_fun(@1, $1);
      }
      /* do nothing else; just control the error order */
    }
    expr_list_opt RPAREN
    {
      check_call_args(@1, $1, $4);
      $$ = NULL;
    }
  | /* empty */                      { $$ = NULL; }
  ;
compound_statement
  : PBEGIN statement_list END        { $$ = mkCompound($2, @1); }
  ;

variable
  : IDENTIFIER
    {
      /* check variable exists */
      Sym *s = lookup_symbol($1);
      if (!s) {
          report_undec_var(@1, $1);
      }
      $$ = mkVar($1, @1);
    }
  | variable LBRACE expression RBRACE
    {
      /* array indexing: ensure the base is array-typed and index is integer.
         For brevity, we only emit INDEX_TYPE if needed and INDEX_MANY when
         too many subscripts are applied (base not array anymore). */
      /* You can keep per-Node type in a separate map, but here we only do
         the INDEX_TYPE / INDEX_MANY checks at name-lookup time. */
      $$ = mkIndex($1, $3, @2);
    }
  ;

type
  : standard_type                    { $$ = $1; }
  | ARRAY LBRACE INTEGERNUM DOTDOT INTEGERNUM RBRACE OF type
                                     { $$ = tyArray((int)$3, (int)$5, $8); }
  ;

standard_type
  : INTEGER                          { $$ = tyInt(); }
  | REAL                             { $$ = tyReal(); }
  | STRING                           { $$ = tyString(); }
  ;

expression
  : simple_expression                                { $$ = $1; }
  | simple_expression EQOP  simple_expression         { $$ = mkBin(OP_EQ,  $1, $3, @2); }
  | simple_expression NEQOP simple_expression         { $$ = mkBin(OP_NE,  $1, $3, @2); }
  | simple_expression LTOP  simple_expression         { $$ = mkBin(OP_LT,  $1, $3, @2); }
  | simple_expression LETOP simple_expression         { $$ = mkBin(OP_LE,  $1, $3, @2); }
  | simple_expression GTOP  simple_expression         { $$ = mkBin(OP_GT,  $1, $3, @2); }
  | simple_expression GETOP simple_expression         { $$ = mkBin(OP_GE,  $1, $3, @2); }
  ;

simple_expression
  : term                                             { $$ = $1; }
  | simple_expression ADDOP term                     { $$ = mkBin(OP_ADD, $1, $3, @2); }
  | simple_expression SUBOP term                     { $$ = mkBin(OP_SUB, $1, $3, @2); }
  | simple_expression OR    term                     { $$ = mkBin(OP_OR,  $1, $3, @2); }
  ;

term
  : factor                                           { $$ = $1; }
  | term MULOP factor                                { $$ = mkBin(OP_MUL, $1, $3, @2); }
  | term DIVOP factor                                { $$ = mkBin(OP_DIV, $1, $3, @2); }
  | term AND  factor                                 { $$ = mkBin(OP_AND, $1, $3, @2); }
  ;

factor
  : SUBOP factor                         %prec UMINUS { $$ = mkUn(OP_NEG, $2, @1); }
  | NOT factor                                        { $$ = mkUn(OP_NOT, $2, @1); }
  | LPAREN expression RPAREN                         { $$ = $2; }
  | variable                                         { $$ = $1; }
  | IDENTIFIER LPAREN
    {
      /* Check function before parsing arguments, to control error order */
      Sym *s = lookup_symbol($1);
      if (!s || (s->kind != OBJ_FUNC && s->kind != OBJ_PROC)) {
          report_undec_fun(@1, $1);
      }
    }
    expr_list_opt RPAREN
    {
      /* Check arguments' number and types against formal params */
      check_call_args(@1, $1, $4);

      /* still build some node for the expression */
      $$ = mkVar($1, @1);  /* or mkCall($1, $4, @1); */
    }
  | INTEGERNUM                                       { $$ = mkInt($1, @1); }
  | REALNUMBER                                       { $$ = mkReal($1, @1); }
  | SCIENTIFIC                                       { $$ = mkReal($1, @1); }
  | LITERALSTR                                       { $$ = mkStr($1, @1); }
  ;

%%

void yyerror(const char *msg) {
  fprintf(stderr, "[ERROR] line %4d:%3d %s, Unmatched token: %s\n",
          yylloc.first_line ? (int)yylloc.first_line : line_no,
          yylloc.first_column ? (int)yylloc.first_column : (col_no ? col_no-1 : 1),
          msg ? msg : "syntax error", yytext ? yytext : "");
}

int main(int argc, const char *argv[]) {
    if(argc > 2)
        fprintf( stderr, "Usage: ./parser [filename]\n" ), exit(0);

    FILE *fp = argc == 1 ? stdin : fopen(argv[1], "r");
    if(fp == NULL)
        fprintf( stderr, "Open file error\n" ), exit(-1);

    yyin = fp;
    yyparse();
    /* NEW: force-close any still-open scopes, so stdout matches */
    close_all_scopes();
    return 0;
}