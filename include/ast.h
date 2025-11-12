#ifndef __AST_H__
#define __AST_H__

#include "loc.h"
#include <stdint.h>

typedef enum {
  ProgNode,
  BlockNode,
  AssignNode,
  IfNode,
  WhileNode,
  CompoundNode,
  BinNode,
  UnNode,
  VarNode,
  IndexNode,
  IntNode,
  RealNode,
  StrNode
} NodeType;

/* forward decls */
typedef struct NodeTag *Node;
typedef struct TypeTag Type;

typedef enum {
  TY_INT, TY_REAL, TY_STRING, TY_BOOL, TY_ARRAY, TY_VOID
} TypeKind;

struct TypeTag {
  TypeKind kind;
  int lo, hi;         /* for arrays */
  Type *elem;         /* for arrays */
};

typedef struct NodeTag{
  NodeType nt;
  LocType  loc;
  union {
    struct { char *name; void *ios; Node block; } prog;
    struct { void *decls; void *stmts; } block;
    struct { Node lhs, rhs; } assign;
    struct { Node cond, thenS, elseS; } ifs;
    struct { Node cond, body; } whiles;
    struct { void *stmts; } compound;
    struct { int op; Node lhs, rhs; } bin;
    struct { int op; Node expr; } un;
    struct { char *name; } var;
    struct { Node base, index; } idx;
    struct { long ival; } lit_i;
    struct { double rval; } lit_r;
    struct { char *sval; } lit_s;
  } as;
} NodeStr;

/* A tiny generic cons list, matching your template */
#define Obj void*
typedef struct ConsTag{
  Obj car;
  struct ConsTag *cdr;
} *Cons, ConsStr;

/* --- Op codes to match parser actions --- */
enum {
  OP_ADD, OP_SUB, OP_MUL, OP_DIV, OP_AND, OP_OR,
  OP_LT, OP_LE, OP_GT, OP_GE, OP_EQ, OP_NE,
  OP_NEG, OP_NOT
};

/* ---- type constructors ---- */
Type *tyInt(void);
Type *tyReal(void);
Type *tyString(void);
Type *tyBool(void);
Type *tyArray(int lo, int hi, Type *elem);

/* ---- node constructors ---- */
Node mkProg(char *name, Cons ios, Node block, LocType loc);
Node mkBlock(Cons stmts, LocType loc);
Node mkCompound(Cons stmts, LocType loc);
Node mkAssign(Node lhs, Node rhs, LocType loc);
Node mkIf(Node cond, Node thenS, Node elseS, LocType loc);
Node mkWhile(Node cond, Node body, LocType loc);
Node mkBin(int op, Node lhs, Node rhs, LocType loc);
Node mkUn(int op, Node expr, LocType loc);
Node mkVar(char *name, LocType loc);
Node mkIndex(Node base, Node index, LocType loc);
Node mkInt(long v, LocType loc);
Node mkReal(double v, LocType loc);
Node mkStr(char *s, LocType loc);

/* ---- list helpers ---- */
Cons consNode(Node n, Cons tail);
Cons consStr(char *s, Cons tail);

#endif
