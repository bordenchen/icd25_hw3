#include <stdlib.h>
#include <string.h>
#include "ast.h"

static Node newNode(NodeType k, LocType loc) {
  Node n = (Node)malloc(sizeof(NodeStr));
  n->nt = k; n->loc = loc; return n;
}

/* types */
static Type *newType(TypeKind k){ Type *t=malloc(sizeof(Type)); t->kind=k; t->lo=t->hi=0; t->elem=NULL; return t; }
Type *tyInt(void){ return newType(TY_INT); }
Type *tyReal(void){ return newType(TY_REAL); }
Type *tyString(void){ return newType(TY_STRING); }
Type *tyBool(void){ return newType(TY_BOOL); }
Type *tyArray(int lo,int hi,Type *elem){ Type *t=newType(TY_ARRAY); t->lo=lo; t->hi=hi; t->elem=elem; return t; }

/* lists */
Cons consNode(Node n, Cons tail){ Cons c = (Cons)malloc(sizeof(ConsStr)); c->car = (Obj)n; c->cdr = tail; return c; }
Cons consStr(char *s, Cons tail){ Cons c = (Cons)malloc(sizeof(ConsStr)); c->car = (Obj)strdup(s); c->cdr = tail; return c; }

/* nodes */
Node mkProg(char *name, Cons ios, Node block, LocType loc){
  Node n=newNode(ProgNode,loc);
  n->as.prog.name=strdup(name); n->as.prog.ios=ios; n->as.prog.block=block; return n;
}
Node mkBlock(Cons stmts, LocType loc){ Node n=newNode(BlockNode,loc); n->as.block.decls=NULL; n->as.block.stmts=stmts; return n; }
Node mkCompound(Cons stmts, LocType loc){ Node n=newNode(CompoundNode,loc); n->as.compound.stmts=stmts; return n; }
Node mkAssign(Node lhs, Node rhs, LocType loc){ Node n=newNode(AssignNode,loc); n->as.assign.lhs=lhs; n->as.assign.rhs=rhs; return n; }
Node mkIf(Node cond, Node thenS, Node elseS, LocType loc){ Node n=newNode(IfNode,loc); n->as.ifs.cond=cond; n->as.ifs.thenS=thenS; n->as.ifs.elseS=elseS; return n; }
Node mkWhile(Node cond, Node body, LocType loc){ Node n=newNode(WhileNode,loc); n->as.whiles.cond=cond; n->as.whiles.body=body; return n; }
Node mkBin(int op, Node lhs, Node rhs, LocType loc){ Node n=newNode(BinNode,loc); n->as.bin.op=op; n->as.bin.lhs=lhs; n->as.bin.rhs=rhs; return n; }
Node mkUn(int op, Node expr, LocType loc){ Node n=newNode(UnNode,loc); n->as.un.op=op; n->as.un.expr=expr; return n; }
Node mkVar(char *name, LocType loc){ Node n=newNode(VarNode,loc); n->as.var.name=strdup(name); return n; }
Node mkIndex(Node base, Node index, LocType loc){ Node n=newNode(IndexNode,loc); n->as.idx.base=base; n->as.idx.index=index; return n; }
Node mkInt(long v, LocType loc){ Node n=newNode(IntNode,loc); n->as.lit_i.ival=v; return n; }
Node mkReal(double v, LocType loc){ Node n=newNode(RealNode,loc); n->as.lit_r.rval=v; return n; }
Node mkStr(char *s, LocType loc){ Node n=newNode(StrNode,loc); n->as.lit_s.sval=strdup(s); return n; }
