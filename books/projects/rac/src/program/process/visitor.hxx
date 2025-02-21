template <typename Derived>
template <typename AbstractBase>
bool RecursiveASTVisitor<Derived>::dispatchTraverse(AbstractBase *e) {
  if (!e)
    return true;

  switch (e->id()) {
#define APPLY(CLASS, _)                                                       \
  case NodesId::CLASS:                                                        \
    if constexpr (std::is_base_of_v<AbstractBase, CLASS>)                     \
      return derived().Traverse##CLASS(static_cast<CLASS *>(e));              \
    else                                                                      \
      UNREACHABLE();
#include "../parser/ast/astnodes.def"
#include "../parser/ast/types.def"
#undef APPLY
  }
  UNREACHABLE();
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseExpression(Expression *e) {
  if (!dispatchTraverse(e))
    return false;

  if (e && !derived().TraverseType(e->get_type())) {
    return false;
  }

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseStatement(Statement *s) {
  return dispatchTraverse(s);
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseSimpleStatement(
    SimpleStatement *s) {
  return dispatchTraverse(s);
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseType(Type *t) {
  return dispatchTraverse(t);
}


template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseConstant(Constant *e) {
  return dispatchTraverse(e);
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseInteger(Integer *e) {
  return derived().WalkUpInteger(e);
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseBoolean(Boolean *e) {
  return derived().WalkUpBoolean(e);
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseParenthesis(Parenthesis *e) {
  if (!derived().postfixTraversal())
    if (!derived().WalkUpParenthesis(e))
      return false;

  if (!derived().TraverseExpression(e->expr_))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpParenthesis(e))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseSymRef(SymRef *e) {
  if (!derived().postfixTraversal())
    if (!derived().WalkUpSymRef(e))
      return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpSymRef(e))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseFunCall(FunCall *e) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpFunCall(e))
      return false;

  if (!std::all_of(e->args.begin(), e->args.end(),
        [&](Expression *e) { return derived().TraverseExpression(e); }))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpFunCall(e))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseTempCall(TempCall *e) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpTempCall(e))
      return false;

  if (!std::all_of(e->args.begin(), e->args.end(),
        [&](Expression *e) { return derived().TraverseExpression(e); }))
    return false;

  if (!std::all_of(e->params.begin(), e->params.end(),
        [&](Expression *e) { return derived().TraverseExpression(e); }))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpTempCall(e))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseInitializer(Initializer *e) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpInitializer(e))
      return false;

  bool b = true;
  for (auto e : e->vals) {
    if (b && !derived().TraverseExpression(e))
      b = false;
  }
  if (!b)
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpInitializer(e))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseArrayRef(ArrayRef *e) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpArrayRef(e))
      return false;

  if (!(derived().TraverseExpression(e->array)
        && derived().TraverseExpression(e->index)))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpArrayRef(e))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseStructRef(StructRef *e) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpStructRef(e))
      return false;

  if (!derived().TraverseExpression(e->base))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpStructRef(e))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseSubrange(Subrange *e) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpSubrange(e))
      return false;

  if (!(derived().TraverseExpression(e->base)
        && derived().TraverseExpression(e->high)
        && derived().TraverseExpression(e->low)))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpSubrange(e))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraversePrefixExpr(PrefixExpr *e) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpPrefixExpr(e))
      return false;

  if (!derived().TraverseExpression(e->expr))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpPrefixExpr(e))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseCastExpr(CastExpr *e) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpCastExpr(e))
      return false;

  if (!derived().TraverseExpression(e->expr))
    return true;

  if (!derived().TraverseType(e->type))
    return true;

  if (derived().postfixTraversal())
    if (!derived().WalkUpCastExpr(e))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseBinaryExpr(BinaryExpr *e) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpBinaryExpr(e))
      return false;

  if (!(derived().TraverseExpression(e->expr1)
        && derived().TraverseExpression(e->expr2)))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpBinaryExpr(e))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseCondExpr(CondExpr *e) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpCondExpr(e))
      return false;

  if (!(derived().TraverseExpression(e->expr1)
        && derived().TraverseExpression(e->expr2)
        && derived().TraverseExpression(e->test)))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpCondExpr(e))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseMultipleValue(MultipleValue *e) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpMultipleValue(e))
      return false;

  if (!std::all_of(e->expr().begin(), e->expr().end(),
        [this](Expression *e) { return derived().TraverseExpression(e); }))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpMultipleValue(e))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseSymDec(SymDec *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpSymDec(s))
      return false;

  if (!derived().TraverseExpression(s->init))
    return false;

  if (!derived().TraverseType(s->get_type()))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpSymDec(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseEnumConstDec(EnumConstDec *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpEnumConstDec(s))
      return false;

  if (!derived().TraverseExpression(s->init))
    return false;

  // We do not traverse its type since it is always processed first.
  // TODO if we overload symdec, we are still looping.

  if (derived().postfixTraversal())
    if (!derived().WalkUpEnumConstDec(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseVarDec(VarDec *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpVarDec(s))
      return false;

  if (!derived().TraverseExpression(s->init))
    return false;

  if (!derived().TraverseType(s->get_type()))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpVarDec(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseMulVarDec(MulVarDec *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpMulVarDec(s))
      return false;

  bool b = true;
  for (auto s : s->decs) {
    if (b && !derived().TraverseStatement(s))
      b = false;
  }
  if (!b)
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpMulVarDec(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseTempParamDec(TempParamDec *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpTempParamDec(s))
      return false;

  if (!derived().TraverseExpression(s->init))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpTempParamDec(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseBreakStmt(BreakStmt *s) {

  return derived().WalkUpBreakStmt(s);
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseReturnStmt(ReturnStmt *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpReturnStmt(s))
      return false;

  if (!derived().TraverseExpression(s->value))
    return false;

  if (!derived().TraverseType(s->returnType))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpReturnStmt(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseNullStmt(NullStmt *s) {
  return derived().WalkUpNullStmt(s);
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseAssertion(Assertion *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpAssertion(s))
      return false;

  if (!derived().TraverseExpression(s->expr))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpAssertion(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseAssignment(Assignment *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpAssignment(s))
      return false;

  if (!derived().TraverseExpression(s->lval))
    return false;

  if (!derived().TraverseExpression(s->rval))
    return false;

  if (!derived().TraverseExpression(s->index))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpAssignment(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseMultipleAssignment(
    MultipleAssignment *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpMultipleAssignment(s))
      return false;

  if (!std::all_of(s->lvals().begin(), s->lvals().end(),
          [this](Expression *e) { return derived().TraverseExpression(e); }))
    return false;

  if (!derived().TraverseExpression(s->rval()))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpMultipleAssignment(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseBlock(Block *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpBlock(s))
      return false;

  if (!std::all_of(s->stmtList.begin(), s->stmtList.end(),
        [&](Statement *s) { return derived().TraverseStatement(s); }))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpBlock(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseIfStmt(IfStmt *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpIfStmt(s))
      return false;

  if (!derived().TraverseExpression(s->test))
    return false;

  if (!derived().TraverseStatement(s->left))
    return false;

  if (!derived().TraverseStatement(s->right))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpIfStmt(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseForStmt(ForStmt *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpForStmt(s))
      return false;

  if (!derived().TraverseStatement(s->init))
    return false;

  if (!derived().TraverseExpression(s->test))
    return false;

  if (!derived().TraverseStatement(s->update))
    return false;

  if (!derived().TraverseStatement(s->body))
    return false;

  if (!derived().postfixTraversal())
    if (!derived().WalkUpForStmt(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseCase(Case *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpCase(s))
      return false;

  if (!derived().TraverseExpression(s->label))
    return false;

  if (!std::all_of(s->action.begin(), s->action.end(),
        [&](Statement *s) { return derived().TraverseStatement(s); }))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpCase(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseSwitchStmt(SwitchStmt *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpSwitchStmt(s))
      return false;

  if (!derived().TraverseExpression(s->test()))
    return false;

  if (!std::all_of(s->cases().begin(),s->cases().end(),
        [&](Case *s) { return derived().TraverseStatement(s); }))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpSwitchStmt(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseFunDef(FunDef *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpFunDef(s))
      return false;

  bool b = true;
  for (auto s : s->params()) {
    if (b && !derived().TraverseStatement(s))
      b = false;
  }
  if (!b)
    return false;

  if (!derived().TraverseType(s->returnType()))
    return false;

  if (!derived().TraverseStatement(s->body()))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpFunDef(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseBuiltin(Builtin *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpBuiltin(s))
      return false;

  bool b = true;
  for(auto s : s->params()) {
    if (b && !derived().TraverseStatement(s))
      b = false;
  }
  if (!b)
    return false;

  if (!derived().TraverseStatement(s->body()))
    return false;

  if (!derived().TraverseType(s->returnType()))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpBuiltin(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseTemplate(Template *s) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpTemplate(s))
      return false;

  bool b = true;
  for (auto s : s->params()) {
    if (b && !derived().TraverseStatement(s))
      b = false;
  }
  if (!b)
    return false;

  if (!derived().TraverseStatement(s->body()))
    return false;

  if (!derived().TraverseType(s->returnType()))
    return false;

  for (auto s : s->tempParams()) {
    if (b && !derived().TraverseStatement(s))
      b = false;
  }
  if (!b)
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpTemplate(s))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraversePrimType(PrimType *t) {
  return derived().WalkUpPrimType(t);
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseDefinedType(DefinedType *t) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpDefinedType(t))
      return false;

  if (!derived().TraverseType(t->getdef()))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpDefinedType(t))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseIntType(IntType *t) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpIntType(t))
      return false;

  if (!derived().TraverseExpression(t->width()))
    return false;

  if (!derived().TraverseExpression(t->isSigned()))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpIntType(t))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseArrayType(ArrayType *t) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpArrayType(t))
      return false;

  if (!derived().TraverseType(t->baseType))
    return false;

  if (!derived().TraverseExpression(t->dim))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpArrayType(t))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseStructType(StructType *t) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpStructType(t))
      return false;

  if (!std::all_of(t->fields().begin(), t->fields().end(), [&](StructField *sf)
        { 
          if (!derived().TraverseType(sf->get_type()))
            return false;

          if (auto val = sf->get_default_value()) {
            return derived().TraverseExpression(*val);
          }
          return true;
        }))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpStructType(t))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseEnumType(EnumType *t) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpEnumType(t))
      return false;

  if (!std::all_of(t->values().begin(), t->values().end(), [&](EnumConstDec *d)
        { return derived().TraverseStatement(d); }))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpEnumType(t))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseMvType(MvType *t) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpMvType(t))
      return false;

  if (!std::all_of(t->types().begin(), t->types().end(), [&](Type *t)
        { return derived().TraverseType(t); }))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpMvType(t))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseInitializerType(InitializerType *t) {

  if (!derived().postfixTraversal())
    if (!derived().WalkUpInitializerType(t))
      return false;

  if (!std::all_of(t->types().begin(), t->types().end(), [&](Type *t)
        { return derived().TraverseType(t); }))
    return false;

  if (derived().postfixTraversal())
    if (!derived().WalkUpInitializerType(t))
      return false;

  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::TraverseErrorType(ErrorType *t) {
  return derived().WalkUpErrorType(t);
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::WalkUpExpression(Expression *e) {
  return derived().VisitExpression(e);
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::WalkUpStatement(Statement *s) {
  return derived().VisitStatement(s);
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::WalkUpType(Type *t) {
  return derived().VisitType(t);
}

#define APPLY(CLASS, PARENT)                                                  \
  template <typename Derived>                                                 \
  bool RecursiveASTVisitor<Derived>::WalkUp##CLASS(CLASS *c) {                \
    if (!derived().WalkUp##PARENT(c))                                         \
      return false;                                                           \
    return derived().Visit##CLASS(c);                                         \
  }
#include "../parser/ast/astnodes.def"
#include "../parser/ast/types.def"
#undef APPLY

template <typename Derived>
bool RecursiveASTVisitor<Derived>::VisitExpression(Expression *) {
  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::VisitStatement(Statement *) {
  return true;
}

template <typename Derived>
bool RecursiveASTVisitor<Derived>::VisitType(Type *) {
  return true;
}

#define APPLY(CLASS, PARENT)                                                  \
  template <typename Derived>                                                 \
  bool RecursiveASTVisitor<Derived>::Visit##CLASS(CLASS *) {                  \
    return true;                                                              \
  }
#include "../parser/ast/astnodes.def"
#include "../parser/ast/types.def"
#undef APPLY
