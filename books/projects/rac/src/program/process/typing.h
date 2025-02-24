#ifndef TYPING_H
#define TYPING_H

#include "visitor.h"

// This pass does the type check, types the nodes which does not have a type
// yet and dereference the defined types.
//
// The typing rule can be found on cppreference and in the Algorithmic C (AC)
// Datatypes Reference Manual, Chapter 2.
//
// At this step, we can have a mix of actual type (ac_int<...>, int, arrays)
// and types defined using typedef. When we want to compare/process types, we
// need the actual type and not the defined one. To do this, there are two
// ways.
//
// First, can use inheritance (definedType in derived from types and will
// dispatch all the methods call to the actual types). This what is the
// preferred solution for "simple" case. The other solution is two use the
// "deref" function (defined below) to always get an actual type. This
// needed in case where we must have a double dispatch: for example, if we want
// to check if two types (t1 and t2) are equals, we may want to use first
// solution: `t1->isEqual(t2)` (dispatch on t1 type) but this probably not the
// wanted behaviour: we are comparing the actual t1's type to t2 that may still
// be a typedef. To compare t1 and t2 actuals types, we must do
// `t1->isEqual(deref(t2)).
//
// To simplify the rest of the parser, after this pass, all the types must be
// dereferenced except for those used in declarations. We want to keep the
// defined types for the pseudocode mode (otherwise, instead of printing the
// defined name in the declarations, it will use the actual type). This hack
// does not impact the rest of the parser as the types used in the declaration
// are only used during typing. This is a dirty trick to keep backward
// compatibility without refactoring the pseudocode mode. In the future (I
// hope), this hack should not be needed and all the types should the actual
// types.
//
class TypingAction final : public RecursiveASTVisitor<TypingAction> {
public:
  TypingAction(DiagnosticHandler &diag) : diag_(diag) {}
  ~TypingAction() {}

  // The type of the current depends on the types of its childs.
  bool postfixTraversal() { return true; }

  // Perform the type dereference. We use Traverse to process the type after
  // it was determined by Visit* functions.
  bool TraverseExpression(Expression *e);

  // Used to keep track of the type of the return type. We assume they are no
  // nested fuction.
  bool TraverseFunDef(FunDef *s);
  bool TraverseTemplate(Template *s);

  // All expressions should be typed.
  bool VisitInteger(Integer *e);
  bool VisitBoolean(Boolean *e);
  bool VisitParenthesis(Parenthesis *e);
  bool VisitSymRef(SymRef *e);
  bool VisitFunCall(FunCall *e);
  bool VisitTempCall(TempCall *e);
  bool VisitInitializer(Initializer *e);
  bool VisitArrayRef(ArrayRef *e);
  bool VisitStructRef(StructRef *e);
  bool VisitSubrange(Subrange *e);
  bool VisitPrefixExpr(PrefixExpr *e);
  bool VisitCastExpr(CastExpr *e);
  bool VisitBinaryExpr(BinaryExpr *e);
  bool VisitCondExpr(CondExpr *e);
  bool VisitMultipleValue(MultipleValue *e);

  // Type and dereference the type of return.
  bool VisitReturnStmt(ReturnStmt *s);
  bool VisitSwitchStmt(SwitchStmt *s);

  // Type check assignements.
  bool VisitAssignment(Assignment *s);
  // Dereference the type.
  bool VisitSymDec(SymDec *s);

private:
  using base_t = RecursiveASTVisitor<TypingAction>;

  DiagnosticHandler &diag_;

  // The return type of the current function. We assume there are no nested
  // functions.
  const Type *type_of_scope_ = nullptr;

  bool template_function_ = false;

  static inline const Type *deref(const Type *t);

  bool check_assignement(const Location &where, const Type *left,
                         const Type *right);
};

#endif // TYPING_H
