#ifndef VISITOR_H
#define VISITOR_H

#include <algorithm>

#include "../parser/ast/expressions.h"
#include "../parser/ast/functions.h"
#include "../parser/ast/statements.h"
#include "../parser/ast/types.h"

// This class performs a preorder or postorder depth-first travsersal of the
// AST. This class should be inherited to add custom actions, see astdumper.h
// for an example.
//
// The following explain with details how and the order the traversal, but for
// basic (and most) usage, only Visit* functions are relevant. See astdumper.h
// for a practical example.
//
// This is done in 3 steps:
// 1. Traverse the AST, going on every one with their most specific type.
// 2. WalkUp the type hierarchy from the most specific type to the top-most
//    class (Expression or Statement).
// 3. Perform some action over given through a overriden function VisitCLASS.
//
// Usually, only Visit* functions should be overriden but in some very specific
// cases, Traverse and WalkUp can be overriden. In those cases, don't forget to
// either reimplement their behavior (not recommended) or call
// RecursiveASTVisitor::METHOD.
//
// If any method returns false, abort the traversal and return false, otherwise
// return true.
//
// As an example of the order, let's take the following hierarchy:
//
// Expression -> Constant -> Integer.
//
// If we call TraverseExpression on an Integer node, we will have the following
// calls: TraverseExpression(), TraverseInteger(), WalkUpInteger(),
// WalkUpConstant(), WalkUpExpression(), VisitExpression(), VisitConstant(),
// VisitInteger().
template <typename Derived> class RecursiveASTVisitor {
public:
  // Configure the order of the traversal. To do it in a postfix order,
  // overload this function and return true.
  inline bool postfixTraversal() { return false; }

  // If the method is abstract (like Expression, Statement, Constant, ..),
  // dispatch the expression or statement to their most specific type. Those
  // function are safe to call with null, they will return true.
  //
  // Otherwise, call Traverse on all its child. If we are doing a prefix
  // traversal call WalkUp on itself before traversing its child, if not call
  // it after.
  inline bool TraverseExpression(Expression *e);
  inline bool TraverseStatement(Statement *s);
  inline bool TraverseType(const Type *s);
#define APPLY(CLASS, PARENT) inline bool Traverse##CLASS(CLASS *);
#include "../parser/ast/astnodes.def"
#undef APPLY

#define APPLY(CLASS, PARENT) inline bool Traverse##CLASS(const CLASS *);
#include "../parser/ast/types.def"
#undef APPLY

  // Takes a pointer to a child class and call WalkUp on its parents. Then
  // calls VisitCLASS. WalkUpExpression and WalkUpStatement will only call
  // VisitExpression or VisitStatement since they are at the top of the
  // hierarchy.
  inline bool WalkUpExpression(Expression *e);
  inline bool WalkUpStatement(Statement *s);
  inline bool WalkUpType(const Type *t);
#define APPLY(CLASS, PARENT) inline bool WalkUp##CLASS(CLASS *);
#include "../parser/ast/astnodes.def"
#undef APPLY

#define APPLY(CLASS, PARENT) inline bool WalkUp##CLASS(const CLASS *);
#include "../parser/ast/types.def"
#undef APPLY

  // Those functions are meant to be overload to add action on nodes on
  // specific type. For example: if VisitConstant is overload, all Constants
  // will be processed by the custom action. Remember, VisitCLASS is called
  // for every node of type CLASS *OR* any class derived from CLASS.
  //
  // Let's consider this partial AST translated from: true + 2 * 3;
  //
  // BinaryExpr (+)
  //  |
  //  +-- Boolean (true)
  //  +-- Integer (2)
  //
  // Let's say, we want to display something for each Constant, then we just
  // have to implement `VisitConstant(Constant *) { std::cout << "Constant "
  // }`. It will be run for every nodes derived from Constant: Integer and
  // Boolean. If we run the visitor, it will print: `Constant Constant`.
  //
  // Now, we want to print the value of the literal integer so, we implement
  // VisitInteger(Integer *i) { std::cout << i->val_ << ' '; }.
  // If we run the visitor, it will print: `Constant Constant 2`.
  //
  // Why ? The first `Constant` is when we traverse `true` (`true` is boolean
  // which is derived from Constant). Then we traverse `2` which is both an
  // Integer and a Constant. Since the types are traversed from least to the
  // most specific, VisitConstant is run before VisitInteger.
  //
  inline bool VisitExpression(Expression *e);
  inline bool VisitStatement(Statement *s);
#define APPLY(CLASS, PARENT) inline bool Visit##CLASS(CLASS *);
#include "../parser/ast/astnodes.def"
#undef APPLY

#define APPLY(CLASS, PARENT) inline bool Visit##CLASS(const CLASS *);
#include "../parser/ast/types.def"
#undef APPLY
  inline bool VisitType(const Type *t);

private:
  inline Derived &derived() { return *static_cast<Derived *>(this); }

  template <typename AbstractBase> bool dispatchTraverse(AbstractBase *e);
};

#include "visitor.hxx"

#endif // VISITOR_H
