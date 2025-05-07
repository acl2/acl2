#include "typing.h"
#include "returnfalse.h"

#include "../parser/ast/expressions.h"
#include "../parser/ast/types.h"

// Expressions:

bool TypingAction::TraverseExpression(Expression *e) {

  // For all expressions, we try to type it...
  if (!base_t::TraverseExpression(e))
    return error();

  // ... and deref its type.
  if (e) {
    e->set_type(deref(e->get_type()));

    if (auto i = dynamic_cast<const IntType *>(e->get_type())) {
      TraverseExpression(i->width());
      TraverseExpression(i->isSigned());
    }
  }

  return true;
}

bool TypingAction::TraverseFunDef(FunDef *e) {

  // When entering a function (a new scope), we store it's return type as it
  // will be usefull to type check the returns.
  assert(!type_of_scope_);
  type_of_scope_ = e->returnType();

  if (!base_t::TraverseFunDef(e)) {
    type_of_scope_ = nullptr;
    return error();
  }

  type_of_scope_ = nullptr;

  return true;
}

bool TypingAction::TraverseTemplate(Template *e) {

  // Same as FunDef, since template are not really
  assert(!type_of_scope_);
  type_of_scope_ = e->returnType();
  template_function_ = true;

  bool success = base_t::TraverseTemplate(e);

  type_of_scope_ = nullptr;
  template_function_ = false;

  return success ? true : error();
}

bool TypingAction::VisitInteger(Integer *e) {

  bool suffix_unsigned = e->has_suffix_unsigned();
  bool suffix_long = e->has_suffix_long();
  bool is_decimal = e->format() == Integer::Format::Decimal;

  // The type of the integer literal is the first type in which the value can
  // fit. If the literal is written in decimal, then it is always signed.
  // https://en.cppreference.com/w/cpp/language/integer_literal
  if (!suffix_unsigned && !suffix_long && e->val_.can_fit_inside<int>()) {
    e->set_type(intType);
  } else if ((!is_decimal || suffix_unsigned) && !suffix_long &&
             e->val_.can_fit_inside<unsigned>()) {
    e->set_type(uintType);
  } else if (!suffix_unsigned && e->val_.can_fit_inside<long>()) {
    e->set_type(int64Type);
  } else if ((!is_decimal || suffix_unsigned) &&
             e->val_.can_fit_inside<unsigned long>()) {
    e->set_type(uint64Type);
  } else {
    diag_
        .new_error(e->loc(),
                   "Integer litteral cannot fit in any available types")
        .note("Try some suffix (U or/and L)")
        .report();
    return error();
  }
  return true;
}

bool TypingAction::VisitBoolean(Boolean *e) {
  e->set_type(boolType);
  return true;
}

bool TypingAction::VisitParenthesis(Parenthesis *e) {
  e->set_type(e->expr_->get_type());
  return true;
}

bool TypingAction::VisitSymRef(SymRef *e) {
  e->set_type(deref(e->symDec->get_type()));

  if (auto i = dynamic_cast<const IntType *>(e->get_type())) {
    TraverseExpression(i->width());
    TraverseExpression(i->isSigned());
  }

  return true;
}

bool TypingAction::VisitFunCall(FunCall *e) {

  if (e->args.size() != e->func->params().size()) {
    diag_
        .new_error(e->loc(), format("Expected %d argument(s), got %d.",
                                    e->func->params().size(), e->args.size()))
        .note("Defined here: ")
        .note_location(e->func->loc())
        .report();
    e->set_type(new ErrorType());
    return error();
  }

  bool has_failed = false;

  for (auto [got, expected] : Zip(e->args, e->func->params())) {
    if (!got->get_type()->canBeImplicitlyCastTo(expected->get_type()) &&
        !got->get_type()->isEqual(expected->get_type())) {

      diag_
          .new_error(got->loc(),
                     format("Expected `%s`, got `%s`",
                            expected->get_original_type()->to_string().c_str(),
                            got->get_type()->to_string().c_str()))
          .context(e->loc())
          .note("Defined here: ")
          .note_location(e->func->loc())
          .report();

      has_failed = true;
    }
  }

  if (has_failed) {
    e->set_type(new ErrorType());
    return error();
  }

  e->set_type(e->func->returnType());
  return true;
}

bool TypingAction::VisitTempCall(TempCall *e) {

  auto type_of_current_scope = type_of_scope_;
  type_of_scope_ = nullptr;

  auto temp = always_cast<Template *>(e->func);

  if (e->params.size() != temp->tempParams().size()) {
    diag_
        .new_error(e->loc(),
                   format("Expected %d argument(s), got %d.",
                          temp->tempParams().size(), e->params.size()))
        .note("Defined here: ")
        .note_location(temp->loc())
        .report();
    e->set_type(new ErrorType());
    return error();
  }

  bool has_failed = false;

  for (auto [got, expected] : Zip(e->params, temp->tempParams())) {
    if (!got->get_type()->canBeImplicitlyCastTo(expected->get_type()) &&
        !got->get_type()->isEqual(expected->get_type())) {

      diag_
          .new_error(got->loc(),
                     format("Expected `%s`, got `%s`",
                            expected->get_original_type()->to_string().c_str(),
                            got->get_type()->to_string().c_str()))
          .context(e->loc())
          .note("Defined here: ")
          .note_location(temp->loc())
          .report();

      has_failed = true;
    }
  }

  if (has_failed) {
    e->set_type(new ErrorType());
    return error();
  }

  // Template are fully type checked for each call with their bindings.
  temp->bindParams(e->params);
  //  TraverseTemplate(temp);
  //  HERE since returntype MUST be instaciated (evalConst).

  if (auto i = dynamic_cast<const IntType *>(e->func->returnType())) {
    auto w = i->width();
    auto s = i->isSigned();

    //    auto ww = new Integer(e->loc(), w);
    //    auto ss = new Boolean(e->loc(), s);

    //    TraverseExpression(ww);
    //    TraverseExpression(ss);

    e->set_type(new IntType(e->loc(), w, s));
  } else {
    e->set_type(e->func->returnType());
  }

  temp->resetParams();

  type_of_scope_ = type_of_current_scope;

  return true;
}

bool TypingAction::VisitInitializer(Initializer *e) {

  // Infer type.
  std::vector<const Type *> types;
  for (auto c : e->vals) {
    types.push_back(c->get_type());
  }
  e->set_type(new InitializerType({e->loc()}, std::move(types)));

  return true;
}

bool TypingAction::VisitArrayRef(ArrayRef *e) {
  if (auto array_type = dynamic_cast<const ArrayType *>(e->array->get_type())) {
    e->set_type(deref(array_type->getBaseType()));

    if (auto i = dynamic_cast<const IntType *>(e->get_type())) {
      TraverseExpression(i->width());
      TraverseExpression(i->isSigned());
    }

  } else {
    // AC register
    e->set_type(new IntType(e->loc(), Integer::one_v(e->loc()), Boolean::false_v(e->loc())));
  }
  return true;
}

bool TypingAction::VisitStructRef(StructRef *e) {
  const StructType *t = always_cast<const StructType *>(e->base->get_type());
  e->set_type(deref(t->getField(e->field)->get_type()));
  return true;
}

bool TypingAction::VisitSubrange(Subrange *e) {

  if (const IntType *t = dynamic_cast<const IntType *>(e->base->get_type())) {

    e->set_type(new IntType(e->loc(), e->width(), t->isSigned()));
  } else {
    diag_
        .new_error(e->base->loc(),
                   format("Base (of type %s) is not a register",
                          e->base->get_type()->to_string().c_str()))
        .context(e->loc())
        .report();
    e->set_type(new ErrorType());
    return error();
  }

  return true;
}

bool TypingAction::VisitPrefixExpr(PrefixExpr *e) {

  const Type *expr_type = e->expr->get_type();

  // Convert an unscoped enum (scoped enum are not supported) to int.
  if (isa<const EnumType *>(expr_type)) {
    expr_type = intType;
  }

  // Type primtive type according to section: "Unary arithmetic operators" of
  // https://en.cppreference.com/w/cpp/language/operator_arithmetic
  if (auto t = dynamic_cast<const PrimType *>(expr_type)) {

    if (e->op == PrefixExpr::Op::Not) {
      e->set_type(boolType);
    } else {

      PrimType *this_type = new PrimType(*t);
      this_type->integerPromtion();
      e->set_type(this_type);
    }
    return true;
  }

  // Type integer register type according to ac_datatypes_ref section 2.3.4.
  if (auto t = dynamic_cast<const IntType *>(expr_type)) {
    switch (e->op) {
    case PrefixExpr::Op::UnaryPlus:
      e->set_type(t);
      break;
    case PrefixExpr::Op::UnaryMinus:
      e->set_type(new IntType(e->loc(),
                              new BinaryExpr(e->loc(), t->width(),
                                             Integer::one_v(e->loc()),
                                             BinaryExpr::Op::Plus),
                              Boolean::true_v(e->loc())));
      break;
    case PrefixExpr::Op::BitNot:
      // ac_int<W+!S, true>
      e->set_type(
          new IntType(e->loc(),
                      new CondExpr(e->loc(), t->width(),
                                   new BinaryExpr(e->loc(), t->width(),
                                                  Integer::one_v(e->loc()),
                                                  BinaryExpr::Op::Plus),
                                   t->isSigned()),
                      Boolean::true_v(e->loc())));
      break;
    case PrefixExpr::Op::Not:
      e->set_type(boolType);
      break;
    }
    return true;
  }

  // No overload found.
  diag_
      .new_error(
          e->expr->loc(),
          format("Cannot apply `%s` to an argument of type `%s` which is not a "
                 "register type or a primitive type, aka int, int64, uint, "
                 "uint64, bool.",
                 to_string(e->op).c_str(), expr_type->to_string().c_str()))
      .context(e->loc())
      .report();

  e->set_type(new ErrorType());
  return error();
}

bool TypingAction::VisitCastExpr(CastExpr *e) {

  const Type *t = deref(e->type);

  bool source_depends_on_template_parameter = false;

  if (auto i = dynamic_cast<const IntType *>(e->expr->get_type())) {
    TraverseExpression(i->width());
    TraverseExpression(i->isSigned());
    source_depends_on_template_parameter =
        !i->width()->isStaticallyEvaluable() ||
        !i->isSigned()->isStaticallyEvaluable();
  }

  e->set_type(t);
  if (!e->expr->get_type()->canBeImplicitlyCastTo(t)) {

    if (source_depends_on_template_parameter) {
      diag_
          .new_error(e->loc(),
                     format("Incompatible types: %s cannot be cast to %s",
                            e->expr->get_type()->to_string().c_str(),
                            t->to_string().c_str()))
          .note("To convert types depending on template parameters to "
                "primitive types, you should add an explicit conversion "
                "(like "
                "this ac_int<32, true>(...) to convert to int)")
          .report();
    } else {
      diag_
          .new_error(e->loc(),
                     format("Incompatible types: %s cannot be cast to %s",
                            e->expr->get_type()->to_string().c_str(),
                            t->to_string().c_str()))
          .report();
    }

    return error();
  }

  return true;
}

bool TypingAction::VisitBinaryExpr(BinaryExpr *e) {

  const Type *t1 = e->expr1->get_type();
  const Type *t2 = e->expr2->get_type();

  // Convert an unscoped enum (scoped enum are not supported) to int.
  if (isa<const EnumType *>(t1)) {
    t1 = intType;
  }
  if (isa<const EnumType *>(t2)) {
    t2 = intType;
  }

  // Both primtype: we follow those rules:
  // https://en.cppreference.com/w/cpp/language/operator_arithmetic.
  if (isa<const PrimType *>(t1) && isa<const PrimType *>(t2)) {

    PrimType *t1_promoted = new PrimType(*always_cast<const PrimType *>(t1));
    t1_promoted->integerPromtion();

    PrimType *t2_promoted = new PrimType(*always_cast<const PrimType *>(t2));
    t2_promoted->integerPromtion();

    if (BinaryExpr::isOpShift(e->op)) {
      e->set_type(t1_promoted);
      delete t2_promoted;
    } else if (BinaryExpr::isOpArithmetic(e->op) ||
               BinaryExpr::isOpBitwise(e->op)) {
      e->set_type(PrimType::usual_conversions(t1_promoted, t2_promoted));
    } else if (BinaryExpr::isOpCompare(e->op) ||
               BinaryExpr::isOpLogical(e->op)) {
      e->set_type(boolType);
    } else {
      UNREACHABLE();
    }

    return true;
  }

  if (isa<const IntType *>(t1) || isa<const IntType *>(t2)) {

    // If e1 if not a intType, try to convert to t2.
    IntType *t1_promoted = nullptr;
    if (auto int_type = dynamic_cast<const IntType *>(t1)) {
      t1_promoted = new IntType(*int_type);
    } else if (auto pt = dynamic_cast<const PrimType *>(t1)) {
      t1_promoted = IntType::FromPrimType(pt);
    } else {
      diag_
          .new_error(e->expr1->loc(),
                     format("Invalid type: left operand is a `%s` but right "
                            "(%s) is not convertible to a register type.",
                            t2->to_string().c_str(), t1->to_string().c_str()))
          .context(e->loc())
          .report();

      e->set_type(new ErrorType());
      return error();
    }

    // Same with e2.
    IntType *t2_promoted = nullptr;
    if (auto int_type = dynamic_cast<const IntType *>(t2)) {
      t2_promoted = new IntType(*int_type);
    } else if (auto pt = dynamic_cast<const PrimType *>(t2)) {
      t2_promoted = IntType::FromPrimType(pt);
    } else {
      diag_
          .new_error(e->expr2->loc(),
                     format("Invalid type: right operand is a `%s` but left "
                            "(%s) is not convertible to a register type.",
                            t1->to_string().c_str(), t2->to_string().c_str()))
          .context(e->loc())
          .report();

      e->set_type(new ErrorType());
      return error();
    }

    Expression *w1 = t1_promoted->width();
    Expression *s1 = t1_promoted->isSigned();
    Expression *w2 = t2_promoted->width();
    Expression *s2 = t2_promoted->isSigned();

    Expression *w_res = nullptr;
    Expression *s_res = nullptr;

    if (BinaryExpr::isOpShift(e->op)) {
      w_res = w1;
      s_res = s1;
    } else if (BinaryExpr::isOpBitwise(e->op)) {
      // w_res = std::max(w1 + (!s1 && s2), w2 + (!s2 && s1));
      // w1 + (!s1 && s2)
      Expression *left = new BinaryExpr(
          e->loc(), w1,
          new BinaryExpr(e->loc(),
                         new PrefixExpr(e->loc(), s1, PrefixExpr::Op::Not), s2,
                         BinaryExpr::Op::And),
          BinaryExpr::Op::Plus);

      // w2 + (!s2 && s1)
      Expression *right = new BinaryExpr(
          e->loc(), w2,
          new BinaryExpr(e->loc(),
                         new PrefixExpr(e->loc(), s2, PrefixExpr::Op::Not), s1,
                         BinaryExpr::Op::And),
          BinaryExpr::Op::Plus);

      // max(left, right)
      w_res = new CondExpr(
          e->loc(), left, right,
          new BinaryExpr(e->loc(), left, right, BinaryExpr::Op::GreaterEqual));

      s_res = (e->op == BinaryExpr::Op::Minus)
                  ? static_cast<Expression *>(Boolean::true_v(e->loc()))
                  : new BinaryExpr(e->loc(), s1, s2, BinaryExpr::Op::Or);
    } else if (e->op == BinaryExpr::Op::Plus ||
               e->op == BinaryExpr::Op::Minus) {
      // w_res = std::max(w1 + (!s1 && s2), w2 + (!s2 && s1)) + 1;

      // w1 + (!s1 && s2)
      Expression *left = new BinaryExpr(
          e->loc(), w1,
          new BinaryExpr(e->loc(),
                         new PrefixExpr(e->loc(), s1, PrefixExpr::Op::Not), s2,
                         BinaryExpr::Op::And),
          BinaryExpr::Op::Plus);

      // w2 + (!s2 && s1)
      Expression *right = new BinaryExpr(
          e->loc(), w2,
          new BinaryExpr(e->loc(),
                         new PrefixExpr(e->loc(), s2, PrefixExpr::Op::Not), s1,
                         BinaryExpr::Op::And),
          BinaryExpr::Op::Plus);

      // max(left, right)
      w_res = new CondExpr(
          e->loc(), left, right,
          new BinaryExpr(e->loc(), left, right, BinaryExpr::Op::GreaterEqual));

      // w_res + 1
      w_res = new BinaryExpr(e->loc(), w_res, Integer::one_v(e->loc()),
                             BinaryExpr::Op::Plus);

      s_res = (e->op == BinaryExpr::Op::Minus)
                  ? static_cast<Expression *>(Boolean::true_v(e->loc()))
                  : new BinaryExpr(e->loc(), s1, s2, BinaryExpr::Op::Or);

    } else if (e->op == BinaryExpr::Op::Times ||
               e->op == BinaryExpr::Op::Divide) {
      w_res = new BinaryExpr(e->loc(), w1, w2, BinaryExpr::Op::Plus);
      s_res = new BinaryExpr(e->loc(), s1, s2, BinaryExpr::Op::Or);

    } else if (e->op == BinaryExpr::Op::Mod) {

      // w2 + (!s2 && s1)
      Expression *right = new BinaryExpr(
          e->loc(), w2,
          new BinaryExpr(e->loc(),
                         new PrefixExpr(e->loc(), s2, PrefixExpr::Op::Not), s1,
                         BinaryExpr::Op::And),
          BinaryExpr::Op::Plus);

      // min(w1, w2 + (!s2 && s1));
      w_res = new CondExpr(
          e->loc(), w2, right,
          new BinaryExpr(e->loc(), w2, right, BinaryExpr::Op::GreaterEqual));

      s_res = s1;

    } else if (BinaryExpr::isOpCompare(e->op) ||
               BinaryExpr::isOpLogical(e->op)) {
      e->set_type(boolType);
      return true;
    } else {
      UNREACHABLE();
    }

    TraverseExpression(w_res);
    TraverseExpression(s_res);

    e->set_type(new IntType(e->loc(), w_res, s_res));

    return true;
  }

  // No overload found.
  diag_
      .new_error(e->loc(),
                 format("Cannot apply `%s` to arguments of type %s and %s",
                        to_string(e->op).c_str(), t1->to_string().c_str(),
                        t2->to_string().c_str()))
      .context(e->loc())
      .note("They should be both a primitive type (like an int or enum) or a "
            "register type.")
      .report();

  e->set_type(new ErrorType());
  return error();
}

bool TypingAction::VisitCondExpr(CondExpr *e) {

  // Convertible to bool
  if (!isIntegerType(e->test->get_type())) {
    diag_
        .new_error(e->test->loc(),
                   format("Expected a boolean, got `%s`.",
                          e->test->get_type()->to_string().c_str()))
        .context(e->loc())
        .report();

    e->set_type(new ErrorType());
    return error();
  }

  // Both are primitive types but not necessarily the same.
  if (auto t1 = dynamic_cast<const PrimType *>(e->expr1->get_type())) {
    if (auto t2 = dynamic_cast<const PrimType *>(e->expr2->get_type())) {
      e->set_type(PrimType::usual_conversions(t1, t2, false));
      return true;
    }
  }

  // They are exactly the same type, for ex: if both are arrays, they need to
  // be array of the same type and size.
  if (e->expr1->get_type()->isEqual(e->expr2->get_type())) {
    e->set_type(e->expr1->get_type());
    return true;
  }

  diag_
      .new_error(e->loc(),
                 format("Left and right do not share same type (left is `%s` "
                        "and right `%s`).",
                        e->expr1->get_type()->to_string().c_str(),
                        e->expr2->get_type()->to_string().c_str()))
      .report();

  e->set_type(new ErrorType());
  return error();
}

bool TypingAction::VisitMultipleValue(MultipleValue *e) {

  const MvType *t = static_cast<const MvType *>(e->get_type());
  // First, check if there number or argument is correct.
  if (e->expr().size() != t->size()) {
    diag_
        .new_error(
            e->loc(),
            format("Expected %d argument(s) (from its type: `%s`), got `%d`.",
                   t->size(), t->to_string().c_str(), e->expr().size()))
        .report();
    e->set_type(new ErrorType());
    return error();
  }

  // Then, if each argument is of correct type.
  bool has_failed = false;
  unsigned size = e->expr().size();
  for (unsigned i = 0; i < size; ++i) {

    const Type *expected = t->get(i);
    const Type *actual = e->expr()[i]->get_type();

    if (!actual->canBeImplicitlyCastTo(deref(expected))) {

      diag_
          .new_error(e->expr()[i]->loc(),
                     format("Expected `%s` (from `%s` at index %d), got `%s`",
                            expected->to_string().c_str(),
                            t->to_string().c_str(), i,
                            actual->to_string().c_str()))
          .context(e->loc())
          .report();

      has_failed = true;
    }
  }

  // Replace the given type by an error.
  if (has_failed) {
    e->set_type(new ErrorType());
    return error();
  }

  return true;
}

// Statements:

bool TypingAction::VisitReturnStmt(ReturnStmt *s) {

  s->returnType = deref(type_of_scope_);
  assert(s->returnType);

  if (auto i = dynamic_cast<const IntType *>(type_of_scope_)) {
    TraverseExpression(i->width());
    TraverseExpression(i->isSigned());
  }

  if (!template_function_) {
    return check_assignement(s->loc(), s->returnType, s->value->get_type());
  } else {
    return true;
  }
}

bool TypingAction::VisitSwitchStmt(SwitchStmt *s) {

  const Type *t = s->test()->get_type();

  bool canBeCastToInt = t->canBeImplicitlyCastTo(uint64Type) ||
                        t->canBeImplicitlyCastTo(int64Type);

  if (!isa<const PrimType *>(t) && !canBeCastToInt) {
    diag_
        .new_error(s->test()->loc(),
                   format("Expected a primtive type, got `%s`",
                          t->to_string().c_str()))
        .context(s->loc())
        .report();

    return error();
  }

  return std::all_of(s->cases().begin(), s->cases().end(), [this](Case *c) {
    // Default case.
    if (c->isDefaultCase()) {
      return true;
    }

    // A label is either an enum value or a constant primtive.
    const Type *t = c->label->get_type();
    if (!(isa<const PrimType *>(t) && c->label->isStaticallyEvaluable()) &&
        !isa<const EnumType *>(t)) {
      diag_
          .new_error(c->label->loc(),
                     "Case label must be an integer or an enum constant.")
          .context(c->loc())
          .report();
      return error();
    }
    return true;
  });
}

bool TypingAction::VisitAssignment(Assignment *s) {

  if (auto symRef = dynamic_cast<SymRef *>(s->lval)) {
    if (symRef->get_type()->isConst()) {
      diag_
          .new_error(s->lval->loc(),
                     format("Assignment of read-only variable %s",
                            symRef->symDec->getname()))
          .context(s->loc())
          .note("defined here")
          .note_location(symRef->symDec->loc())
          .report();
      return error();
    }
  } else if (auto ar = dynamic_cast<ArrayRef *>(s->lval)) {
    if (!isa<const ArrayType *>(ar->array->get_type())) {
      ar->set_type(new IntType(ar->loc(),
                               Integer::one_v(ar->loc()),
                               Boolean::false_v(ar->loc())));
    }
  }

  if (!strcmp(s->op, "set_slc")) {

    if (!isa<const IntType *>(s->lval->get_type())) {
      diag_
          .new_error(s->lval->loc(),
                     format("Base (of type %s) is not a register",
                            s->lval->get_type()->to_string().c_str()))
          .context(s->loc())
          .report();
      return error();
    }

    if (!isa<const IntType *>(s->rval->get_type())) {
      diag_
          .new_error(s->rval->loc(),
                     format("Value (of type %s) is not a register",
                            s->rval->get_type()->to_string().c_str()))
          .context(s->loc())
          .report();
      return error();
    }

    if (!isIntegerType(s->index->get_type())) {
      diag_
          .new_error(
              s->index->loc(),
              format("Expected an integer (ac_int, int, ..,), got %s instead",
                     s->index->get_type()->to_string().c_str()))
          .context(s->loc())
          .report();
      return error();
    }

    s->resolveOverload();
    // We force to retype lval since it was been modified in resolveOverload().
    TraverseExpression(s->lval);

    return true;
  }

  if (!template_function_) {
    return check_assignement(s->loc(), s->lval->get_type(),
                             s->rval->get_type());
  } else {
    return true;
  }
}

bool TypingAction::VisitSymDec(SymDec *s) {

  s->set_type(deref(s->get_type()));

  if (s->init && !template_function_) {

    if (auto i = dynamic_cast<const IntType *>(s->get_type())) {
      TraverseExpression(i->width());
      TraverseExpression(i->isSigned());
    }

    auto sym_type = deref(s->get_type());

    if (isa<const EnumType *>(s->get_type())) {
      sym_type = intType;
    }

    return check_assignement(s->loc(), sym_type, s->init->get_type());
  }
  return true;
}

bool TypingAction::VisitArrayType(const ArrayType *t) {

  if (t->fast_repr()) {
    if (!t->isConst()) {
      diag_.new_error(t->get_original_location(), "Fast array must be const")
        .report();
      return error();
    }
  }
  return true;
}

bool TypingAction::check_assignement(const Location &where, const Type *left,
                                     const Type *right) {

  // TODO: refactore this nightmare.
  // Initializer list can be used in two differents context: array and
  // struct. Strong typed Initialization is not supported yet.
  if (auto t = dynamic_cast<const InitializerType *>(right)) {

    if (auto array = dynamic_cast<const ArrayType *>(left)) {

      unsigned array_size = array->dim->evalConst();

      if (t->size() > array_size) {
        diag_
            .new_error(
                where,
                format("Too many arguments, expected %d argument(s) got %d",
                       array_size, t->size()))
            .report();
        return error();
      }

      const Type *arrayBaseType = deref(array->baseType);

      auto is_correct =
          std::all_of(t->types().begin(), t->types().end(), [&](const Type *t) {
            if (!check_assignement(where, arrayBaseType, t)) {
              return false;
            }
            return true;
          });

      return is_correct ? true : error();

    } else if (auto struct_ = dynamic_cast<const StructType *>(left)) {

      unsigned struct_size = struct_->fields().size();

      if (t->size() > struct_size) {
        diag_
            .new_error(
                where,
                format("Too many arguments, expected %d argument(s) got %d",
                       struct_size, t->size()))
            .report();
        return error();
      }

      unsigned i = 0;
      auto is_correct =
          std::all_of(t->types().begin(), t->types().end(), [&](const Type *t) {
            const Type *field_type = struct_->fields()[i]->get_type();
            if (!check_assignement(where, deref(field_type), t)) {
              return false;
            }
            ++i;
            return true;
          });

      return is_correct ? true : error();

    } else if (auto mv = dynamic_cast<const MvType *>(left)) {

      if (t->size() != mv->size()) {
        diag_
            .new_error(
                where,
                format("Too many arguments, expected %d argument(s) got %d",
                       mv->size(), t->size()))
            .report();
        return error();
      }

      unsigned i = 0;
      auto is_correct =
          std::all_of(t->types().begin(), t->types().end(), [&](const Type *t) {
            if (!t->canBeImplicitlyCastTo(deref(mv->get(i)))) {
              diag_
                  .new_error(
                      where,
                      format("Wrong type provided, expected %s but got %s",
                             mv->get(i)->to_string().c_str(),
                             t->to_string().c_str()))
                  .report();
              return false;
            }
            ++i;
            return true;
          });

      return is_correct ? true : error();
    }
  }

  bool is_same_type = right->isEqual(left);
  bool can_be_cast = right->canBeImplicitlyCastTo(left);

  if (!is_same_type && !can_be_cast) {
    diag_
        .new_error(where, format("Incompatible types: %s cannot be cast to %s",
                                 right->to_string().c_str(),
                                 left->to_string().c_str()))
        .note("To convert types depending on template parameters to "
              "primitive types, you should add an explicit conversion (like "
              "this ac_int<32, true>(...) to convert to int)")
        .report();
    return error();
  }
  return true;
}

const Type *TypingAction::deref(const Type *t) {

  if (const DefinedType *dt = dynamic_cast<const DefinedType *>(t)) {
    assert(dt->derefType());
    return dt->derefType();
  } else {
    return t;
  }
}
