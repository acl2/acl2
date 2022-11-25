; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")
(include-book "variable-tables")
(include-book "tag-tables")
(include-book "term-checkers-atc")
(include-book "types-to-recognizers")

(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/fty/pseudo-event-form-list" :dir :system)
(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/std/system/untranslate-dollar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-expression-generation
  :parents (atc-event-and-code-generation)
  :short "Generation of C expressions."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod pexpr-gin
  :short "Inputs for @(tsee atc-gen-expr-pure)."
  ((inscope atc-symbol-varinfo-alist-list)
   (prec-tags atc-string-taginfo-alist)
   (fn symbol)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred pexpr-ginp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod pexpr-gout
  :short "Outputs for @(tsee atc-gen-expr-pure)."
  ((expr expr)
   (type type)
   (events pseudo-event-form-list)
   (thm-name symbolp)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred pexpr-goutp)

;;;;;;;;;;

(defirrelevant irr-pexpr-gout
  :short "An irrelevant output for @(tsee atc-gen-expr-pure)."
  :type pexpr-goutp
  :body (make-pexpr-gout :expr (irr-expr)
                         :type (irr-type)
                         :events nil
                         :thm-name nil
                         :thm-index 1
                         :names-to-avoid nil
                         :proofs nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bexpr-gin
  :short "Inputs for @(tsee atc-gen-expr-bool)."
  ((inscope atc-symbol-varinfo-alist-list)
   (prec-tags atc-string-taginfo-alist)
   (fn symbol)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred bexpr-ginp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod bexpr-gout
  :short "Outputs for @(tsee atc-gen-expr-bool)."
  ((expr expr)
   (events pseudo-event-form-list)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred bexpr-goutp)

;;;;;;;;;;

(defirrelevant irr-bexpr-gout
  :short "An irrelevant output for @(tsee atc-gen-expr-bool)."
  :type bexpr-goutp
  :body (make-bexpr-gout :expr (irr-expr)
                         :events nil
                         :thm-index 1
                         :names-to-avoid nil
                         :proofs nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-var ((var symbolp)
                          (gin pexpr-ginp))
  :returns (gout pexpr-goutp)
  :short "Generate a C expression from an ACL2 variable."
  (b* (((pexpr-gin gin) gin)
       (info (atc-get-var var gin.inscope))
       ((when (not info))
        (raise "Internal error: the variable ~x0 in function ~x1 ~
                has no associated information." var gin.fn)
        (irr-pexpr-gout))
       (type (atc-var-info->type info)))
    (make-pexpr-gout
     :expr (expr-ident (make-ident :name (symbol-name var)))
     :type type
     :events nil
     :thm-name nil
     :thm-index gin.thm-index
     :names-to-avoid gin.names-to-avoid
     :proofs nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-const ((term pseudo-termp)
                            (const iconstp)
                            (type typep)
                            (type-base-const symbolp)
                            (gin pexpr-ginp)
                            state)
  :guard (type-integerp type)
  :returns (gout pexpr-goutp)
  :short "Generate a C expression and theorem from an ACL2 term
          that represents an integer constant expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem says that the execution yields the term.
     It also says that the term satisfies
     the applicable shallowly embedded type predicate.")
   (xdoc::p
    "The hints cover all possible integer constants,
     but we could make them more nuanced to the specifics of the constant."))
  (b* (((pexpr-gin gin) gin)
       (wrld (w state))
       (expr (expr-const (const-int const)))
       ((when (not gin.proofs))
        (make-pexpr-gout :expr expr
                         :type type
                         :events nil
                         :thm-name nil
                         :thm-index gin.thm-index
                         :names-to-avoid gin.names-to-avoid
                         :proofs nil))
       (thm-name (pack gin.fn '-expr gin.thm-index '-correct))
       ((mv thm-name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                      thm-name nil gin.names-to-avoid wrld))
       (typep (type-to-recognizer type wrld))
       (formula `(and (equal (exec-expr-pure ',expr compst)
                             ,term)
                      (,typep ,term)))
       (formula (untranslate$ formula nil state))
       (fixtype (pack (type-kind type)))
       (exec-const-to-fixtype (pack 'exec-const-to- fixtype))
       (fixtype-integerp (pack fixtype '-integerp))
       (recognizer (pack fixtype 'p))
       (recognizer-of-fixtype (pack recognizer '-of- fixtype))
       (hints `(("Goal" :in-theory '(exec-expr-pure-when-const
                                     (:e expr-kind)
                                     (:e expr-const->get)
                                     ,exec-const-to-fixtype
                                     (:e const-kind)
                                     (:e const-int->get)
                                     (:e iconst->unsignedp)
                                     (:e iconst->length)
                                     (:e iconst->value)
                                     (:e iconst->base)
                                     (:e iconst-length-kind)
                                     (:e iconst-base-kind)
                                     (:e ,fixtype-integerp)
                                     ,type-base-const
                                     ,recognizer-of-fixtype))))
       ((mv event &) (evmac-generate-defthm thm-name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (make-pexpr-gout :expr expr
                     :type type
                     :events (list event)
                     :thm-name thm-name
                     :thm-index (1+ gin.thm-index)
                     :names-to-avoid names-to-avoid
                     :proofs t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atc-gen-expr-pure/bool
  :short "Mutually recursive ACL2 functions to
          generate pure C expressions from ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are for pure expression terms
     and for expression terms returning booleans (which are always pure).")
   (xdoc::p
    "We also generate correctness theorems for the generated expressions.
     The theorems relate (the semantics of) the expressions
     to the ACL2 terms from which they are generated.
     Fow now we only generate theorems for some expressions,
     but eventually we plan to extend this to all the expressions.
     The theorem events are in the @('events') components
     of @(tsee pexpr-gout) and @(tsee bexpr-gout).
     In order to generate unique and relatively readable theorem names,
     we thread through these code generation functions
     an index that gets incremented for each theorem,
     as well as an increasing list of names to avoid."))

  (define atc-gen-expr-pure ((term pseudo-termp)
                             (gin pexpr-ginp)
                             state)
    :returns (mv erp
                 (gout pexpr-goutp))
    :parents (atc-event-and-code-generation atc-gen-expr-pure/bool)
    :short "Generate a C expression from an ACL2 term
            that must be a pure expression term."
    :long
    (xdoc::topstring
     (xdoc::p
      "At the same time,
       we check that the term is a pure expression term,
       as described in the user documentation.")
     (xdoc::p
      "We also return the C type of the expression.")
     (xdoc::p
      "An ACL2 variable is translated to a C variable.
       Its type is looked up in the symbol table passed as input.")
     (xdoc::p
      "If the term fits the pattern of an integer constant
       we translate it to a C integer constant.")
     (xdoc::p
      "If the term fits the pattern of a unary or binary operation,
       we translate it to the application of the operator
       to the recursively generated expressions.
       The type is the result type of the operator.")
     (xdoc::p
      "If the term fits the pattern of a conversion,
       we translate it to a cast of
       the recursively generated subexpression.
       The type is the one of the cast.
       (Future versions of ATC will avoid the cast
       when the conversion happens automatically in C.)")
     (xdoc::p
      "If the term fits the pattern of an array read,
       we translate it to an array subscripting expression
       on the recursively generated expressions.
       The type is the array's element type.")
     (xdoc::p
      "If the term fits the pattern of a structure scalar read,
       we translate it to a structure member or pointer member expression
       on the recursively generated expression.
       The type is the member's type.")
     (xdoc::p
      "If the term fits the pattern of a structure array element read,
       we translate it to an array subscripting expression
       on the recursively generated index expression
       and on a structure member of pointer member expression
       on the recursively generated structure expression.
       The type is the member element's type.")
     (xdoc::p
      "If the term is a call of @(tsee sint-from-boolean),
       we call the mutually recursive ACL2 function
       that translates the argument
       (which must be an expression term returning a boolean)
       to an expression, which we return.
       The type of this expression is always @('int').")
     (xdoc::p
      "If the term is a @(tsee condexpr) call on an @(tsee if) call,
       we call the mutually recursive ACL2 function on the test,
       we call this ACL2 function on the branches,
       and we construct a conditional expression.
       We ensure that the two branches have the same type.")
     (xdoc::p
      "In all other cases, we fail with an error.
       The term is not a pure expression term.
       We could extend this code to provide
       more information to the user at some point.")
     (xdoc::p
      "As we generate the code, we ensure that the ACL2 terms
       are well-typed according to the C types.
       This is subsumed by guard verification for all the code,
       except for any code that is dead (i.e. unreachable) under the guard:
       the dead code passes guard verification
       (under a hypothesis of @('nil'), i.e. false),
       but the resulting C code may not compile.
       The additional type checking we do here should ensure that
       all the code satisfies the C static semantics."))
    (b* (((reterr) (irr-pexpr-gout))
         ((pexpr-gin gin) gin)
         ((when (pseudo-term-case term :var))
          (retok (atc-gen-expr-var (pseudo-term-var->name term) gin)))
         ((erp okp const type type-base-const) (atc-check-iconst term))
         ((when okp) (retok (atc-gen-expr-const
                             term const type type-base-const gin state)))
         ((mv okp op arg-term in-type out-type) (atc-check-unop term))
         ((when okp)
          (b* (((erp (pexpr-gout arg))
                (atc-gen-expr-pure arg-term gin state))
               ((unless (equal arg.type in-type))
                (reterr
                 (msg "The unary operator ~x0 is applied ~
                       to an expression term ~x1 returning ~x2, ~
                       but a ~x3 operand is expected. ~
                       This is indicative of provably dead code, ~
                       given that the code is guard-verified."
                      op arg-term arg.type in-type))))
            (retok (make-pexpr-gout
                    :expr (make-expr-unary :op op
                                           :arg arg.expr)
                    :type out-type
                    :events arg.events
                    :thm-name nil
                    :thm-index arg.thm-index
                    :names-to-avoid arg.names-to-avoid
                    :proofs nil))))
         ((mv okp op arg1-term arg2-term in-type1 in-type2 out-type)
          (atc-check-binop term))
         ((when okp)
          (b* (((erp (pexpr-gout arg1))
                (atc-gen-expr-pure arg1-term gin state))
               ((erp (pexpr-gout arg2))
                (atc-gen-expr-pure arg2-term
                                   (change-pexpr-gin
                                    gin
                                    :thm-index arg1.thm-index
                                    :names-to-avoid arg1.names-to-avoid)
                                   state))
               ((unless (and (equal arg1.type in-type1)
                             (equal arg2.type in-type2)))
                (reterr
                 (msg "The binary operator ~x0 is applied ~
                       to an expression term ~x1 returning ~x2 ~
                       and to an expression term ~x3 returning ~x4, ~
                       but a ~x5 and a ~x6 operand is expected. ~
                       This is indicative of provably dead code, ~
                       given that the code is guard-verified."
                      op arg1-term arg1.type arg2-term arg2.type
                      in-type1 in-type2))))
            (retok (make-pexpr-gout
                    :expr (make-expr-binary :op op
                                            :arg1 arg1.expr
                                            :arg2 arg2.expr)
                    :type out-type
                    :events (append arg1.events arg2.events)
                    :thm-name nil
                    :thm-index arg2.thm-index
                    :names-to-avoid arg2.names-to-avoid
                    :proofs nil))))
         ((mv okp tyname arg-term in-type out-type) (atc-check-conv term))
         ((when okp)
          (b* (((erp (pexpr-gout arg))
                (atc-gen-expr-pure arg-term gin state))
               ((unless (equal arg.type in-type))
                (reterr
                 (msg "The conversion from ~x0 to ~x1 is applied ~
                       to an expression term ~x2 returning ~x3, ~
                       but a ~x0 operand is expected. ~
                       This is indicative of provably dead code, ~
                       given that the code is guard-verified."
                      in-type out-type arg-term arg.type))))
            (retok (make-pexpr-gout
                    :expr (make-expr-cast :type tyname
                                          :arg arg.expr)
                    :type out-type
                    :events arg.events
                    :thm-name nil
                    :thm-index arg.thm-index
                    :names-to-avoid arg.names-to-avoid
                    :proofs nil))))
         ((mv okp arr-term sub-term in-type1 in-type2 out-type)
          (atc-check-array-read term))
         ((when okp)
          (b* (((erp (pexpr-gout arr))
                (atc-gen-expr-pure arr-term gin state))
               ((erp (pexpr-gout sub))
                (atc-gen-expr-pure sub-term
                                   (change-pexpr-gin
                                    gin
                                    :thm-index arr.thm-index
                                    :names-to-avoid arr.names-to-avoid)
                                   state))
               ((unless (and (equal arr.type in-type1)
                             (equal sub.type in-type2)))
                (reterr
                 (msg "The reading of a ~x0 array with a ~x1 index ~
                       is applied to ~
                       an expression term ~x2 returning ~x3 ~
                       and to an expression term ~x4 returning ~x5, ~
                       but a ~x0 and a ~x1 operand is expected. ~
                       This is indicative of provably dead code, ~
                       given that the code is guard-verified."
                      in-type1 in-type2
                      arr-term arr.type sub-term sub.type))))
            (retok (make-pexpr-gout
                    :expr (make-expr-arrsub :arr arr.expr
                                            :sub sub.expr)
                    :type out-type
                    :events (append arr.events sub.events)
                    :thm-name nil
                    :thm-index sub.thm-index
                    :names-to-avoid sub.names-to-avoid
                    :proofs nil))))
         ((mv okp arg-term tag member mem-type)
          (atc-check-struct-read-scalar term gin.prec-tags))
         ((when okp)
          (b* (((erp (pexpr-gout arg))
                (atc-gen-expr-pure arg-term gin state)))
            (cond ((equal arg.type (type-struct tag))
                   (retok (make-pexpr-gout
                           :expr (make-expr-member :target arg.expr
                                                   :name member)
                           :type mem-type
                           :events arg.events
                           :thm-name nil
                           :thm-index arg.thm-index
                           :names-to-avoid arg.names-to-avoid
                           :proofs nil)))
                  ((equal arg.type (type-pointer (type-struct tag)))
                   (retok (make-pexpr-gout
                           :expr (make-expr-memberp :target arg.expr
                                                    :name member)
                           :type mem-type
                           :events arg.events
                           :thm-name nil
                           :thm-index arg.thm-index
                           :names-to-avoid arg.names-to-avoid
                           :proofs nil)))
                  (t (reterr
                      (msg "The reading of a ~x0 structure with member ~x1 ~
                            is applied to ~
                            an expression term ~x2 returning ~x3, ~
                            but a an operand of type ~x4 or ~x5 ~
                            is expected. ~
                            This is indicative of provably dead code, ~
                            given that the code is guard-verified."
                           tag
                           member
                           arg-term
                           arg.type
                           (type-struct tag)
                           (type-pointer (type-struct tag))))))))
         ((mv okp index-term struct-term tag member index-type elem-type)
          (atc-check-struct-read-array term gin.prec-tags))
         ((when okp)
          (b* (((erp (pexpr-gout index))
                (atc-gen-expr-pure index-term gin state))
               ((unless (equal index.type index-type))
                (reterr
                 (msg "The reading of ~x0 structure with member ~x1 ~
                       is applied to ~
                       an expression term ~x2 returning ~x3, ~
                       but a ~x4 operand is expected. ~
                       This is indicative of provably dead code, ~
                       given that the code is guard-verified."
                      (type-struct tag)
                      member
                      index-term
                      index.type
                      index-type)))
               ((erp (pexpr-gout struct))
                (atc-gen-expr-pure struct-term
                                   (change-pexpr-gin
                                    gin
                                    :thm-index index.thm-index
                                    :names-to-avoid index.names-to-avoid)
                                   state)))
            (cond ((equal struct.type (type-struct tag))
                   (retok (make-pexpr-gout
                           :expr (make-expr-arrsub
                                  :arr (make-expr-member
                                        :target struct.expr
                                        :name member)
                                  :sub index.expr)
                           :type elem-type
                           :events (append index.events struct.events)
                           :thm-name nil
                           :thm-index struct.thm-index
                           :names-to-avoid struct.names-to-avoid
                           :proofs nil)))
                  ((equal struct.type (type-pointer (type-struct tag)))
                   (retok (make-pexpr-gout
                           :expr (make-expr-arrsub
                                  :arr (make-expr-memberp
                                        :target struct.expr
                                        :name member)
                                  :sub index.expr)
                           :type elem-type
                           :events (append index.events struct.events)
                           :thm-name nil
                           :thm-index struct.thm-index
                           :names-to-avoid struct.names-to-avoid
                           :proofs nil)))
                  (t (reterr
                      (msg "The reading of ~x0 structure with member ~x1 ~
                            is applied to ~
                            an expression term ~x2 returning ~x3, ~
                            but an operand of type ~x4 or ~x5 ~
                            is expected. ~
                            This is indicative of provably dead code, ~
                            given that the code is guard-verified."
                           tag
                           member
                           struct-term
                           struct.type
                           (type-struct tag)
                           (type-pointer (type-struct tag))))))))
         ((mv okp arg-term) (atc-check-sint-from-boolean term))
         ((when okp)
          (b* (((erp (bexpr-gout arg))
                (atc-gen-expr-bool arg-term
                                   (make-bexpr-gin
                                    :inscope gin.inscope
                                    :prec-tags gin.prec-tags
                                    :fn gin.fn
                                    :thm-index gin.thm-index
                                    :names-to-avoid gin.names-to-avoid
                                    :proofs nil)
                                   state)))
            (retok (make-pexpr-gout :expr arg.expr
                                    :type (type-sint)
                                    :events arg.events
                                    :thm-name nil
                                    :thm-index arg.thm-index
                                    :names-to-avoid arg.names-to-avoid
                                    :proofs nil))))
         ((mv okp test-term then-term else-term) (atc-check-condexpr term))
         ((when okp)
          (b* (((erp (bexpr-gout test))
                (atc-gen-expr-bool test-term
                                   (make-bexpr-gin
                                    :inscope gin.inscope
                                    :prec-tags gin.prec-tags
                                    :fn gin.fn
                                    :thm-index gin.thm-index
                                    :names-to-avoid gin.names-to-avoid
                                    :proofs nil)
                                   state))
               ((erp (pexpr-gout then))
                (atc-gen-expr-pure then-term
                                   (change-pexpr-gin
                                    gin
                                    :thm-index test.thm-index
                                    :names-to-avoid test.names-to-avoid)
                                   state))
               ((erp (pexpr-gout else))
                (atc-gen-expr-pure else-term
                                   (change-pexpr-gin
                                    gin
                                    :thm-index then.thm-index
                                    :names-to-avoid then.names-to-avoid)
                                   state))
               ((unless (equal then.type else.type))
                (reterr
                 (msg "When generating C code for the function ~x0, ~
                       two branches ~x1 and ~x2 of a conditional term ~
                       have different types ~x3 and ~x4; ~
                       use conversion operations, if needed, ~
                       to make the branches of the same type."
                      gin.fn then-term else-term then.type else.type))))
            (retok
             (make-pexpr-gout
              :expr (make-expr-cond :test test.expr
                                    :then then.expr
                                    :else else.expr)
              :type then.type
              :events (append test.events then.events else.events)
              :thm-name nil
              :thm-index else.thm-index
              :names-to-avoid else.names-to-avoid
              :proofs nil)))))
      (reterr
       (msg "When generating C code for the function ~x0, ~
             at a point where ~
             a pure expression term returning a C type is expected, ~
             the term ~x1 is encountered instead, ~
             which is not a C expression term returning a C type; ~
             see the ATC user documentation."
            gin.fn term)))
    :measure (pseudo-term-count term))

  (define atc-gen-expr-bool ((term pseudo-termp)
                             (gin bexpr-ginp)
                             state)
    :returns (mv erp
                 (gout bexpr-goutp))
    :parents (atc-event-and-code-generation atc-gen-expr-pure/bool)
    :short "Generate a C expression from an ACL2 term
            that must be an expression term returning a boolean."
    :long
    (xdoc::topstring
     (xdoc::p
      "At the same time, we check that the term is
       an expression term returning a boolean,
       as described in the user documentation.")
     (xdoc::p
      "If the term is a call of @(tsee not), @(tsee and), or @(tsee or),
       we recursively translate the arguments,
       which must be an expression term returning a boolean,
       and we construct a logical expression
       with the corresponding C operators.")
     (xdoc::p
      "If the term is a call of @('boolean-from-<type>'),
       we call the mutually recursive function
       that translates the argument,
       which must be an expression term returning a C value,
       to an expression, which we return.")
     (xdoc::p
      "In all other cases, we fail with an error.
       The term is not an expression term returning a C value.
       We could extend this code to provide
       more information to the user at some point.")
     (xdoc::p
      "As in @(tsee atc-gen-expr-pure),
       we perform C type checks on the ACL2 terms.
       See  @(tsee atc-gen-expr-pure) for an explanation."))
    (b* (((reterr) (irr-bexpr-gout))
         ((bexpr-gin gin) gin)
         ((mv okp arg-term) (fty-check-not-call term))
         ((when okp)
          (b* (((erp (bexpr-gout arg))
                (atc-gen-expr-bool arg-term gin state)))
            (retok (make-bexpr-gout
                    :expr (make-expr-unary :op (unop-lognot)
                                           :arg arg.expr)
                    :events arg.events
                    :thm-index arg.thm-index
                    :names-to-avoid arg.names-to-avoid
                    :proofs nil))))
         ((mv okp arg1-term arg2-term) (fty-check-and-call term))
         ((when okp)
          (b* (((erp (bexpr-gout arg1))
                (atc-gen-expr-bool arg1-term gin state))
               ((erp (bexpr-gout arg2))
                (atc-gen-expr-bool arg2-term
                                   (change-bexpr-gin
                                    gin
                                    :thm-index arg1.thm-index
                                    :names-to-avoid arg1.names-to-avoid)
                                   state)))
            (retok (make-bexpr-gout
                    :expr (make-expr-binary :op (binop-logand)
                                            :arg1 arg1.expr
                                            :arg2 arg2.expr)
                    :events (append arg1.events arg2.events)
                    :thm-index arg2.thm-index
                    :names-to-avoid arg2.names-to-avoid
                    :proofs nil))))
         ((mv okp arg1-term arg2-term) (fty-check-or-call term))
         ((when okp)
          (b* (((erp (bexpr-gout arg1))
                (atc-gen-expr-bool arg1-term gin state))
               ((erp (bexpr-gout arg2))
                (atc-gen-expr-bool arg2-term
                                   (change-bexpr-gin
                                    gin
                                    :thm-index arg1.thm-index
                                    :names-to-avoid arg1.names-to-avoid)
                                   state)))
            (retok (make-bexpr-gout
                    :expr (make-expr-binary :op (binop-logor)
                                            :arg1 arg1.expr
                                            :arg2 arg2.expr)
                    :events (append arg1.events arg2.events)
                    :thm-index arg2.thm-index
                    :names-to-avoid arg2.names-to-avoid
                    :proofs nil))))
         ((mv okp arg-term in-type) (atc-check-boolean-from-type term))
         ((when okp)
          (b* (((erp (pexpr-gout arg))
                (atc-gen-expr-pure arg-term
                                   (make-pexpr-gin
                                    :inscope gin.inscope
                                    :prec-tags gin.prec-tags
                                    :fn gin.fn
                                    :thm-index gin.thm-index
                                    :names-to-avoid gin.names-to-avoid
                                    :proofs nil)
                                   state))
               ((unless (equal arg.type in-type))
                (reterr
                 (msg "The conversion from ~x0 to boolean is applied to ~
                       an expression term ~x1 returning ~x2, ~
                       but a ~x0 operand is expected. ~
                       This is indicative of provably dead code, ~
                       given that the code is guard-verified."
                      in-type arg-term arg.type))))
            (retok
             (make-bexpr-gout :expr arg.expr
                              :events arg.events
                              :thm-index arg.thm-index
                              :names-to-avoid arg.names-to-avoid
                              :proofs nil)))))
      (reterr
       (msg "When generating C code for the function ~x0, ~
             at a point where ~
             an expression term returning boolean is expected, ~
             the term ~x1 is encountered instead, ~
             which is not a C epxression term returning boolean; ~
             see the ATC user documentation."
            gin.fn term)))
    :measure (pseudo-term-count term))

  :verify-guards nil ; done below
  ///
  (verify-guards atc-gen-expr-pure))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod pexprs-gin
  :short "Inputs for @(tsee atc-gen-expr-pure-list)."
  ((inscope atc-symbol-varinfo-alist-list)
   (prec-tags atc-string-taginfo-alist)
   (fn symbol)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred pexprs-ginp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod pexprs-gout
  :short "Outputs for @(tsee atc-gen-expr-pure-list)."
  ((exprs expr-list)
   (types type-list)
   (events pseudo-event-form-list)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred pexprs-goutp)

;;;;;;;;;;

(defirrelevant irr-pexprs-gout
  :short "An irrelevant output for @(tsee atc-gen-expr-pure-list)."
  :type pexprs-goutp
  :body (make-pexprs-gout :exprs nil
                          :types nil
                          :events nil
                          :thm-index 1
                          :names-to-avoid nil
                          :proofs nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-pure-list ((terms pseudo-term-listp)
                                (gin pexprs-ginp)
                                state)
  :returns (mv erp
               (gout pexprs-goutp))
  :short "Generate a list of C expressions from a list of ACL2 terms
          that must be pure expression terms returning C values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee atc-gen-expr-pure) to lists.
     However, we do not return the C types of the expressions."))
  (b* (((reterr) (irr-pexprs-gout))
       ((pexprs-gin gin) gin)
       ((when (endp terms))
        (retok (make-pexprs-gout :exprs nil
                                 :types nil
                                 :events nil
                                 :thm-index gin.thm-index
                                 :names-to-avoid gin.names-to-avoid
                                 :proofs gin.proofs)))
       ((erp (pexpr-gout first))
        (atc-gen-expr-pure (car terms)
                           (make-pexpr-gin
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :thm-index gin.thm-index
                            :names-to-avoid gin.names-to-avoid
                            :proofs gin.proofs)
                           state))
       ((erp (pexprs-gout rest))
        (atc-gen-expr-pure-list (cdr terms)
                                (change-pexprs-gin
                                 gin
                                 :thm-index first.thm-index
                                 :names-to-avoid first.names-to-avoid
                                 :proofs first.proofs)
                                state)))
    (retok (make-pexprs-gout
            :exprs (cons first.expr rest.exprs)
            :types (cons first.type rest.types)
            :events (append first.events rest.events)
            :thm-index rest.thm-index
            :names-to-avoid rest.names-to-avoid
            :proofs rest.proofs)))
  :verify-guards nil ; done below
  ///
  (verify-guards atc-gen-expr-pure-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-gin
  :short "Inputs for @(tsee atc-gen-expr)."
  ((var-term-alist symbol-pseudoterm-alist)
   (inscope atc-symbol-varinfo-alist-list)
   (fn symbol)
   (prec-fns atc-symbol-fninfo-alist)
   (prec-tags atc-string-taginfo-alist)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred expr-ginp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-gout
  :short "Outputs for @(tsee atc-gen-expr)."
  ((expr exprp)
   (type typep)
   (affect symbol-listp)
   (limit pseudo-termp)
   (events pseudo-event-form-list)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred expr-goutp)

;;;;;;;;;;

(defirrelevant irr-expr-gout
  :short "An irrelevant output for @(tsee atc-gen-expr)."
  :type expr-goutp
  :body (make-expr-gout :expr (irr-expr)
                        :type (irr-type)
                        :affect nil
                        :limit nil
                        :events nil
                        :thm-index 1
                        :names-to-avoid nil
                        :proofs nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr ((term pseudo-termp)
                      (gin expr-ginp)
                      state)
  :returns (mv erp
               (gout expr-goutp))
  :short "Generate a C expression from an ACL2 term
          that must be an expression term."
  :long
  (xdoc::topstring
   (xdoc::p
    "At the same time,
     we check that the term is an expression term,
     as described in the user documentation.")
   (xdoc::p
    "We also return the C type of the expression,
     the affected variables,
     and a limit that suffices for @(tsee exec-expr-call-or-pure)
     to execute the expression completely.")
   (xdoc::p
    "If the term is a call of a function that precedes @('fn')
     in the list of target functions among @('t1'), ..., @('tp'),
     we translate it to a C function call on the translated arguments.
     The type of the expression is the result type of the function,
     which is looked up in the function alist passed as input:
     we ensure that this type is not @('void').
     A sufficient limit for @(tsee exec-fun) to execute the called function
     is retrieved from the called function's information;
     we add 2 to it, to take into account the decrementing of the limit
     to go from @(tsee exec-expr-call-or-pure) to @(tsee exec-expr-call)
     and from there to @(tsee exec-fun).")
   (xdoc::p
    "Otherwise, we attempt to translate the term as a pure expression term.
     The type is the one returned by that translation.
     As limit we return 1, which suffices for @(tsee exec-expr-call-or-pure)
     to not stop right away due to the limit being 0."))
  (b* (((reterr) (irr-expr-gout))
       ((expr-gin gin) gin)
       ((mv okp called-fn arg-terms in-types out-type affect limit)
        (atc-check-cfun-call term gin.var-term-alist gin.prec-fns (w state)))
       ((when okp)
        (b* (((when (type-case out-type :void))
              (reterr
               (msg "A call ~x0 of the function ~x1, which returns void, ~
                     is being used where ~
                     an expression term returning a a non-void C type ~
                     is expected."
                    term called-fn)))
             ((unless (atc-check-cfun-call-args (formals+ called-fn (w state))
                                                in-types
                                                arg-terms))
              (reterr
               (msg "The call ~x0 does not satisfy the restrictions ~
                     on array arguments being identical to the formals."
                    term)))
             ((erp (pexprs-gout args))
              (atc-gen-expr-pure-list arg-terms
                                      (make-pexprs-gin
                                       :inscope gin.inscope
                                       :prec-tags gin.prec-tags
                                       :fn gin.fn
                                       :thm-index gin.thm-index
                                       :names-to-avoid gin.names-to-avoid
                                       :proofs gin.proofs)
                                      state))
             ((unless (equal args.types in-types))
              (reterr
               (msg "The function ~x0 with input types ~x1 ~
                     is applied to expression terms ~x2 returning ~x3. ~
                     This is indicative of provably dead code, ~
                     given that the code is guard-verified."
                    called-fn in-types arg-terms args.types))))
          (retok
           (make-expr-gout
            :expr (make-expr-call :fun (make-ident
                                        :name (symbol-name called-fn))
                                  :args args.exprs)
            :type out-type
            :affect affect
            :limit `(binary-+ '2 ,limit)
            :events args.events
            :thm-index args.thm-index
            :names-to-avoid args.names-to-avoid
            :proofs nil))))
       ((erp (pexpr-gout pure))
        (atc-gen-expr-pure term
                           (make-pexpr-gin :inscope gin.inscope
                                           :prec-tags gin.prec-tags
                                           :fn gin.fn
                                           :thm-index gin.thm-index
                                           :names-to-avoid gin.names-to-avoid
                                           :proofs gin.proofs)
                           state)))
    (retok (make-expr-gout :expr pure.expr
                           :type pure.type
                           :affect affect
                           :limit '(quote 1)
                           :events pure.events
                           :thm-index pure.thm-index
                           :names-to-avoid pure.names-to-avoid
                           :proofs pure.proofs))))
