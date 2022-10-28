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
(include-book "pretty-printer" :ttags ((:open-output-channel!)))
(include-book "dynamic-semantics")
(include-book "shallow-embedding")
(include-book "table")
(include-book "variable-tables")
(include-book "function-tables")
(include-book "tag-tables")
(include-book "object-tables")
(include-book "term-checkers-atc")

(include-book "symbolic-execution-rules/top")

(include-book "../language/static-semantics")

(include-book "kestrel/event-macros/applicability-conditions" :dir :system)
(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/fty/pseudo-event-form-list" :dir :system)
(include-book "kestrel/std/strings/strtok-bang" :dir :system)
(include-book "kestrel/std/system/add-suffix-to-fn-lst" :dir :system)
(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/std/system/function-symbolp" :dir :system)
(include-book "kestrel/std/system/genvar-dollar" :dir :system)
(include-book "kestrel/std/system/measure-plus" :dir :system)
(include-book "kestrel/std/system/one-way-unify-dollar" :dir :system)
(include-book "kestrel/std/system/termination-theorem-dollar" :dir :system)
(include-book "kestrel/std/system/ubody-plus" :dir :system)
(include-book "kestrel/std/system/uguard-plus" :dir :system)
(include-book "kestrel/std/system/untranslate-dollar" :dir :system)
(include-book "kestrel/std/system/well-founded-relation-plus" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)
(include-book "kestrel/utilities/doublets" :dir :system)
(include-book "std/typed-alists/keyword-symbol-alistp" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)
(include-book "tools/trivial-ancestors-check" :dir :system)

(local (include-book "kestrel/std/basic/member-symbol-name" :dir :system))
(local (include-book "kestrel/std/system/all-fnnames" :dir :system))
(local (include-book "kestrel/std/system/all-vars" :dir :system))
(local (include-book "kestrel/std/system/flatten-ands-in-lit" :dir :system))
(local (include-book "kestrel/std/system/w" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (include-book "projects/apply/loop" :dir :system))
(local (in-theory (disable acl2::loop-book-theory)))

(local (in-theory (disable state-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to a more general library:

(defrule pseudo-term-list-count-of-pseudo-term-call->args
  (implies (pseudo-term-case term :call)
           (< (pseudo-term-list-count (pseudo-term-call->args term))
              (pseudo-term-count term)))
  :rule-classes :linear)

(defrule pseudo-term-count-of-pseudo-lambda->body
  (implies (and (not (member-eq (pseudo-term-kind term)
                                '(:null :var :quote)))
                (pseudo-lambda-p (pseudo-term-call->fn term)))
           (< (pseudo-term-count
               (pseudo-lambda->body (pseudo-term-call->fn term)))
              (pseudo-term-count term)))
  :expand ((pseudo-term-count term))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to a more general library:

(defun list-lenp-fn (n l)
  (if (zp n)
      `(endp ,l)
    `(and (consp ,l)
          ,(list-lenp-fn (1- n) `(cdr ,l)))))

(defmacro list-lenp (n l)
  (declare (xargs :guard (natp n)))
  `(let ((l ,l)) ,(list-lenp-fn n 'l)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to a more general library:

; (these serve to speed up some proofs in this file)

(defrulel tuplep-of-2-of-list
  (std::tuplep 2 (list x1 x2)))

(defrulel tuplep-of-3-of-list
  (std::tuplep 3 (list x1 x2 x3)))

(defrulel tuplep-of-4-of-list
  (std::tuplep 4 (list x1 x2 x3 x4)))

(defrulel tuplep-of-5-of-list
  (std::tuplep 5 (list x1 x2 x3 x4 x5)))

(defrulel tuplep-of-6-of-list
  (std::tuplep 6 (list x1 x2 x3 x4 x5 x6)))

(local (in-theory (disable std::tuplep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-event-and-code-generation
  :parents (atc-implementation)
  :short "Event generation and code generation performed by @(tsee atc)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate C abstract syntax,
     which we pretty-print to a file
     and also assign to a named constant.")
   (xdoc::p
    "Given the restrictions on the target functions,
     the translation is relatively straightforward, by design.")
   (xdoc::p
    "Some events are generated in two slightly different variants:
     one that is local to the generated @(tsee encapsulate),
     and one that is exported from the  @(tsee encapsulate).
     Proof hints are in the former but not in the latter,
     thus keeping the ACL2 history ``clean'';
     some proof hints may refer to events
     that are generated only locally to the @(tsee encapsulate).")
   (xdoc::p
    "Some code and event generation functions
     group some of their inputs and some of their outputs
     into @(tsee fty::defprod) values,
     to make the code more readable and more easily extensible,
     at a performance cost that should be unimportant.
     These product fixtypes have names @('...-gin') and @('...-gout'),
     where @('...') is derived from the corresponding function name,
     and where the @('g') in @('gin') and @('gout')
     conveys the reference to code and event generation functions.
     See the code generation functions documentation
     for a description of the components of these fixtypes;
     also note that some components follow the naming conventions
     described in @(see atc-implementation)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-appconds ((targets symbol-listp) (wrld plist-worldp))
  :returns (mv (appconds evmac-appcond-listp)
               (fn-appconds symbol-symbol-alistp :hyp (symbol-listp targets)))
  :short "Generate the applicability conditions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Also return an alist from the recursive target functions
     to the corresponding applicability condition names.")
   (xdoc::p
    "We skip over
     @(tsee defstruct) names,
     @(tsee defobject) names,
     and non-recursive function names."))
  (b* (((when (endp targets)) (mv nil nil))
       (target (car targets))
       ((when (not (function-symbolp target wrld)))
        (atc-gen-appconds (cdr targets) wrld))
       ((when (not (irecursivep+ target wrld)))
        (atc-gen-appconds (cdr targets) wrld))
       (meas (measure+ target wrld))
       (name (packn-pos (list 'natp-of-measure-of- target) :keyword))
       (formula `(natp ,meas))
       (appcond (make-evmac-appcond :name name :formula formula))
       ((mv appconds fn-appconds) (atc-gen-appconds (cdr targets) wrld)))
    (mv (cons appcond appconds)
        (acons target name fn-appconds)))
  :verify-guards nil ; done below
  ///
  (verify-guards atc-gen-appconds
    :hints
    (("Goal"
      :in-theory (enable acl2::alistp-when-symbol-symbol-alistp-rewrite)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-type-to-recognizer ((type typep) (wrld plist-worldp))
  :returns (recognizer symbolp)
  :short "ACL2 recognizer corresponding to a C type."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a supported integer type,
     the predicate is the recognizer of values of that type.
     For a structure type,
     the predicate is the recognizer of structures of that type.
     For a pointer to integer type,
     the predicate is the recognizer of arrays with that element type.
     For a pointer to structure type,
     the predicate is the recognizer of structures of that type.")
   (xdoc::p
    "This is based on our current ACL2 representation of C types,
     which may be extended in the future.
     Note that, in the current representation,
     the predicate corresponding to each type
     is never a recognizer of pointer values."))
  (type-case
   type
   :void (raise "Internal error: type ~x0." type)
   :char (raise "Internal error: type ~x0." type)
   :schar 'scharp
   :uchar 'ucharp
   :sshort 'sshortp
   :ushort 'ushortp
   :sint 'sintp
   :uint 'uintp
   :slong 'slongp
   :ulong 'ulongp
   :sllong 'sllongp
   :ullong 'ullongp
   :struct (b* ((info (defstruct-table-lookup (ident->name type.tag) wrld))
                ((unless info)
                 (raise "Internal error: no recognizer for ~x0." type)))
             (defstruct-info->recognizer info))
   :pointer (type-case
             type.to
             :void (raise "Internal error: type ~x0." type)
             :char (raise "Internal error: type ~x0." type)
             :schar 'schar-arrayp
             :uchar 'uchar-arrayp
             :sshort 'sshort-arrayp
             :ushort 'ushort-arrayp
             :sint 'sint-arrayp
             :uint 'uint-arrayp
             :slong 'slong-arrayp
             :ulong 'ulong-arrayp
             :sllong 'sllong-arrayp
             :ullong 'ullong-arrayp
             :struct (b* ((info (defstruct-table-lookup
                                  (ident->name type.to.tag)
                                  wrld))
                          ((unless info)
                           (raise "Internal error: no recognizer for ~x0."
                                  type)))
                       (defstruct-info->recognizer info))
             :pointer (raise "Internal error: type ~x0." type)
             :array (raise "Internal error: type ~x0." type))
   :array (raise "Internal error: type ~x0." type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod pexpr-gin
  :short "Inputs for @(tsee atc-gen-expr-pure)."
  ((inscope atc-symbol-type-alist-list)
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
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred pexpr-goutp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bexpr-gin
  :short "Inputs for @(tsee atc-gen-expr-bool)."
  ((inscope atc-symbol-type-alist-list)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-const-correct-thm ((fn symbolp)
                                        (term pseudo-termp)
                                        (expr exprp)
                                        (thm-index posp)
                                        (names-to-avoid symbol-listp)
                                        state)
  :returns (mv (event pseudo-event-formp)
               (name symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate a correctness theorem for the execution of
          a constant expression."
  (b* ((name (pack fn '-expr thm-index '-correct))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name nil names-to-avoid (w state)))
       (formula `(equal (exec-expr-pure ',expr compst)
                        ,term))
       (formula (untranslate$ formula nil state))
       (hints `(("Goal" :in-theory '(exec-expr-pure-when-const
                                     (:e expr-kind)
                                     (:e expr-const->get)
                                     exec-const-to-sint
                                     exec-const-to-uint
                                     exec-const-to-slong
                                     exec-const-to-ulong
                                     exec-const-to-sllong
                                     exec-const-to-ullong
                                     (:e const-kind)
                                     (:e const-int->get)
                                     (:e iconst->unsignedp)
                                     (:e iconst->length)
                                     (:e iconst->value)
                                     (:e iconst->base)
                                     (:e iconst-length-kind)
                                     (:e iconst-base-kind)
                                     (:e sint-integerp)
                                     (:e uint-integerp)
                                     (:e slong-integerp)
                                     (:e ulong-integerp)
                                     (:e sllong-integerp)
                                     (:e ullong-integerp)
                                     sint-dec-const
                                     sint-oct-const
                                     sint-hex-const
                                     uint-dec-const
                                     uint-oct-const
                                     uint-hex-const
                                     slong-dec-const
                                     slong-oct-const
                                     slong-hex-const
                                     ulong-dec-const
                                     ulong-oct-const
                                     ulong-hex-const
                                     sllong-dec-const
                                     sllong-oct-const
                                     sllong-hex-const
                                     ullong-dec-const
                                     ullong-oct-const
                                     ullong-hex-const))))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (mv event name names-to-avoid)))

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
                             (ctx ctxp)
                             state)
    :returns (mv erp (val pexpr-goutp) state)
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
    (b* (((acl2::fun (irr)) (ec-call (pexpr-gout-fix :irrelevant)))
         ((pexpr-gin gin) gin)
         ((when (pseudo-term-case term :var))
          (b* ((var (pseudo-term-var->name term))
               (type (atc-get-var var gin.inscope))
               ((when (not type))
                (raise "Internal error: the variable ~x0 in function ~x1 ~
                        has no associated type." var gin.fn)
                (acl2::value (irr))))
            (acl2::value
             (make-pexpr-gout
              :expr (expr-ident (make-ident :name (symbol-name var)))
              :type type
              :events nil
              :thm-index gin.thm-index
              :names-to-avoid gin.names-to-avoid
              :proofs nil))))
         ((er (list okp const out-type) :iferr (irr))
          (atc-check-iconst term ctx state))
         ((when okp)
          (b* ((expr (expr-const (const-int const)))
               ((mv event & names-to-avoid)
                (atc-gen-expr-const-correct-thm gin.fn
                                                term
                                                expr
                                                gin.thm-index
                                                gin.names-to-avoid
                                                state)))
            (acl2::value
             (make-pexpr-gout :expr expr
                              :type out-type
                              :events (list event)
                              :thm-index (1+ gin.thm-index)
                              :names-to-avoid names-to-avoid
                              :proofs nil))))
         ((mv okp op arg-term in-type out-type) (atc-check-unop term))
         ((when okp)
          (b* (((er (pexpr-gout arg))
                (atc-gen-expr-pure arg-term gin ctx state))
               ((unless (equal arg.type in-type))
                (er-soft+ ctx t (irr)
                          "The unary operator ~x0 is applied ~
                           to an expression term ~x1 returning ~x2, ~
                           but a ~x3 operand is expected. ~
                           This is indicative of provably dead code, ~
                           given that the code is guard-verified."
                          op arg-term arg.type in-type)))
            (acl2::value (make-pexpr-gout
                          :expr (make-expr-unary :op op
                                                 :arg arg.expr)
                          :type out-type
                          :events arg.events
                          :thm-index arg.thm-index
                          :names-to-avoid arg.names-to-avoid
                          :proofs nil))))
         ((mv okp op arg1-term arg2-term in-type1 in-type2 out-type)
          (atc-check-binop term))
         ((when okp)
          (b* (((er (pexpr-gout arg1))
                (atc-gen-expr-pure arg1-term gin ctx state))
               ((er (pexpr-gout arg2))
                (atc-gen-expr-pure arg2-term
                                   (change-pexpr-gin
                                    gin
                                    :thm-index arg1.thm-index
                                    :names-to-avoid arg1.names-to-avoid)
                                   ctx
                                   state))
               ((unless (and (equal arg1.type in-type1)
                             (equal arg2.type in-type2)))
                (er-soft+ ctx t (irr)
                          "The binary operator ~x0 is applied ~
                           to an expression term ~x1 returning ~x2 ~
                           and to an expression term ~x3 returning ~x4, ~
                           but a ~x5 and a ~x6 operand is expected. ~
                           This is indicative of provably dead code, ~
                           given that the code is guard-verified."
                          op arg1-term arg1.type arg2-term arg2.type
                          in-type1 in-type2)))
            (acl2::value (make-pexpr-gout
                          :expr (make-expr-binary :op op
                                                  :arg1 arg1.expr
                                                  :arg2 arg2.expr)
                          :type out-type
                          :events (append arg1.events arg2.events)
                          :thm-index arg2.thm-index
                          :names-to-avoid arg2.names-to-avoid
                          :proofs nil))))
         ((mv okp tyname arg-term in-type out-type) (atc-check-conv term))
         ((when okp)
          (b* (((er (pexpr-gout arg))
                (atc-gen-expr-pure arg-term gin ctx state))
               ((unless (equal arg.type in-type))
                (er-soft+ ctx t (irr)
                          "The conversion from ~x0 to ~x1 is applied ~
                           to an expression term ~x2 returning ~x3, ~
                           but a ~x0 operand is expected. ~
                           This is indicative of provably dead code, ~
                           given that the code is guard-verified."
                          in-type out-type arg-term arg.type)))
            (acl2::value (make-pexpr-gout
                          :expr (make-expr-cast :type tyname
                                                :arg arg.expr)
                          :type out-type
                          :events arg.events
                          :thm-index arg.thm-index
                          :names-to-avoid arg.names-to-avoid
                          :proofs nil))))
         ((mv okp arr-term sub-term in-type1 in-type2 out-type)
          (atc-check-array-read term))
         ((when okp)
          (b* (((er (pexpr-gout arr))
                (atc-gen-expr-pure arr-term gin ctx state))
               ((er (pexpr-gout sub))
                (atc-gen-expr-pure sub-term
                                   (change-pexpr-gin
                                    gin
                                    :thm-index arr.thm-index
                                    :names-to-avoid arr.names-to-avoid)
                                   ctx
                                   state))
               ((unless (and (equal arr.type in-type1)
                             (equal sub.type in-type2)))
                (er-soft+ ctx t (irr)
                          "The reading of a ~x0 array with a ~x1 index ~
                           is applied to ~
                           an expression term ~x2 returning ~x3 ~
                           and to an expression term ~x4 returning ~x5, ~
                           but a ~x0 and a ~x1 operand is expected. ~
                           This is indicative of provably dead code, ~
                           given that the code is guard-verified."
                          in-type1 in-type2
                          arr-term arr.type sub-term sub.type)))
            (acl2::value (make-pexpr-gout
                          :expr (make-expr-arrsub :arr arr.expr
                                                  :sub sub.expr)
                          :type out-type
                          :events (append arr.events sub.events)
                          :thm-index sub.thm-index
                          :names-to-avoid sub.names-to-avoid
                          :proofs nil))))
         ((mv okp arg-term tag member mem-type)
          (atc-check-struct-read-scalar term gin.prec-tags))
         ((when okp)
          (b* (((er (pexpr-gout arg))
                (atc-gen-expr-pure arg-term gin ctx state)))
            (cond ((equal arg.type (type-struct tag))
                   (acl2::value (make-pexpr-gout
                                 :expr (make-expr-member :target arg.expr
                                                         :name member)
                                 :type mem-type
                                 :events arg.events
                                 :thm-index arg.thm-index
                                 :names-to-avoid arg.names-to-avoid
                                 :proofs nil)))
                  ((equal arg.type (type-pointer (type-struct tag)))
                   (acl2::value (make-pexpr-gout
                                 :expr (make-expr-memberp :target arg.expr
                                                          :name member)
                                 :type mem-type
                                 :events arg.events
                                 :thm-index arg.thm-index
                                 :names-to-avoid arg.names-to-avoid
                                 :proofs nil)))
                  (t (er-soft+ ctx t (irr)
                               "The reading of a ~x0 structure with member ~x1 ~
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
                               (type-pointer (type-struct tag)))))))
         ((mv okp index-term struct-term tag member index-type elem-type)
          (atc-check-struct-read-array term gin.prec-tags))
         ((when okp)
          (b* (((er (pexpr-gout index))
                (atc-gen-expr-pure index-term gin ctx state))
               ((unless (equal index.type index-type))
                (er-soft+ ctx t (irr)
                          "The reading of ~x0 structure with member ~x1 ~
                           is applied to ~
                           an expression term ~x2 returning ~x3, ~
                           but a ~x4 operand is expected. ~
                           This is indicative of provably dead code, ~
                           given that the code is guard-verified."
                          (type-struct tag)
                          member
                          index-term
                          index.type
                          index-type))
               ((er (pexpr-gout struct))
                (atc-gen-expr-pure struct-term
                                   (change-pexpr-gin
                                    gin
                                    :thm-index index.thm-index
                                    :names-to-avoid index.names-to-avoid)
                                   ctx
                                   state)))
            (cond ((equal struct.type (type-struct tag))
                   (acl2::value (make-pexpr-gout
                                 :expr (make-expr-arrsub
                                        :arr (make-expr-member
                                              :target struct.expr
                                              :name member)
                                        :sub index.expr)
                                 :type elem-type
                                 :events (append index.events struct.events)
                                 :thm-index struct.thm-index
                                 :names-to-avoid struct.names-to-avoid
                                 :proofs nil)))
                  ((equal struct.type (type-pointer (type-struct tag)))
                   (acl2::value (make-pexpr-gout
                                 :expr (make-expr-arrsub
                                        :arr (make-expr-memberp
                                              :target struct.expr
                                              :name member)
                                        :sub index.expr)
                                 :type elem-type
                                 :events (append index.events struct.events)
                                 :thm-index struct.thm-index
                                 :names-to-avoid struct.names-to-avoid
                                 :proofs nil)))
                  (t (er-soft+ ctx t (irr)
                               "The reading of ~x0 structure with member ~x1 ~
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
                               (type-pointer (type-struct tag)))))))
         ((mv okp arg-term) (atc-check-sint-from-boolean term))
         ((when okp)
          (b* (((er (bexpr-gout arg) :iferr (irr))
                (atc-gen-expr-bool arg-term
                                   (make-bexpr-gin
                                    :inscope gin.inscope
                                    :prec-tags gin.prec-tags
                                    :fn gin.fn
                                    :thm-index gin.thm-index
                                    :names-to-avoid gin.names-to-avoid
                                    :proofs nil)
                                   ctx
                                   state)))
            (acl2::value (make-pexpr-gout :expr arg.expr
                                          :type (type-sint)
                                          :events arg.events
                                          :thm-index arg.thm-index
                                          :names-to-avoid arg.names-to-avoid
                                          :proofs nil))))
         ((mv okp test-term then-term else-term) (atc-check-condexpr term))
         ((when okp)
          (b* (((er (bexpr-gout test) :iferr (irr))
                (atc-gen-expr-bool test-term
                                   (make-bexpr-gin
                                    :inscope gin.inscope
                                    :prec-tags gin.prec-tags
                                    :fn gin.fn
                                    :thm-index gin.thm-index
                                    :names-to-avoid gin.names-to-avoid
                                    :proofs nil)
                                   ctx
                                   state))
               ((er (pexpr-gout then))
                (atc-gen-expr-pure then-term
                                   (change-pexpr-gin
                                    gin
                                    :thm-index test.thm-index
                                    :names-to-avoid test.names-to-avoid)
                                   ctx
                                   state))
               ((er (pexpr-gout else))
                (atc-gen-expr-pure else-term
                                   (change-pexpr-gin
                                    gin
                                    :thm-index then.thm-index
                                    :names-to-avoid then.names-to-avoid)
                                   ctx
                                   state))
               ((unless (equal then.type else.type))
                (er-soft+ ctx t (irr)
                          "When generating C code for the function ~x0, ~
                           two branches ~x1 and ~x2 of a conditional term ~
                           have different types ~x3 and ~x4; ~
                           use conversion operations, if needed, ~
                           to make the branches of the same type."
                          gin.fn then-term else-term then.type else.type)))
            (acl2::value
             (make-pexpr-gout
              :expr (make-expr-cond :test test.expr
                                    :then then.expr
                                    :else else.expr)
              :type then.type
              :events (append test.events then.events else.events)
              :thm-index else.thm-index
              :names-to-avoid else.names-to-avoid
              :proofs nil)))))
      (er-soft+ ctx t (irr)
                "When generating C code for the function ~x0, ~
                 at a point where ~
                 a pure expression term returning a C type is expected, ~
                 the term ~x1 is encountered instead."
                gin.fn term))
    :measure (pseudo-term-count term))

  (define atc-gen-expr-bool ((term pseudo-termp)
                             (gin bexpr-ginp)
                             (ctx ctxp)
                             state)
    :returns (mv erp (val bexpr-goutp) state)
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
    (b* (((acl2::fun (irr)) (ec-call (bexpr-gout-fix :irrelevant)))
         ((bexpr-gin gin) gin)
         ((mv okp arg-term) (fty-check-not-call term))
         ((when okp)
          (b* (((er (bexpr-gout arg))
                (atc-gen-expr-bool arg-term gin ctx state)))
            (acl2::value (make-bexpr-gout
                          :expr (make-expr-unary :op (unop-lognot)
                                                 :arg arg.expr)
                          :events arg.events
                          :thm-index arg.thm-index
                          :names-to-avoid arg.names-to-avoid
                          :proofs nil))))
         ((mv okp arg1-term arg2-term) (fty-check-and-call term))
         ((when okp)
          (b* (((er (bexpr-gout arg1))
                (atc-gen-expr-bool arg1-term gin ctx state))
               ((er (bexpr-gout arg2))
                (atc-gen-expr-bool arg2-term
                                   (change-bexpr-gin
                                    gin
                                    :thm-index arg1.thm-index
                                    :names-to-avoid arg1.names-to-avoid)
                                   ctx
                                   state)))
            (acl2::value (make-bexpr-gout
                          :expr (make-expr-binary :op (binop-logand)
                                                  :arg1 arg1.expr
                                                  :arg2 arg2.expr)
                          :events (append arg1.events arg2.events)
                          :thm-index arg2.thm-index
                          :names-to-avoid arg2.names-to-avoid
                          :proofs nil))))
         ((mv okp arg1-term arg2-term) (fty-check-or-call term))
         ((when okp)
          (b* (((er (bexpr-gout arg1))
                (atc-gen-expr-bool arg1-term gin ctx state))
               ((er (bexpr-gout arg2))
                (atc-gen-expr-bool arg2-term
                                   (change-bexpr-gin
                                    gin
                                    :thm-index arg1.thm-index
                                    :names-to-avoid arg1.names-to-avoid)
                                   ctx
                                   state)))
            (acl2::value (make-bexpr-gout
                          :expr (make-expr-binary :op (binop-logor)
                                                  :arg1 arg1.expr
                                                  :arg2 arg2.expr)
                          :events (append arg1.events arg2.events)
                          :thm-index arg2.thm-index
                          :names-to-avoid arg2.names-to-avoid
                          :proofs nil))))
         ((mv okp arg-term in-type) (atc-check-boolean-from-type term))
         ((when okp)
          (b* (((er (pexpr-gout arg) :iferr (irr))
                (atc-gen-expr-pure arg-term
                                   (make-pexpr-gin
                                    :inscope gin.inscope
                                    :prec-tags gin.prec-tags
                                    :fn gin.fn
                                    :thm-index gin.thm-index
                                    :names-to-avoid gin.names-to-avoid
                                    :proofs nil)
                                   ctx
                                   state))
               ((unless (equal arg.type in-type))
                (er-soft+ ctx t (irr)
                          "The conversion from ~x0 to boolean is applied to ~
                           an expression term ~x1 returning ~x2, ~
                           but a ~x0 operand is expected. ~
                           This is indicative of provably dead code, ~
                           given that the code is guard-verified."
                          in-type arg-term arg.type)))
            (acl2::value
             (make-bexpr-gout :expr arg.expr
                              :events arg.events
                              :thm-index arg.thm-index
                              :names-to-avoid arg.names-to-avoid
                              :proofs nil)))))
      (er-soft+ ctx t (irr)
                "When generating C code for the function ~x0, ~
                 at a point where ~
                 an expression term returning boolean is expected, ~
                 the term ~x1 is encountered instead."
                gin.fn term))
    :measure (pseudo-term-count term))

  :verify-guards nil ; done below
  ///
  (verify-guards atc-gen-expr-pure))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod pexprs-gin
  :short "Inputs for @(tsee atc-gen-expr-pure-list)."
  ((inscope atc-symbol-type-alist-list)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-pure-list ((terms pseudo-term-listp)
                                (gin pexprs-ginp)
                                (ctx ctxp)
                                state)
  :returns (mv erp (val pexprs-goutp) state)
  :short "Generate a list of C expressions from a list of ACL2 terms
          that must be pure expression terms returning C values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee atc-gen-expr-pure) to lists.
     However, we do not return the C types of the expressions."))
  (b* (((acl2::fun (irr)) (ec-call (pexprs-gout-fix :irrelevant)))
       ((pexprs-gin gin) gin)
       ((when (endp terms))
        (acl2::value (make-pexprs-gout :exprs nil
                                       :types nil
                                       :events nil
                                       :thm-index gin.thm-index
                                       :names-to-avoid gin.names-to-avoid
                                       :proofs nil)))
       ((er (pexpr-gout first) :iferr (irr))
        (atc-gen-expr-pure (car terms)
                           (make-pexpr-gin
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :thm-index gin.thm-index
                            :names-to-avoid gin.names-to-avoid
                            :proofs nil)
                           ctx
                           state))
       ((er (pexprs-gout rest))
        (atc-gen-expr-pure-list (cdr terms)
                                (change-pexprs-gin
                                 gin
                                 :thm-index first.thm-index
                                 :names-to-avoid first.names-to-avoid)
                                ctx
                                state)))
    (acl2::value (make-pexprs-gout
                  :exprs (cons first.expr rest.exprs)
                  :types (cons first.type rest.types)
                  :events (append first.events rest.events)
                  :thm-index rest.thm-index
                  :names-to-avoid rest.names-to-avoid
                  :proofs nil)))
  :verify-guards nil ; done below
  ///
  (verify-guards atc-gen-expr-pure-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-gin
  :short "Inputs for @(tsee atc-gen-expr)."
  ((var-term-alist acl2::symbol-pseudoterm-alist)
   (inscope atc-symbol-type-alist-list)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr ((term pseudo-termp)
                      (gin expr-ginp)
                      (ctx ctxp)
                      state)
  :returns (mv erp (val expr-goutp) state)
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
  (b* (((acl2::fun (irr)) (ec-call (expr-gout-fix :irrelevant)))
       ((expr-gin gin) gin)
       ((mv okp called-fn arg-terms in-types out-type affect limit)
        (atc-check-cfun-call term gin.var-term-alist gin.prec-fns (w state)))
       ((when okp)
        (b* (((when (type-case out-type :void))
              (er-soft+ ctx t (irr)
                        "A call ~x0 of the function ~x1, which returns void, ~
                         is being used where ~
                         an expression term returning a a non-void C type ~
                         is expected."
                        term called-fn))
             ((unless (atc-check-cfun-call-args (formals+ called-fn (w state))
                                                in-types
                                                arg-terms))
              (er-soft+ ctx t (irr)
                        "The call ~x0 does not satisfy the restrictions ~
                         on array arguments being identical to the formals."
                        term))
             ((er (pexprs-gout args) :iferr (irr))
              (atc-gen-expr-pure-list arg-terms
                                      (make-pexprs-gin
                                       :inscope gin.inscope
                                       :prec-tags gin.prec-tags
                                       :fn gin.fn
                                       :thm-index gin.thm-index
                                       :names-to-avoid gin.names-to-avoid
                                       :proofs nil)
                                      ctx
                                      state))
             ((unless (equal args.types in-types))
              (er-soft+ ctx t (irr)
                        "The function ~x0 with input types ~x1 ~
                         is applied to expression terms ~x2 returning ~x3. ~
                         This is indicative of provably dead code, ~
                         given that the code is guard-verified."
                        called-fn in-types arg-terms args.types)))
          (acl2::value
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
            :proofs nil)))))
    (b* (((er (pexpr-gout pure) :iferr (irr))
          (atc-gen-expr-pure term
                             (make-pexpr-gin :inscope gin.inscope
                                             :prec-tags gin.prec-tags
                                             :fn gin.fn
                                             :thm-index gin.thm-index
                                             :names-to-avoid gin.names-to-avoid
                                             :proofs nil)
                             ctx
                             state)))
      (acl2::value (make-expr-gout :expr pure.expr
                                   :type pure.type
                                   :affect affect
                                   :limit '(quote 1)
                                   :events pure.events
                                   :thm-index pure.thm-index
                                   :names-to-avoid pure.names-to-avoid
                                   :proofs nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-var-assignablep ((var symbolp)
                             (innermostp booleanp)
                             (affect symbol-listp))
  :returns (yes/no booleanp :hyp (booleanp innermostp))
  :short "Check if a variable is assignable,
          based on whether it is in the innermost scope
          and based on the variables being currently affected."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variable may be destructively assigned to
     if any of the following conditions apply:
     (i) it is declared in the innermost scope,
     because in that case it cannot be accessed after exiting the scope;
     (ii) it is being affected,
     because in that case its modified value is returned
     and used in subsequent code;
     (iii) no variable is being affected,
     because in that case there is no subsequent code."))
  (or innermostp
      (and (member-eq var affect) t)
      (null affect)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-vars-assignablep ((var-list symbol-listp)
                              (innermostp-list boolean-listp)
                              (affect symbol-listp))
  :guard (equal (len var-list) (len innermostp-list))
  :returns (yes/no booleanp :hyp (boolean-listp innermostp-list))
  :short "Lift @(tsee atc-var-assignablep) to lists."
  (or (endp var-list)
      (and
       (atc-var-assignablep (car var-list) (car innermostp-list) affect)
       (atc-vars-assignablep (cdr var-list) (cdr innermostp-list) affect))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-affecting-term-for-let-p ((term pseudo-termp)
                                      (prec-fns atc-symbol-fninfo-alistp))
  :returns (yes/no booleanp)
  :short "Check if a term @('term') has the basic structure
          required for representing code affecting variables
          in @('(let ((var term)) body)')
          or @('(mv-let (var1 ... varn) term body)')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is explained in the user documentation.
     Here we perform a shallow check,
     because we examine the term in full detail
     when recursively generating C code from it.
     In essence, here we check that the term is either
     (i) an @(tsee if) whose test is not @(tsee mbt) or @(tsee mbt$) or
     (ii) a call of a (preceding) target function."))
  (case-match term
    (('if test . &) (and (case-match test
                           ((fn . &) (not (member-eq fn '(mbt mbt$))))
                           (& t))))
    ((fn . &) (and (symbolp fn)
                   (consp (assoc-eq fn prec-fns))))
    (& nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-make-mv-nth-terms ((indices nat-listp) (term pseudo-termp))
  :returns (terms pseudo-term-listp)
  :short "Create a list of @(tsee mv-nth)s applied to a term
          for a list of indices."
  (cond ((endp indices) nil)
        (t (cons `(mv-nth ',(car indices) ,(pseudo-term-fix term))
                 (atc-make-mv-nth-terms (cdr indices) term))))
  ///
  (defret len-of-atc-make-mv-nth-terms
    (equal (len terms)
           (len indices))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-update-var-term-alist ((vars symbol-listp)
                                   (terms pseudo-term-listp)
                                   (alist symbol-pseudoterm-alistp))
  :returns (new-alist symbol-pseudoterm-alistp)
  :short "Update an alist from symbols to terms."
  (append (pairlis$ (symbol-list-fix vars)
                    (pseudo-term-list-fix terms))
          (symbol-pseudoterm-alist-fix alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-ensure-formals-not-lost ((bind-affect symbol-listp)
                                     (fn-affect symbol-listp)
                                     (fn-typed-formals atc-symbol-type-alistp)
                                     (fn symbolp)
                                     (ctx ctxp)
                                     state)
  :returns (mv erp
               (nothing null)
               state)
  :short "Ensure that no affected formals are lost."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the body of a non-recursive function @('fn')
     includes an @(tsee mv-let)s or a @(tsee let)
     that affects a formal of @('fn') of pointer type,
     that formal must be among the variables affected by ('fn').
     If the body of a recursive function @('fn')
     includes an @(tsee mv-let)s or a @(tsee let)
     that affects a formal of @('fn') of any type,
     that formal must be among the variables affected by ('fn').
     In other words, no modification of formals must be ``lost''.
     The case of formals of pointer types is clear,
     because it means that objects in the heap are affected.
     The case of formals of non-pointer types
     applies to recursive functions
     because they represent loops,
     which may affect local variables in the function where they appear.")
   (xdoc::p
    "This ACL2 function ensures that no formals are lost in the sense above.
     The parameter @('bind-affect') consists of
     the variable affected by the @(tsee mv-let) or @(tsee let).
     The parameter @('fn-affect') consists of
     the variables purported to be affected by @('fn').
     We go through the elements of @('bind-affect')
     and check each one against the formals of @('fn'),
     taking into account the types and whether @('fn') is recursive."))
  (b* (((when (endp bind-affect)) (acl2::value nil))
       (var (car bind-affect))
       (type (cdr (assoc-eq var fn-typed-formals)))
       ((when (and type
                   (or (irecursivep+ fn (w state))
                       (type-case type :pointer))
                   (not (member-eq var fn-affect))))
        (er-soft+ ctx t nil
                  "When generating C code for the function ~x0, ~
                   the formal parameter ~x1 is being affected ~
                   in an MV-LET or LET term, ~
                   but it is not being returned by ~x0."
                  fn var)))
    (atc-ensure-formals-not-lost
     (cdr bind-affect) fn-affect fn-typed-formals fn ctx state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-guard-conjunct ((conjunct pseudo-termp)
                                  (prec-tags atc-string-taginfo-alistp)
                                  (prec-objs atc-string-objinfo-alistp))
  :returns (mv (type type-optionp) (arg symbolp))
  :short "C type and argument derived from a guard conjunct, if any."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to determine the types of the formal parameters of functions
     from the conjuncts used in the guard,
     as explained in the user documentation.")
   (xdoc::p
    "The conjunct must have the form
     @('(recognizer var)') or @('(pointer (recognizer var))'),
     where @('recognizer') is a recognizer of a C type
     and @('var') is a variable.
     If the recognizer is a known one for integer or integer array types,
     the @(tsee pointer) wrapper is disallowed,
     and the integer type is readily determined.
     Otherwise, there may be two possibilities.
     One is that the recognizer is the one of a @(tsee defstruct),
     of the form @('struct-<tag>-p'):
     in this case, the type is the structure type or a pointer type to it,
     depending on the absence or presence of the @(tsee pointer) wrapper.
     The other possibility is that
     the recognizer is the one of a @(tsee defobject),
     of the form @('object-<name>-p'):
     in this case, the @(tsee pointer) wrapper is disallowed,
     and the type is a pointer to the integer type
     that is the element type of the array type of the object.")
   (xdoc::p
    "If the recognizer does not have any of the above forms,
     we return @('nil') as both results.
     If the argument is not a variable,
     we also return @('nil') as both results."))
  (b* (((when (or (variablep conjunct)
                  (fquotep conjunct)
                  (flambda-applicationp conjunct)))
        (mv nil nil))
       (fn (ffn-symb conjunct))
       (arg (fargn conjunct 1))
       ((mv okp pointerp fn arg)
        (if (eq fn 'pointer)
            (if (or (variablep arg)
                    (fquotep arg)
                    (flambda-applicationp arg))
                (mv nil nil nil nil)
              (mv t t (ffn-symb arg) (fargn arg 1)))
          (mv t nil fn arg)))
       ((when (not okp)) (mv nil nil))
       ((unless (symbolp arg)) (mv nil nil))
       (type
        (b* (((when (eq fn 'scharp)) (type-schar))
             ((when (eq fn 'ucharp)) (type-uchar))
             ((when (eq fn 'sshortp)) (type-sshort))
             ((when (eq fn 'ushortp)) (type-ushort))
             ((when (eq fn 'sintp)) (type-sint))
             ((when (eq fn 'uintp)) (type-uint))
             ((when (eq fn 'slongp)) (type-slong))
             ((when (eq fn 'ulongp)) (type-ulong))
             ((when (eq fn 'sllongp)) (type-sllong))
             ((when (eq fn 'ullongp)) (type-ullong))
             ((when (eq fn 'schar-arrayp)) (type-pointer (type-schar)))
             ((when (eq fn 'uchar-arrayp)) (type-pointer (type-uchar)))
             ((when (eq fn 'sshort-arrayp)) (type-pointer (type-sshort)))
             ((when (eq fn 'ushort-arrayp)) (type-pointer (type-ushort)))
             ((when (eq fn 'sint-arrayp)) (type-pointer (type-sint)))
             ((when (eq fn 'uint-arrayp)) (type-pointer (type-uint)))
             ((when (eq fn 'slong-arrayp)) (type-pointer (type-slong)))
             ((when (eq fn 'ulong-arrayp)) (type-pointer (type-ulong)))
             ((when (eq fn 'sllong-arrayp)) (type-pointer (type-sllong)))
             ((when (eq fn 'ullong-arrayp)) (type-pointer (type-ullong)))
             ((mv okp struct/object tag/name p) (atc-check-symbol-3part fn))
             ((unless (and okp
                           (equal (symbol-name p) "P")))
              nil)
             ((when (equal (symbol-name struct/object) "STRUCT"))
              (b* ((tag (symbol-name tag/name))
                   (info (cdr (assoc-equal tag prec-tags)))
                   ((unless info) nil)
                   ((unless (atc-tag-infop info))
                    (raise "Internal error: malformed ATC-TAG-INFO ~x0." info))
                   (info (atc-tag-info->defstruct info))
                   ((unless (eq fn (defstruct-info->recognizer info))) nil)
                   ((when (and (defstruct-info->flexiblep info)
                               (not pointerp)))
                    nil))
                (type-struct (defstruct-info->tag info))))
             ((when (equal (symbol-name struct/object) "OBJECT"))
              (b* ((name (symbol-name tag/name))
                   (info (cdr (assoc-equal name prec-objs)))
                   ((unless info) nil)
                   ((unless (atc-obj-infop info))
                    (raise "Internal error: malformed ATC-OBJ-INFO ~x0." info))
                   (info (atc-obj-info->defobject info))
                   ((unless (eq fn (defobject-info->recognizer info))) nil)
                   (arrtype (defobject-info->type info))
                   ((unless (type-case arrtype :array))
                    (raise "Internal error: object ~s0 has type ~x1."
                           name arrtype)))
                (type-pointer (type-array->of arrtype)))))
          nil))
       ((unless type) (mv nil nil))
       ((when (and pointerp
                   (not (type-case type :struct))))
        (mv nil nil))
       (type (if pointerp
                 (type-pointer type)
               type)))
    (mv type arg)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-typed-formals ((fn symbolp)
                           (prec-tags atc-string-taginfo-alistp)
                           (prec-objs atc-string-objinfo-alistp)
                           (ctx ctxp)
                           state)
  :returns (mv erp
               (typed-formals atc-symbol-type-alistp)
               state)
  :short "Calculate the C types of the formal parameters of a target function."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look for conjuncts from which we derive,
     according to @(tsee atc-check-guard-conjunct),
     types for the formals of @('fn').
     We ensure that there is exactly one such term for each formal.")
   (xdoc::p
    "If this is successful,
     we return an alist from the formals to their types.
     The alist has unique keys, in the order of the formals.")
   (xdoc::p
    "We first extract the guard's conjuncts,
     then we go through the conjuncts, looking for the pattern,
     and we extend an alist from formals to types as we find patterns;
     this preliminary alist may not have the keys in order,
     because it goes according to the order of the guard's conjuncts.
     As we construct this preliminary alist,
     we check for multiple terms for the same formal,
     rejecting them even if they are identical.
     Then we construct the final alist by going through the formals in order,
     and looking up their types in the preliminary alist;
     here we detect when a formal has no corresponding conjunct in the guard."))
  (b* ((wrld (w state))
       (formals (formals+ fn wrld))
       (guard (uguard+ fn wrld))
       (guard-conjuncts (flatten-ands-in-lit guard))
       ((er prelim-alist) (atc-typed-formals-prelim-alist fn
                                                          formals
                                                          guard
                                                          guard-conjuncts
                                                          nil
                                                          prec-tags
                                                          prec-objs
                                                          ctx
                                                          state)))
    (atc-typed-formals-final-alist fn formals guard prelim-alist ctx state))

  :prepwork

  ((define atc-typed-formals-prelim-alist ((fn symbolp)
                                           (formals symbol-listp)
                                           (guard pseudo-termp)
                                           (guard-conjuncts pseudo-term-listp)
                                           (prelim-alist atc-symbol-type-alistp)
                                           (prec-tags atc-string-taginfo-alistp)
                                           (prec-objs atc-string-objinfo-alistp)
                                           (ctx ctxp)
                                           state)
     :returns (mv erp
                  (prelim-alist-final atc-symbol-type-alistp)
                  state)
     :parents nil
     (b* (((when (endp guard-conjuncts))
           (acl2::value (atc-symbol-type-alist-fix prelim-alist)))
          (conjunct (car guard-conjuncts))
          ((mv type arg) (atc-check-guard-conjunct conjunct
                                                   prec-tags
                                                   prec-objs))
          ((unless type)
           (atc-typed-formals-prelim-alist fn
                                           formals
                                           guard
                                           (cdr guard-conjuncts)
                                           prelim-alist
                                           prec-tags
                                           prec-objs
                                           ctx
                                           state))
          ((unless (member-eq arg formals))
           (atc-typed-formals-prelim-alist fn
                                           formals
                                           guard
                                           (cdr guard-conjuncts)
                                           prelim-alist
                                           prec-tags
                                           prec-objs
                                           ctx
                                           state))
          ((when (consp (assoc-eq arg prelim-alist)))
           (er-soft+ ctx t nil
                     "The guard ~x0 of the target function ~x1 ~
                      includes multiple type predicates ~
                      for the formal parameter ~x2. ~
                      This is disallowed: every formal paramter ~
                      must have exactly one type predicate in the guard, ~
                      even when the multiple predicates are the same."
                     guard fn arg))
          (prelim-alist (acons arg type prelim-alist)))
       (atc-typed-formals-prelim-alist fn
                                       formals
                                       guard
                                       (cdr guard-conjuncts)
                                       prelim-alist
                                       prec-tags
                                       prec-objs
                                       ctx
                                       state)))

   (define atc-typed-formals-final-alist ((fn symbolp)
                                          (formals symbol-listp)
                                          (guard pseudo-termp)
                                          (prelim-alist atc-symbol-type-alistp)
                                          (ctx ctxp)
                                          state)
     :returns (mv erp
                  (typed-formals atc-symbol-type-alistp)
                  state)
     :parents nil
     (b* (((when (endp formals)) (acl2::value nil))
          (formal (symbol-fix (car formals)))
          (formal+type (assoc-eq formal
                                 (atc-symbol-type-alist-fix prelim-alist)))
          ((when (not (consp formal+type)))
           (er-soft+ ctx t nil
                     "The guard ~x0 of the target function ~x1 ~
                      has no type predicate for the formal parameter ~x2. ~
                      Every formal parameter must have a type predicate."
                     guard fn formal))
          (type (cdr formal+type))
          ((er typed-formals) (atc-typed-formals-final-alist fn
                                                             (cdr formals)
                                                             guard
                                                             prelim-alist
                                                             ctx
                                                             state)))
       (acl2::value (acons formal type typed-formals)))
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod stmt-gin
  :short "Inputs for @(tsee atc-gen-stmt)."
  ((var-term-alist symbol-pseudoterm-alistp)
   (inscope atc-symbol-type-alist-listp)
   (loop-flag booleanp)
   (affect symbol-listp)
   (fn symbolp)
   (prec-fns atc-symbol-fninfo-alistp)
   (prec-tags atc-string-taginfo-alistp)
   (prec-objs atc-string-objinfo-alistp)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred stmt-ginp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod stmt-gout
  :short "Outputs for @(tsee atc-gen-stmt)."
  ((items block-item-listp)
   (type typep)
   (limit pseudo-termp)
   (events pseudo-event-form-list)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred stmt-goutp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-stmt ((term pseudo-termp)
                      (gin stmt-ginp)
                      (ctx ctxp)
                      state)
  :returns (mv erp (val stmt-goutp) state)
  :short "Generate a C statement from an ACL2 term."
  :long
  (xdoc::topstring
   (xdoc::p
    "More precisely, we return a list of block items.
     These can be regarded as forming a compound statement,
     but lists of block items are compositional (via concatenation).")
   (xdoc::p
    "At the same time, we check that the term is a statement term,
     as described in the user documentation.")
   (xdoc::p
    "Along with the term, we pass an alist from symbols to terms
     that collects the @(tsee let) and @(tsee mv-let) bindings
     encountered along the way.
     These are eventually used to properly instantiate
     limits associated to function calls,
     because those limits apply to the functions' formals,
     which must therefore be replaced not just with the actuals of the call,
     but with those actuals with variables replaced with terms
     according to the bindings that lead to the call.")
   (xdoc::p
    "The @('loop-flag') input of this ACL2 function (see @(tsee stmt-gin))
     is the loop flag @('L') described in the user documentation.")
   (xdoc::p
    "The @('affect') input of this ACL2 function (see @(tsee stmt-gin))
     is the list of variables being affected by this statement.
     This is denoted @('vars') in the user documentation at @(tsee atc).")
   (xdoc::p
    "Besides the generated block items,
     we also return a C type, which is the one returned by the statement.
     This type may be @('void').")
   (xdoc::p
    "We also return a limit that suffices for @(tsee exec-block-item-list)
     to execute the returned block items completely.")
   (xdoc::p
    "We also return the correctness theorems for expressions
     generated for the expressions contained in the generated statement.")
   (xdoc::p
    "If the term is a conditional, there are two cases.
     If the test is @(tsee mbt) or @(tsee mbt$),
     we discard test and `else' branch
     and recursively translate the `then' branch;
     the limit is the same as the `then' branch.
     Otherwise, we generate an @('if') statement
     (as a singleton block item list),
     with recursively generated compound statements as branches;
     the test expression is generated from the test term;
     we ensure that the two branches have the same type.
     When we process the branches,
     we extend the symbol table with a new empty scope for each branch.
     The calculation of the limit result is a bit more complicated in this case:
     we need 1 to go from @(tsee exec-block-item-list)
     to @(tsee exec-block-item),
     another 1 to go from that to @(tsee exec-stmt),
     and another 1 to go to the @(':ifelse') case there;
     the test is pure and so it needs no addition to the limit;
     since either branch may be taken,
     we return the sum of the limits for the two branches.
     More precisely, the limit recursively returned for each branch
     pertains to the block item list in the branch,
     but those are put into a compound statement;
     thus, we need to increase the recursively calculated limit
     by 1 to go from @(tsee exec-block-item-list) to @(tsee exec-block-item),
     and another 1 to go from there to @(tsee exec-stmt).
     In principle we could return the maximum from the two branches
     instead of their sum,
     but we want the limits to be
     linear combinations of sub-limits,
     so that ACL2's linear arithmetic can handle the reasoning about limits
     during the generated proofs.")
   (xdoc::p
    "If the term is a @(tsee mv-let),
     there are three cases.
     If the term involves a @('declar<n>') wrapper,
     we ensure that a variable with
     the same symbol name as the first bound variable
     is not already in scope
     (i.e. in the symbol table)
     and that the name is a portable ASCII identifier;
     we generate a declaration for the variable,
     initialized with the expression obtained
     from the term that the variable is bound to,
     which also determines the type of the variable,
     and which must affect the bound variables except the first one;
     the type must not be a pointer type (code generation fails if it is);
     we also ensure that the other variables are assignable.
     Otherwise, if the term involves an @('assign<n>') wrapper,
     we ensure that the first bound variable is assignable,
     which implies that it must be in scope,
     and we also ensure that it has the same type as the one in scope;
     we generate an assignment whose right-hand side is
     obtained from the unwrapped term,
     which must be an expression term returning a C value
     that affects the bound variables except the first one;
     we also ensure that the other variables are assignable.
     Otherwise, if the term involves no wrapper,
     we ensure that the bound variables are all assignable,
     and that the non-wrapped term has the form
     described in the user documentation;
     we generate code that affects the variables from that term.
     In all cases, we recursively generate the block items for the body
     and we put those just after the preceding code.
     We use the sum of the two limits as the overall limit:
     thus, after @(tsee exec-block-item-list) executes
     the block items for the bound term,
     it still has enough limit to execute the block items for the body term.")
   (xdoc::p
    "If the term is a @(tsee let), there are six cases.
     If the binding has the form of an array write,
     we generate an array assignment.
     If the binding has the form of a structure scalar member write,
     we generate an assignment to
     the member of the structure,
     by value or by pointer
     If the binding has the form of a structure array member write,
     we generate an assignment to
     the element of the member of the structure,
     by value or by pointer.
     The other three cases are similar to
     the three @(tsee mv-let) cases above.
     The limit is calculated as follows.
     For the case of the term representing code that affects variables,
     we add up the two limits,
     similarly to the @(tsee mv-let) case.
     For the other cases, we have one block item followed by block items.
     First, we need 1 to go from @(tsee exec-block-item-list)
     to @(tsee exec-block-item).
     Then we take the sum of the limit for the first block item
     and the limit for the remaining block items
     (in principle we could take the maximum,
     but see the discussion above for @(tsee if)
     for why we take the sum instead).
     The first block item is a declaration, an assignment, or a function call.
     If it is a declaration, we need 1 to go from @(tsee exec-block-item)
     to the @(':declon') case and to @(tsee exec-expr-call-or-pure),
     for which we get the limit.
     If it is an assignment, we need 1 to go from @(tsee exec-block-item)
     to the @(':stmt') case and to @(tsee exec-stmt),
     another 1 to go from there to the @(':expr') case
     and to @(tsee exec-expr-call-or-asg),
     another 1 to fo from there to @(tsee exec-expr-asg),
     and another 1 to go from there to @(tsee exec-expr-call-or-pure),
     for which we recursively get the limit.
     For the remaining block items, we need to add another 1
     to go from @(tsee exec-block-item-list) to its recursive call.")
   (xdoc::p
    "If the term is a single variable
     and @('affect') is a singleton list with that variable,
     there are two cases:
     if the loop flag is @('t'), it is an error;
     otherwise, we return nothing, because
     this is the end of a list of block items that affects that variable.
     We generate 1 as the limit,
     because we need 1 to go from @(tsee exec-block-item-list)
     to the empty list case.")
   (xdoc::p
    "If the term is an @(tsee mv), there are three cases.
     If the loop flag is @('t'), it is an error.
     Otherwise, if the arguments of @(tsee mv) are the @('affect') variables,
     we return nothing, because
     this is the end of a list of block items that affects that variable;
     we return 1 as the limit, for the same reason as the case above.
     Otherwise, if the @(tsee cdr) of the arguments of @(tsee mv)
     are the @('affect') variables,
     we treat the @(tsee car) of the arguments of @(tsee mv)
     as an expression term that must affect no variables,
     and generate a return statement for it.")
   (xdoc::p
    "If the term is a call of a recursive target function on its formals,
     different from the current function @('fn'),
     then the term represents a loop.
     The loop flag must be @('nil') for this to be allowed.
     We retrieve the associated loop statement and return it.
     We also retrieve the associated limit term,
     which, as explained in @(tsee atc-fn-info),
     suffices to execute @(tsee exec-stmt-while).
     But here we are executing lists of block items,
     so we need to add 1 to go from @(tsee exec-block-item-list)
     to the call to @(tsee exec-block-item),
     another 1 to go from there to the call to @(tsee exec-stmt),
     and another 1 to go from there to the call to @(tsee exec-stmt-while).")
   (xdoc::p
    "If the term is a call of the current function @('fn') on its formals,
     we ensure that the loop flag is @('t'),
     and we generate no code.
     This represents the conclusion of a loop body (on some path).")
   (xdoc::p
    "If the term is a call of
     a non-recursive target function that returns @('void'),
     the term represents an expression statement
     consisting of a call to the corresponding C function.
     The loop flag must be @('nil') for this to be allowed.
     We ensure that all the pointer arguments are equal to the formals,
     and that the variables affected by the called function are correct.
     We retrieve the limit term associated to the called function,
     which, as explained in @(tsee atc-fn-info),
     suffices to execute @(tsee exec-fun).
     But here we are executing lists of block items,
     so we need to add 1 to go from @(tsee exec-block-item-list)
     to the call of @(tsee exec-block-item),
     another 1 to go from there to the call of @(tsee exec-stmt),
     another 1 to go from there to the call of @(tsee exec-expr-call-or-asg),
     another 1 to go from there to the call of @(tsee exec-expr-call),
     and another 1 to go from there to the call of @(tsee exec-fun).")
   (xdoc::p
    "If the term does not have any of the forms above,
     we treat it as an expression term returning a C value.
     We ensure that the loop flag is @('nil').
     We also ensure that the expression affects
     the same variables as the statement term.
     For the limit, we need 1 to go from @(tsee exec-block-item-list)
     to @(tsee exec-block-item),
     another 1 to go from there to the @(':stmt') case and @(tsee exec-stmt),
     another 1 to go from there to the @(':return') case
     and @(tsee exec-expr-call-or-pure),
     for which we use the recursively calculated limit."))
  (b* (((acl2::fun (irr)) (ec-call (stmt-gout-fix :irrelevant)))
       (wrld (w state))
       ((stmt-gin gin) gin)
       ((mv okp test-term then-term else-term) (fty-check-if-call term))
       ((when okp)
        (b* (((mv mbtp &) (check-mbt-call test-term))
             ((when mbtp) (atc-gen-stmt then-term gin ctx state))
             ((mv mbt$p &) (check-mbt$-call test-term))
             ((when mbt$p) (atc-gen-stmt then-term gin ctx state))
             ((er (bexpr-gout test) :iferr (irr))
              (atc-gen-expr-bool test-term
                                 (make-bexpr-gin
                                  :inscope gin.inscope
                                  :prec-tags gin.prec-tags
                                  :fn gin.fn
                                  :thm-index gin.thm-index
                                  :names-to-avoid gin.names-to-avoid
                                  :proofs nil)
                                 ctx
                                 state))
             ((er (stmt-gout then))
              (atc-gen-stmt then-term
                            (change-stmt-gin
                             gin
                             :inscope (cons nil gin.inscope)
                             :thm-index test.thm-index
                             :names-to-avoid test.names-to-avoid)
                            ctx
                            state))
             ((er (stmt-gout else))
              (atc-gen-stmt else-term
                            (change-stmt-gin
                             gin
                             :inscope (cons nil gin.inscope)
                             :thm-index then.thm-index
                             :names-to-avoid then.names-to-avoid)
                            ctx
                            state))
             ((unless (equal then.type else.type))
              (er-soft+ ctx t (irr)
                        "When generating C code for the function ~x0, ~
                         two branches ~x1 and ~x2 of a conditional term ~
                         have different types ~x3 and ~x4; ~
                         use conversion operations, if needed, ~
                         to make the branches of the same type."
                        gin.fn then-term else-term then.type else.type))
             (type then.type)
             (limit (pseudo-term-fncall
                     'binary-+
                     (list
                      (pseudo-term-quote 5)
                      (pseudo-term-fncall
                       'binary-+
                       (list then.limit else.limit))))))
          (acl2::value
           (make-stmt-gout
            :items
            (list
             (block-item-stmt
              (make-stmt-ifelse :test test.expr
                                :then (make-stmt-compound :items then.items)
                                :else (make-stmt-compound :items else.items))))
            :type type
            :limit limit
            :events (append test.events then.events else.events)
            :thm-index else.thm-index
            :names-to-avoid else.names-to-avoid
            :proofs nil))))
       ((mv okp var? vars indices val-term body-term wrapper?)
        (atc-check-mv-let term))
       ((when okp)
        (b* ((all-vars (if var? (cons var? vars) vars))
             (val-instance (fty-fsublis-var gin.var-term-alist val-term))
             (vals (atc-make-mv-nth-terms indices val-instance))
             (var-term-alist-body
              (atc-update-var-term-alist all-vars vals gin.var-term-alist))
             ((when (eq wrapper? 'declar))
              (b* ((var var?)
                   ((mv type? & errorp) (atc-check-var var gin.inscope))
                   ((when errorp)
                    (er-soft+ ctx t (irr)
                              "When generating C code for the function ~x0, ~
                               a new variable ~x1 has been encountered ~
                               that has the same symbol name as, ~
                               but different package name from, ~
                               a variable already in scope. ~
                               This is disallowed."
                              gin.fn var))
                   ((when type?)
                    (er-soft+ ctx t (irr)
                              "The variable ~x0 in the function ~x1 ~
                               is already in scope and cannot be re-declared."
                              var gin.fn))
                   ((unless (paident-stringp (symbol-name var)))
                    (er-soft+ ctx t (irr)
                              "The symbol name ~s0 of ~
                               the MV-LET variable ~x1 of the function ~x2 ~
                               must be a portable ASCII C identifier, ~
                               but it is not."
                              (symbol-name var) var gin.fn))
                   ((mv type?-list innermostp-list)
                    (atc-get-vars-check-innermost vars gin.inscope))
                   ((when (member-eq nil type?-list))
                    (er-soft+ ctx t (irr)
                              "When generating C code for the function ~x0, ~
                               an attempt is made to modify the variables ~x1, ~
                               not all of which are in scope."
                              gin.fn vars))
                   ((unless (atc-vars-assignablep
                             vars innermostp-list gin.affect))
                    (er-soft+ ctx t (irr)
                              "When generating C code for the function ~x0, ~
                               an attempt is made to modify the variables ~x1, ~
                               not all of which are assignable."
                              gin.fn vars))
                   ((er (expr-gout init) :iferr (irr))
                    (atc-gen-expr val-term
                                  (make-expr-gin
                                   :var-term-alist gin.var-term-alist
                                   :inscope gin.inscope
                                   :fn gin.fn
                                   :prec-fns gin.prec-fns
                                   :prec-tags gin.prec-tags
                                   :thm-index gin.thm-index
                                   :names-to-avoid gin.names-to-avoid
                                   :proofs nil)
                                  ctx
                                  state))
                   ((when (type-case init.type :pointer))
                    (er-soft+ ctx t (irr)
                              "When generating C code for the function ~x0, ~
                               the term ~x1 of pointer type ~x2 ~
                               is being assigned to a new variable ~x3. ~
                               This is currently disallowed, ~
                               because it would create an alias."
                              gin.fn val-term init.type var))
                   ((unless (equal init.affect vars))
                    (er-soft+ ctx t (irr)
                              "The term ~x0 to which the variable ~x1 is bound ~
                               must affect the variables ~x2, ~
                               but it affects ~x3 instead."
                              val-term var vars init.affect))
                   ((er typed-formals :iferr (irr))
                    (atc-typed-formals gin.fn
                                       gin.prec-tags
                                       gin.prec-objs
                                       ctx
                                       state))
                   ((er & :iferr (irr))
                    (atc-ensure-formals-not-lost vars
                                                 gin.affect
                                                 typed-formals
                                                 gin.fn
                                                 ctx
                                                 state))
                   ((mv tyspec declor) (ident+type-to-tyspec+declor
                                        (make-ident :name (symbol-name var))
                                        init.type))
                   (declon (make-obj-declon :tyspec tyspec
                                            :declor declor
                                            :init? (initer-single init.expr)))
                   (item (block-item-declon declon))
                   (inscope-body (atc-add-var var init.type gin.inscope))
                   ((er (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :var-term-alist var-term-alist-body
                                   :inscope inscope-body
                                   :thm-index init.thm-index
                                   :names-to-avoid init.names-to-avoid
                                   :proofs nil)
                                  ctx
                                  state))
                   (type body.type)
                   (limit (pseudo-term-fncall
                           'binary-+
                           (list (pseudo-term-quote 3)
                                 (pseudo-term-fncall
                                  'binary-+
                                  (list init.limit body.limit))))))
                (acl2::value (make-stmt-gout
                              :items (cons item body.items)
                              :type type
                              :limit limit
                              :events (append init.events body.events)
                              :thm-index body.thm-index
                              :names-to-avoid body.names-to-avoid
                              :proofs nil))))
             ((when (eq wrapper? 'assign))
              (b* ((var var?)
                   ((mv type? innermostp &) (atc-check-var var gin.inscope))
                   ((unless type?)
                    (er-soft+ ctx t (irr)
                              "When generating C code for the function ~x0, ~
                               an attempt is being made ~
                               to modify a variable ~x1 not in scope."
                              gin.fn var))
                   ((unless (atc-var-assignablep var innermostp gin.affect))
                    (er-soft+ ctx t (irr)
                              "When generating C code for the function ~x0, ~
                               an attempt is being made ~
                               to modify a non-assignable variable ~x1."
                              gin.fn var))
                   (prev-type type?)
                   ((er (expr-gout rhs) :iferr (irr))
                    (atc-gen-expr val-term
                                  (make-expr-gin
                                   :var-term-alist gin.var-term-alist
                                   :inscope gin.inscope
                                   :fn gin.fn
                                   :prec-fns gin.prec-fns
                                   :prec-tags gin.prec-tags
                                   :thm-index gin.thm-index
                                   :names-to-avoid gin.names-to-avoid
                                   :proofs nil)
                                  ctx
                                  state))
                   ((unless (equal prev-type rhs.type))
                    (er-soft+ ctx t (irr)
                              "The type ~x0 of the term ~x1 ~
                               assigned to the LET variable ~x2 ~
                               of the function ~x3 ~
                               differs from the type ~x4 ~
                               of a variable with the same symbol in scope."
                              rhs.type val-term var gin.fn prev-type))
                   ((unless (equal rhs.affect vars))
                    (er-soft+ ctx t (irr)
                              "The term ~x0 to which the variable ~x1 is bound ~
                               must affect the variables ~x2, ~
                               but it affects ~x3 instead."
                              val-term var vars rhs.affect))
                   ((er typed-formals :iferr (irr))
                    (atc-typed-formals gin.fn
                                       gin.prec-tags
                                       gin.prec-objs
                                       ctx
                                       state))
                   ((er & :iferr (irr))
                    (atc-ensure-formals-not-lost vars
                                                 gin.affect
                                                 typed-formals
                                                 gin.fn
                                                 ctx
                                                 state))
                   ((when (type-case rhs.type :array))
                    (raise "Internal error: array type ~x0." rhs.type)
                    (acl2::value (irr)))
                   ((when (type-case rhs.type :pointer))
                    (er-soft+ ctx t (irr)
                              "The term ~x0 to which the variable ~x1 is bound ~
                               must not have a C pointer type, ~
                               but it has type ~x2 instead."
                              val-term var rhs.type))
                   (asg (make-expr-binary
                         :op (binop-asg)
                         :arg1 (expr-ident (make-ident :name (symbol-name var)))
                         :arg2 rhs.expr))
                   (stmt (stmt-expr asg))
                   (item (block-item-stmt stmt))
                   ((er (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :var-term-alist var-term-alist-body
                                   :thm-index rhs.thm-index
                                   :names-to-avoid rhs.names-to-avoid)
                                  ctx
                                  state))
                   (type body.type)
                   (limit (pseudo-term-fncall
                           'binary-+
                           (list (pseudo-term-quote 6)
                                 (pseudo-term-fncall
                                  'binary-+
                                  (list rhs.limit body.limit))))))
                (acl2::value (make-stmt-gout
                              :items (cons item body.items)
                              :type type
                              :limit limit
                              :events (append rhs.events body.events)
                              :thm-index body.thm-index
                              :names-to-avoid body.names-to-avoid
                              :proofs nil))))
             ((unless (eq wrapper? nil))
              (prog2$ (raise "Internal error: MV-LET wrapper is ~x0." wrapper?)
                      (acl2::value (irr))))
             ((mv type?-list innermostp-list)
              (atc-get-vars-check-innermost vars gin.inscope))
             ((when (member-eq nil type?-list))
              (er-soft+ ctx t (irr)
                        "When generating C code for the function ~x0, ~
                         an attempt is made to modify the variables ~x1, ~
                         not all of which are in scope."
                        gin.fn vars))
             ((unless (atc-vars-assignablep vars innermostp-list gin.affect))
              (er-soft+ ctx t (irr)
                        "When generating C code for the function ~x0, ~
                         an attempt is made to modify the variables ~x1, ~
                         not all of which are assignable."
                        gin.fn vars))
             ((unless (atc-affecting-term-for-let-p val-term gin.prec-fns))
              (er-soft+ ctx t (irr)
                        "When generating C code for the function ~x0, ~
                         an MV-LET has been encountered ~
                         whose term ~x1 to which the variables are bound ~
                         does not have the required form."
                        gin.fn val-term))
             ((er typed-formals :iferr (irr))
              (atc-typed-formals gin.fn gin.prec-tags gin.prec-objs ctx state))
             ((er & :iferr (irr))
              (atc-ensure-formals-not-lost vars
                                           gin.affect
                                           typed-formals
                                           gin.fn
                                           ctx
                                           state))
             ((er (stmt-gout xform))
              (atc-gen-stmt val-term
                            (change-stmt-gin gin
                                             :affect vars
                                             :loop-flag nil
                                             :thm-index gin.thm-index
                                             :names-to-avoid gin.names-to-avoid)
                            ctx
                            state))
             ((unless (type-case xform.type :void))
              (er-soft+ ctx t (irr)
                        "When generating C code for the function ~x0, ~
                         an MV-LET has been encountered ~
                         whose term ~x1 to which the variables are bound ~
                         has the non-void type ~x2, ~
                         which is disallowed."
                        gin.fn val-term xform.type))
             ((er (stmt-gout body))
              (atc-gen-stmt body-term
                            (change-stmt-gin
                             gin
                             :var-term-alist var-term-alist-body
                             :thm-index xform.thm-index
                             :names-to-avoid xform.names-to-avoid)
                            ctx
                            state))
             (items (append xform.items body.items))
             (type body.type)
             (limit (pseudo-term-fncall 'binary-+
                                        (list xform.limit body.limit))))
          (acl2::value (make-stmt-gout
                        :items items
                        :type type
                        :limit limit
                        :events (append xform.events body.events)
                        :thm-index body.thm-index
                        :names-to-avoid body.names-to-avoid
                        :proofs nil))))
       ((mv okp var val-term body-term wrapper?) (atc-check-let term))
       ((when okp)
        (b* ((val-instance (fty-fsublis-var gin.var-term-alist val-term))
             (var-term-alist-body
              (atc-update-var-term-alist (list var)
                                         (list val-instance)
                                         gin.var-term-alist))
             ((mv okp sub-term elem-term sub-type elem-type)
              (atc-check-array-write var val-term))
             ((when okp)
              (b* (((unless (eq wrapper? nil))
                    (er-soft+ ctx t (irr)
                              "The array write term ~x0 to which ~x1 is bound ~
                               has the ~x2 wrapper, which is disallowed."
                              val-term var wrapper?))
                   ((unless (member-eq var gin.affect))
                    (er-soft+ ctx t (irr)
                              "The array ~x0 is being written to, ~
                               but it is not among the variables ~x1 ~
                               currently affected."
                              var gin.affect))
                   ((er (pexpr-gout arr) :iferr (irr))
                    (atc-gen-expr-pure var
                                       (make-pexpr-gin
                                        :inscope gin.inscope
                                        :prec-tags gin.prec-tags
                                        :fn gin.fn
                                        :thm-index gin.thm-index
                                        :names-to-avoid gin.names-to-avoid
                                        :proofs nil)
                                       ctx
                                       state))
                   ((er (pexpr-gout sub) :iferr (irr))
                    (atc-gen-expr-pure sub-term
                                       (make-pexpr-gin
                                        :inscope gin.inscope
                                        :prec-tags gin.prec-tags
                                        :fn gin.fn
                                        :thm-index arr.thm-index
                                        :names-to-avoid arr.names-to-avoid
                                        :proofs nil)
                                       ctx
                                       state))
                   ((er (pexpr-gout elem) :iferr (irr))
                    (atc-gen-expr-pure elem-term
                                       (make-pexpr-gin
                                        :inscope gin.inscope
                                        :prec-tags gin.prec-tags
                                        :fn gin.fn
                                        :thm-index sub.thm-index
                                        :names-to-avoid sub.names-to-avoid
                                        :proofs nil)
                                       ctx
                                       state))
                   ((unless (equal arr.type (type-pointer elem-type)))
                    (er-soft+ ctx t (irr)
                              "The array ~x0 of type ~x1 ~
                               does not have the expected type ~x2. ~
                               This is indicative of ~
                               unreachable code under the guards, ~
                               given that the code is guard-verified."
                              var arr.type (type-pointer elem-type)))
                   ((unless (equal sub.type sub-type))
                    (er-soft+ ctx t (irr)
                              "The array ~x0 of type ~x1 ~
                               is being indexed with ~
                               a subscript ~x2 of type x3, ~
                               instead of type ~x4 as expected.
                               This is indicative of ~
                               unreachable code under the guards, ~
                               given that the code is guard-verified."
                              var arr.type sub sub.type sub-type))
                   ((unless (equal elem.type elem-type))
                    (er-soft+ ctx t (irr)
                              "The array ~x0 of type ~x1 ~
                               is being written to with ~
                               an element ~x2 of type x3, ~
                               instead of type ~x4 as expected.
                               This is indicative of ~
                               unreachable code under the guards, ~
                               given that the code is guard-verified."
                              var arr.type elem elem.type elem-type))
                   (asg (make-expr-binary
                         :op (binop-asg)
                         :arg1 (make-expr-arrsub :arr arr.expr
                                                 :sub sub.expr)
                         :arg2 elem.expr))
                   (stmt (stmt-expr asg))
                   (item (block-item-stmt stmt))
                   ((er (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :var-term-alist var-term-alist-body
                                   :thm-index elem.thm-index
                                   :names-to-avoid elem.names-to-avoid)
                                  ctx
                                  state))
                   (limit (pseudo-term-fncall 'binary-+
                                              (list (pseudo-term-quote 4)
                                                    body.limit))))
                (acl2::value (make-stmt-gout
                              :items (cons item body.items)
                              :type body.type
                              :limit limit
                              :events (append arr.events
                                              sub.events
                                              elem.events
                                              body.events)
                              :thm-index body.thm-index
                              :names-to-avoid body.names-to-avoid
                              :proofs nil))))
             ((mv okp member-term tag member-name member-type)
              (atc-check-struct-write-scalar var val-term gin.prec-tags))
             ((when okp)
              (b* (((unless (eq wrapper? nil))
                    (er-soft+ ctx t (irr)
                              "The structure write term ~x0 ~
                               to which ~x1 is bound ~
                               has the ~x2 wrapper, which is disallowed."
                              val-term var wrapper?))
                   ((er (pexpr-gout struct) :iferr (irr))
                    (atc-gen-expr-pure var
                                       (make-pexpr-gin
                                        :inscope gin.inscope
                                        :prec-tags gin.prec-tags
                                        :fn gin.fn
                                        :thm-index gin.thm-index
                                        :names-to-avoid gin.names-to-avoid
                                        :proofs nil)
                                       ctx
                                       state))
                   ((er pointerp)
                    (cond
                     ((equal struct.type (type-struct tag))
                      (acl2::value nil))
                     ((equal struct.type (type-pointer (type-struct tag)))
                      (acl2::value t))
                     (t (er-soft+ ctx t (irr)
                                  "The structure ~x0 of type ~x1 ~
                                   does not have the expected type ~x2 or ~x3. ~
                                   This is indicative of ~
                                   unreachable code under the guards, ~
                                   given that the code is guard-verified."
                                  var
                                  struct.type
                                  (type-struct tag)
                                  (type-pointer (type-struct tag))))))
                   ((when (and pointerp
                               (not (member-eq var gin.affect))))
                    (er-soft+ ctx t (irr)
                              "The structure ~x0 ~
                               is being written to by pointer, ~
                               but it is not among the variables ~x1 ~
                               currently affected."
                              var gin.affect))
                   ((er (pexpr-gout member) :iferr (irr))
                    (atc-gen-expr-pure member-term
                                       (make-pexpr-gin
                                        :inscope gin.inscope
                                        :prec-tags gin.prec-tags
                                        :fn gin.fn
                                        :thm-index struct.thm-index
                                        :names-to-avoid struct.names-to-avoid
                                        :proofs nil)
                                       ctx
                                       state))
                   ((unless (equal member.type member-type))
                    (er-soft+ ctx t (irr)
                              "The structure ~x0 of type ~x1 ~
                               is being written to with ~
                               a member ~x2 of type ~x3, ~
                               instead of type ~x4 as expected. ~
                               This is indicative of ~
                               unreachable code under the guards, ~
                               given that the code is guard-verified."
                              var struct.type member-term
                              member.type member-type))
                   (asg-mem (if pointerp
                                (make-expr-memberp :target struct.expr
                                                   :name member-name)
                              (make-expr-member :target struct.expr
                                                :name member-name)))
                   (asg (make-expr-binary :op (binop-asg)
                                          :arg1 asg-mem
                                          :arg2 member.expr))
                   (stmt (stmt-expr asg))
                   (item (block-item-stmt stmt))
                   ((er (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :var-term-alist var-term-alist-body
                                   :thm-index member.thm-index
                                   :names-to-avoid member.names-to-avoid)
                                  ctx
                                  state))
                   (limit (pseudo-term-fncall 'binary-+
                                              (list (pseudo-term-quote 4)
                                                    body.limit))))
                (acl2::value (make-stmt-gout
                              :items (cons item body.items)
                              :type body.type
                              :limit limit
                              :events (append struct.events
                                              member.events)
                              :thm-index body.thm-index
                              :names-to-avoid body.names-to-avoid
                              :proofs nil))))
             ((mv okp index-term elem-term tag member index-type elem-type)
              (atc-check-struct-write-array var val-term gin.prec-tags))
             ((when okp)
              (b* (((unless (eq wrapper? nil))
                    (er-soft+ ctx t (irr)
                              "The structure write term ~x0 ~
                               to which ~x1 is bound ~
                               has the ~x2 wrapper, which is disallowed."
                              val-term var wrapper?))
                   ((er (pexpr-gout struct) :iferr (irr))
                    (atc-gen-expr-pure var
                                       (make-pexpr-gin
                                        :inscope gin.inscope
                                        :prec-tags gin.prec-tags
                                        :fn gin.fn
                                        :thm-index gin.thm-index
                                        :names-to-avoid gin.names-to-avoid
                                        :proofs nil)
                                       ctx
                                       state))
                   ((er pointerp)
                    (cond
                     ((equal struct.type (type-struct tag))
                      (acl2::value nil))
                     ((equal struct.type (type-pointer (type-struct tag)))
                      (acl2::value t))
                     (t (er-soft+ ctx t (irr)
                                  "The structure ~x0 of type ~x1 ~
                                   does not have the expected type ~x2 or ~x3. ~
                                   This is indicative of ~
                                   unreachable code under the guards, ~
                                   given that the code is guard-verified."
                                  var
                                  struct.type
                                  (type-struct tag)
                                  (type-pointer (type-struct tag))))))
                   ((when (and pointerp
                               (not (member-eq var gin.affect))))
                    (er-soft+ ctx t (irr)
                              "The structure ~x0 ~
                               is being written to by pointer, ~
                               but it is not among the variables ~x1 ~
                               currently affected."
                              var gin.affect))
                   ((er (pexpr-gout index) :iferr (irr))
                    (atc-gen-expr-pure index-term
                                       (make-pexpr-gin
                                        :inscope gin.inscope
                                        :prec-tags gin.prec-tags
                                        :fn gin.fn
                                        :thm-index struct.thm-index
                                        :names-to-avoid struct.names-to-avoid
                                        :proofs nil)
                                       ctx
                                       state))
                   ((unless (equal index.type index-type))
                    (er-soft+ ctx t (irr)
                              "The structure ~x0 of type ~x1 ~
                               is being written to with ~
                               an index ~x2 of type ~x3, ~
                               instead of type ~x4 as expected. ~
                               This is indicative of ~
                               unreachable code under the guards, ~
                               given that the code is guard-verified."
                              var struct.type index-term index.type index-type))
                   ((er (pexpr-gout elem) :iferr (irr))
                    (atc-gen-expr-pure elem-term
                                       (make-pexpr-gin
                                        :inscope gin.inscope
                                        :prec-tags gin.prec-tags
                                        :fn gin.fn
                                        :thm-index index.thm-index
                                        :names-to-avoid index.names-to-avoid
                                        :proofs nil)
                                       ctx
                                       state))
                   ((unless (equal elem.type elem-type))
                    (er-soft+ ctx t (irr)
                              "The structure ~x0 of type ~x1 ~
                               is being written to with ~
                               a member array element ~x2 of type ~x3, ~
                               instead of type ~x4 as expected.
                               This is indicative of ~
                               unreachable code under the guards, ~
                               given that the code is guard-verified."
                              var struct.type elem-term elem.type elem-type))
                   (asg-mem (if pointerp
                                (make-expr-memberp :target struct.expr
                                                   :name member)
                              (make-expr-member :target struct.expr
                                                :name member)))
                   (asg (make-expr-binary
                         :op (binop-asg)
                         :arg1 (make-expr-arrsub :arr asg-mem
                                                 :sub index.expr)
                         :arg2 elem.expr))
                   (stmt (stmt-expr asg))
                   (item (block-item-stmt stmt))
                   ((er (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :var-term-alist var-term-alist-body
                                   :thm-index elem.thm-index
                                   :names-to-avoid elem.names-to-avoid)
                                  ctx
                                  state))
                   (limit (pseudo-term-fncall 'binary-+
                                              (list (pseudo-term-quote 4)
                                                    body.limit))))
                (acl2::value (make-stmt-gout
                              :items (cons item body.items)
                              :type body.type
                              :limit limit
                              :events (append struct.events
                                              index.events
                                              elem.events
                                              body.events)
                              :thm-index body.thm-index
                              :names-to-avoid body.names-to-avoid
                              :proofs nil))))
             ((mv type? innermostp errorp) (atc-check-var var gin.inscope))
             ((when errorp)
              (er-soft+ ctx t (irr)
                        "When generating C code for the function ~x0, ~
                         a new variable ~x1 has been encountered ~
                         that has the same symbol name as, ~
                         but different package name from, ~
                         a variable already in scope. ~
                         This is disallowed."
                        gin.fn var))
             ((when (eq wrapper? 'declar))
              (b* (((when type?)
                    (er-soft+ ctx t (irr)
                              "The variable ~x0 in the function ~x1 ~
                               is already in scope and cannot be re-declared."
                              var gin.fn))
                   ((unless (paident-stringp (symbol-name var)))
                    (er-soft+ ctx t (irr)
                              "The symbol name ~s0 of ~
                               the LET variable ~x1 of the function ~x2 ~
                               must be a portable ASCII C identifier, ~
                               but it is not."
                              (symbol-name var) var gin.fn))
                   ((er (expr-gout init) :iferr (irr))
                    (atc-gen-expr val-term
                                  (make-expr-gin
                                   :var-term-alist gin.var-term-alist
                                   :inscope gin.inscope
                                   :fn gin.fn
                                   :prec-fns gin.prec-fns
                                   :prec-tags gin.prec-tags
                                   :thm-index gin.thm-index
                                   :names-to-avoid gin.names-to-avoid
                                   :proofs nil)
                                  ctx
                                  state))
                   ((when (type-case init.type :pointer))
                    (er-soft+ ctx t (irr)
                              "When generating C code for the function ~x0, ~
                               the term ~x1 of pointer type ~x2 ~
                               is being assigned to a new variable ~x3. ~
                               This is currently disallowed, ~
                               because it would create an alias."
                              gin.fn val-term init.type var))
                   ((when (consp init.affect))
                    (er-soft+ ctx t (irr)
                              "The term ~x0 to which the variable ~x1 is bound ~
                               must not affect any variables, ~
                               but it affects ~x2 instead."
                              val-term var init.affect))
                   ((mv tyspec declor) (ident+type-to-tyspec+declor
                                        (make-ident :name (symbol-name var))
                                        init.type))
                   (declon (make-obj-declon :tyspec tyspec
                                            :declor declor
                                            :init? (initer-single init.expr)))
                   (item (block-item-declon declon))
                   (inscope-body (atc-add-var var init.type gin.inscope))
                   ((er (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :var-term-alist var-term-alist-body
                                   :inscope inscope-body
                                   :thm-index init.thm-index
                                   :names-to-avoid init.names-to-avoid)
                                  ctx
                                  state))
                   (type body.type)
                   (limit (pseudo-term-fncall
                           'binary-+
                           (list (pseudo-term-quote 3)
                                 (pseudo-term-fncall
                                  'binary-+
                                  (list init.limit body.limit))))))
                (acl2::value (make-stmt-gout
                              :items (cons item body.items)
                              :type type
                              :limit limit
                              :events (append init.events body.events)
                              :thm-index body.thm-index
                              :names-to-avoid body.names-to-avoid
                              :proofs nil))))
             ((unless (atc-var-assignablep var innermostp gin.affect))
              (er-soft+ ctx t (irr)
                        "When generating C code for the function ~x0, ~
                         an attempt is being made ~
                         to modify a non-assignable variable ~x1."
                        gin.fn var))
             ((when (eq wrapper? 'assign))
              (b* ((prev-type type?)
                   ((er (expr-gout rhs) :iferr (irr))
                    (atc-gen-expr val-term
                                  (make-expr-gin
                                   :var-term-alist gin.var-term-alist
                                   :inscope gin.inscope
                                   :fn gin.fn
                                   :prec-fns gin.prec-fns
                                   :prec-tags gin.prec-tags
                                   :thm-index gin.thm-index
                                   :names-to-avoid gin.names-to-avoid
                                   :proofs nil)
                                  ctx
                                  state))
                   ((unless (equal prev-type rhs.type))
                    (er-soft+ ctx t (irr)
                              "The type ~x0 of the term ~x1 ~
                               assigned to the LET variable ~x2 ~
                               of the function ~x3 ~
                               differs from the type ~x4 ~
                               of a variable with the same symbol in scope."
                              rhs.type val-term var gin.fn prev-type))
                   ((when (consp rhs.affect))
                    (er-soft+ ctx t (irr)
                              "The term ~x0 to which the variable ~x1 is bound ~
                               must not affect any variables, ~
                               but it affects ~x2 instead."
                              val-term var rhs.affect))
                   ((when (type-case rhs.type :array))
                    (raise "Internal error: array type ~x0." rhs.type)
                    (acl2::value (irr)))
                   ((when (type-case rhs.type :pointer))
                    (er-soft+ ctx t (irr)
                              "The term ~x0 to which the variable ~x1 is bound ~
                               must not have a C pointer type, ~
                               but it has type ~x2 instead."
                              val-term var rhs.type))
                   (asg (make-expr-binary
                         :op (binop-asg)
                         :arg1 (expr-ident (make-ident :name (symbol-name var)))
                         :arg2 rhs.expr))
                   (stmt (stmt-expr asg))
                   (item (block-item-stmt stmt))
                   ((er (stmt-gout body))
                    (atc-gen-stmt body-term
                                  (change-stmt-gin
                                   gin
                                   :var-term-alist var-term-alist-body
                                   :thm-index rhs.thm-index
                                   :names-to-avoid rhs.names-to-avoid)
                                  ctx
                                  state))
                   (type body.type)
                   (limit (pseudo-term-fncall
                           'binary-+
                           (list (pseudo-term-quote 6)
                                 (pseudo-term-fncall
                                  'binary-+
                                  (list rhs.limit body.limit))))))
                (acl2::value (make-stmt-gout
                              :items (cons item body.items)
                              :type type
                              :limit limit
                              :events (append rhs.events body.events)
                              :thm-index body.thm-index
                              :names-to-avoid body.names-to-avoid
                              :proofs nil))))
             ((unless (eq wrapper? nil))
              (prog2$ (raise "Internal error: LET wrapper is ~x0." wrapper?)
                      (acl2::value (irr))))
             ((unless (atc-affecting-term-for-let-p val-term gin.prec-fns))
              (er-soft+ ctx t (irr)
                        "When generating C code for the function ~x0, ~
                         we encountered a term ~x1, ~
                         to which a LET variable is bound, ~
                         that is not wrapped by C::DECLAR or C::ASSIGN, ~
                         and that is neither an IF or a loop function call. ~
                         This is disallowed."
                        gin.fn val-term))
             ((er typed-formals :iferr (irr))
              (atc-typed-formals gin.fn
                                 gin.prec-tags
                                 gin.prec-objs
                                 ctx
                                 state))
             ((er & :iferr (irr))
              (atc-ensure-formals-not-lost (list var)
                                           gin.affect
                                           typed-formals
                                           gin.fn
                                           ctx
                                           state))
             ((er (stmt-gout xform))
              (atc-gen-stmt val-term
                            (change-stmt-gin gin
                                             :affect (list var)
                                             :loop-flag nil)
                            ctx
                            state))
             ((unless (type-case xform.type :void))
              (er-soft+ ctx t (irr)
                        "When generating C code for the function ~x0, ~
                         a LET has been encountered ~
                         whose unwrapped term ~x1 ~
                         to which the variable is bound ~
                         has the non-void type ~x2, ~
                         which is disallowed."
                        gin.fn val-term xform.type))
             ((er (stmt-gout body))
              (atc-gen-stmt body-term
                            (change-stmt-gin
                             gin
                             :var-term-alist var-term-alist-body
                             :thm-index xform.thm-index
                             :names-to-avoid xform.names-to-avoid)
                            ctx
                            state))
             (items (append xform.items body.items))
             (type body.type)
             (limit (pseudo-term-fncall
                     'binary-+
                     (list xform.limit body.limit))))
          (acl2::value (make-stmt-gout
                        :items items
                        :type type
                        :limit limit
                        :events (append xform.events body.events)
                        :thm-index body.thm-index
                        :names-to-avoid body.names-to-avoid
                        :proofs nil))))
       ((when (and (pseudo-term-case term :var)
                   (equal gin.affect
                          (list (pseudo-term-var->name term)))))
        (if gin.loop-flag
            (er-soft+ ctx t (irr)
                      "A loop body must end with ~
                       a recursive call on every path, ~
                       but in the function ~x0 it ends with ~x1 instead."
                      gin.fn term)
          (acl2::value (make-stmt-gout
                        :items nil
                        :type (type-void)
                        :limit (pseudo-term-quote 1)
                        :events nil
                        :thm-index gin.thm-index
                        :names-to-avoid gin.names-to-avoid
                        :proofs nil))))
       ((mv okp terms) (fty-check-list-call term))
       ((when okp)
        (b* (((unless (>= (len terms) 2))
              (raise "Internal error: MV applied to ~x0." terms)
              (acl2::value (irr)))
             ((when gin.loop-flag)
              (er-soft+ ctx t (irr)
                        "A loop body must end with ~
                         a recursive call on every path, ~
                         but in the function ~x0 ~
                         it ends with ~x1 instead."
                        gin.fn term)))
          (cond
           ((equal terms gin.affect)
            (acl2::value (make-stmt-gout :items nil
                                         :type (type-void)
                                         :limit (pseudo-term-quote 1)
                                         :events nil
                                         :thm-index gin.thm-index
                                         :names-to-avoid gin.names-to-avoid
                                         :proofs nil)))
           ((equal (cdr terms) gin.affect)
            (b* (((er (expr-gout first) :iferr (irr))
                  (atc-gen-expr (car terms)
                                (make-expr-gin
                                 :var-term-alist gin.var-term-alist
                                 :inscope gin.inscope
                                 :fn gin.fn
                                 :prec-fns gin.prec-fns
                                 :prec-tags gin.prec-tags
                                 :thm-index gin.thm-index
                                 :names-to-avoid gin.names-to-avoid
                                 :proofs nil)
                                ctx
                                state))
                 ((when (consp first.affect))
                  (er-soft+ ctx t (irr)
                            "The first argument ~x0 of the term ~x1 ~
                             in the function ~x2 ~
                             affects the variables ~x3, which is disallowed."
                            (car terms) term gin.fn first.affect))
                 (limit (pseudo-term-fncall
                         'binary-+
                         (list (pseudo-term-quote 3)
                               first.limit))))
              (acl2::value (make-stmt-gout
                            :items (list (block-item-stmt
                                          (make-stmt-return :value first.expr)))
                            :type first.type
                            :limit limit
                            :events first.events
                            :thm-index first.thm-index
                            :names-to-avoid first.names-to-avoid
                            :proofs nil))))
           (t (er-soft+ ctx t (irr)
                        "When generating C code for the function ~x0, ~
                         a term ~x0 has been encountered, ~
                         which is disallowed."
                        gin.fn term)))))
       ((mv okp loop-fn loop-args in-types loop-affect loop-stmt loop-limit)
        (atc-check-loop-call term gin.var-term-alist gin.prec-fns))
       ((when okp)
        (b* (((when gin.loop-flag)
              (er-soft+ ctx t (irr)
                        "A loop body must end with ~
                         a recursive call on every path, ~
                         but in the function ~x0 it ends with ~x1 instead."
                        gin.fn term))
             (formals (formals+ loop-fn wrld))
             ((unless (equal formals loop-args))
              (er-soft+ ctx t (irr)
                        "When generating C code for the function ~x0, ~
                         a call of the recursive function ~x1 ~
                         has been encountered ~
                         that is not on its formals, ~
                         but instead on the arguments ~x2.
                         This is disallowed; see the ATC user documentation."
                        gin.fn loop-fn loop-args))
             ((unless (equal gin.affect loop-affect))
              (er-soft+ ctx t (irr)
                        "When generating C code for the function ~x0, ~
                         a call of the recursive function ~x1 ~
                         has been encountered
                         that represents a loop affecting ~x2, ~
                         which differs from the variables ~x3 ~
                         being affected here."
                        gin.fn loop-fn loop-affect gin.affect))
             (types (atc-get-vars formals gin.inscope))
             ((when (member-eq nil types))
              (raise "Internal error: not all formals ~x0 have types ~x1."
                     formals types)
              (acl2::value (irr)))
             ((unless (equal types in-types))
              (er-soft+ ctx t (irr)
                        "The loop function ~x0 with input types ~x1 ~
                         is applied to terms ~x2 returning ~x3. ~
                         This is indicative of dead code under the guards, ~
                         given that the code is guard-verified."
                        loop-fn in-types formals types))
             (limit (pseudo-term-fncall
                     'binary-+
                     (list (pseudo-term-quote 3)
                           loop-limit))))
          (acl2::value (make-stmt-gout
                        :items (list (block-item-stmt loop-stmt))
                        :type (type-void)
                        :limit limit
                        :events nil
                        :thm-index gin.thm-index
                        :names-to-avoid gin.names-to-avoid
                        :proofs nil))))
       ((when (equal term `(,gin.fn ,@(formals+ gin.fn wrld))))
        (if gin.loop-flag
            (acl2::value (make-stmt-gout
                          :items nil
                          :type (type-void)
                          :limit (pseudo-term-quote 1)
                          :events nil
                          :thm-index gin.thm-index
                          :names-to-avoid gin.names-to-avoid
                          :proofs nil))
          (er-soft+ ctx t (irr)
                    "When generating code for the recursive function ~x0, ~
                     a recursive call to the loop function occurs ~
                     not at the end of the computation on some path."
                    gin.fn)))
       ((mv okp called-fn arg-terms in-types out-type fn-affect limit)
        (atc-check-cfun-call term gin.var-term-alist gin.prec-fns wrld))
       ((when (and okp
                   (type-case out-type :void)))
        (b* (((when gin.loop-flag)
              (er-soft+ ctx t (irr)
                        "A loop body must end with ~
                         a recursive call on every path, ~
                         but in the function ~x0 it ends with ~x1 instead."
                        gin.fn term))
             ((unless (atc-check-cfun-call-args (formals+ called-fn wrld)
                                                in-types
                                                arg-terms))
              (er-soft+ ctx t (irr)
                        "The call ~x0 does not satisfy the restrictions ~
                         on array arguments being identical to the formals."
                        term))
             ((unless (equal gin.affect fn-affect))
              (er-soft+ ctx t (irr)
                        "When generating C code for the function ~x0, ~
                         a call of the non-recursive function ~x1 ~
                         has been encountered that affects ~x2, ~
                         which differs from the variables ~x3 ~
                         being affected here."
                        gin.fn loop-fn fn-affect gin.affect))
             ((er (pexprs-gout args) :iferr (irr))
              (atc-gen-expr-pure-list arg-terms
                                      (make-pexprs-gin
                                       :inscope gin.inscope
                                       :prec-tags gin.prec-tags
                                       :fn gin.fn
                                       :thm-index gin.thm-index
                                       :names-to-avoid gin.names-to-avoid
                                       :proofs nil)
                                      ctx
                                      state))
             ((unless (equal args.types in-types))
              (er-soft+ ctx t (irr)
                        "The function ~x0 with input types ~x1 is applied to ~
                         expression terms ~x2 returning ~x3. ~
                         This is indicative of provably dead code, ~
                         given that the code is guard-verified."
                        called-fn in-types arg-terms args.types))
             (call-expr (make-expr-call :fun (make-ident
                                              :name (symbol-name called-fn))
                                        :args args.exprs)))
          (acl2::value (make-stmt-gout
                        :items (list (block-item-stmt (stmt-expr call-expr)))
                        :type (type-void)
                        :limit `(binary-+ '5 ,limit)
                        :events args.events
                        :thm-index args.thm-index
                        :names-to-avoid args.names-to-avoid
                        :proofs nil))))
       ((er (expr-gout term) :iferr (irr))
        (atc-gen-expr term
                      (make-expr-gin :var-term-alist gin.var-term-alist
                                     :inscope gin.inscope
                                     :fn gin.fn
                                     :prec-fns gin.prec-fns
                                     :prec-tags gin.prec-tags
                                     :thm-index gin.thm-index
                                     :names-to-avoid gin.names-to-avoid
                                     :proofs nil)
                      ctx
                      state))
       ((when gin.loop-flag)
        (er-soft+ ctx t (irr)
                  "A loop body must end with ~
                   a recursive call on every path, ~
                   but in the function ~x0 it ends with ~x1 instead."
                  gin.fn term))
       ((unless (equal gin.affect term.affect))
        (er-soft+ ctx t (irr)
                  "When generating code for the non-recursive function ~x0, ~
                   a term ~x1 was encountered at the end of the computation, ~
                   that affects the variables ~x2, ~
                   but ~x0 affects the variables ~x3 instead."
                  gin.fn term term.affect gin.affect))
       ((when (type-case term.type :void))
        (raise "Internal error: return term ~x0 has type void." term)
        (acl2::value (irr)))
       ((when (type-case term.type :array))
        (raise "Internal error: array type ~x0." term.type)
        (acl2::value (irr)))
       ((when (type-case term.type :pointer))
        (er-soft+ ctx t (irr)
                  "When generating a return statement for function ~x0, ~
                   the term ~x1 that represents the return expression ~
                   has pointer type ~x2, which is disallowed."
                  gin.fn term term.type))
       (limit (pseudo-term-fncall
               'binary-+
               (list (pseudo-term-quote 3)
                     term.limit))))
    (acl2::value (make-stmt-gout
                  :items (list (block-item-stmt
                                (make-stmt-return :value term.expr)))
                  :type term.type
                  :limit limit
                  :events term.events
                  :thm-index term.thm-index
                  :names-to-avoid term.names-to-avoid
                  :proofs nil)))

  :measure (pseudo-term-count term)

  :verify-guards nil ; done below

  ///

  (defrulel pseudo-termp-when-symbolp
    (implies (symbolp x)
             (pseudo-termp x))
    :enable pseudo-termp)

  (verify-guards atc-gen-stmt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod lstmt-gin
  :short "Inputs for @(tsee atc-gen-loop-stmt)."
  ((inscope atc-symbol-type-alist-listp)
   (fn symbolp)
   (measure-for-fn symbolp)
   (measure-formals symbol-listp)
   (prec-fns atc-symbol-fninfo-alistp)
   (prec-tags atc-string-taginfo-alistp)
   (prec-objs atc-string-objinfo-alistp)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs booleanp))
  :pred lstmt-ginp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod lstmt-gout
  :short "Outputs for @(tsee atc-gen-loop-stmt)."
  ((stmt stmtp)
   (test-term pseudo-termp)
   (body-term pseudo-termp)
   (affect symbol-listp)
   (limit-body pseudo-termp)
   (limit-all pseudo-termp)
   (events pseudo-event-form-list)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs booleanp))
  :pred lstmt-goutp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-stmt ((term pseudo-termp)
                           (gin lstmt-ginp)
                           (ctx ctxp)
                           state)
  :returns (mv erp (val lstmt-goutp) state)
  :short "Generate a C loop statement from an ACL2 term."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called on loop terms (see user documentation).")
   (xdoc::p
    "The term must be an @(tsee if).
     If the test is an @(tsee mbt) or @(tsee mbt$),
     test and `else' branch are ignored,
     while the `then' branch is recursively processed.
     Otherwise, the test must be an expression term returning a boolean
     from which we generate the loop test;
     the `then' branch must be a statement term,
     from which we generate the loop body;
     and the `else' branch must be either a single variable
     or an @(tsee mv) call on variables,
     which must be a subset of the function's formals,
     and from those variables we determine
     the variables affected by the loop.
     The statement term in the `then' branch
     must affect the variables found in the `else' branch.
     We return
     the term that represents the loop test,
     the term that represent the loop body
     and the variables affected by the loop.
     The loop test and body are used to generate more modular theorems.")
   (xdoc::p
    "Note that we push a new scope before processing the loop body.
     This is because the loop body is a block, which opens a new scope in C.")
   (xdoc::p
    "We return a limit that suffices
     to execute @(tsee exec-stmt-while) on (the test and body of)
     the loop statement, as follows.
     We need 1 to get to executing the test,
     which is pure and so does not contribute to the overall limit.
     If the test is true, we need to add the limit to execute the body.
     After that, @(tsee exec-stmt-while) is called recursively,
     decrementing the limit:
     given that we know that the loop function terminates,
     its measure must suffice as the limit.
     The loop function decreases the measure by at least 1 (maybe more)
     at every recursive call, so the limit does not decrease any faster,
     and we will never run out of the limit before the measure runs out.
     Thus the measure is an over-approximation for the limit, which is sound.
     We also note that the measure refers to the initial call of the function,
     while here it would suffice
     to take the measure at the first recursive call,
     but taking the whole measure is simpler,
     and again it is sound to over-appoximate.
     Note that we use the measure function for @('fn')
     that is generated by ATC,
     for the reasons explained in @(tsee atc-gen-loop-measure-fn).
     Besides the @('limit-all') result,
     which is the limit for the whole loop,
     we also return @('limit-body'), which is just for the loop body;
     this is in support for more modular proofs. "))
  (b* (((acl2::fun (irr)) (ec-call (lstmt-gout-fix :irrelevant)))
       ((lstmt-gin gin) gin)
       (wrld (w state))
       ((mv okp test-term then-term else-term) (fty-check-if-call term))
       ((unless okp)
        (er-soft+ ctx t (irr)
                  "When generating C loop code for the recursive function ~x0, ~
                   a term ~x1 that is not an IF has been encountered."
                  gin.fn term))
       ((mv mbtp &) (check-mbt-call test-term))
       ((when mbtp) (atc-gen-loop-stmt then-term gin ctx state))
       ((mv mbt$p &) (check-mbt$-call test-term))
       ((when mbt$p) (atc-gen-loop-stmt then-term gin ctx state))
       ((er (bexpr-gout test) :iferr (irr))
        (atc-gen-expr-bool test-term
                           (make-bexpr-gin
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :thm-index gin.thm-index
                            :names-to-avoid gin.names-to-avoid
                            :proofs nil)
                           ctx
                           state))
       (formals (formals+ gin.fn wrld))
       ((mv okp affect)
        (b* (((when (member-eq else-term formals)) (mv t (list else-term)))
             ((mv okp terms) (fty-check-list-call else-term))
             ((when (and okp
                         (subsetp-eq terms formals)))
              (mv t terms)))
          (mv nil nil)))
       ((unless okp)
        (er-soft+ ctx t (irr)
                  "The non-recursive branch ~x0 of the function ~x1 ~
                   does not have the required form. ~
                   See the user documentation."
                  else-term gin.fn))
       ((er (stmt-gout body) :iferr (irr))
        (atc-gen-stmt then-term
                      (make-stmt-gin
                       :var-term-alist nil
                       :inscope (cons nil gin.inscope)
                       :loop-flag t
                       :affect affect
                       :fn gin.fn
                       :prec-fns gin.prec-fns
                       :prec-tags gin.prec-tags
                       :prec-objs gin.prec-objs
                       :thm-index test.thm-index
                       :names-to-avoid test.names-to-avoid
                       :proofs nil)
                      ctx
                      state))
       ((unless (type-case body.type :void))
        (raise "Internal error: ~
                the loop body ~x0 of ~x1 ~ returns type ~x2."
               then-term gin.fn body.type)
        (mv t (irr) state))
       (body-stmt (make-stmt-compound :items body.items))
       (stmt (make-stmt-while :test test.expr :body body-stmt))
       ((when (eq gin.measure-for-fn 'quote))
        (raise "Internal error: the measure function is QUOTE.")
        (mv t (irr) state))
       (measure-call (pseudo-term-fncall gin.measure-for-fn
                                         gin.measure-formals))
       (limit `(binary-+ '1 (binary-+ ,body.limit ,measure-call))))
    (acl2::value (make-lstmt-gout :stmt stmt
                                  :test-term test-term
                                  :body-term then-term
                                  :affect affect
                                  :limit-body body.limit
                                  :limit-all limit
                                  :thm-index body.thm-index
                                  :names-to-avoid body.names-to-avoid
                                  :proofs nil)))
  :measure (pseudo-term-count term)
  :guard-hints (("Goal" :in-theory (enable acl2::pseudo-fnsym-p)))
  ///

  (defret stmt-kind-of-atc-gen-loop-stmt
    (implies (not erp)
             (equal (stmt-kind (lstmt-gout->stmt val))
                    :while))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-param-declon-list ((typed-formals atc-symbol-type-alistp)
                                   (fn symbolp)
                                   (prec-objs atc-string-objinfo-alistp)
                                   (ctx ctxp)
                                   state)
  :returns (mv erp
               (params param-declon-listp)
               state)
  :short "Generate a list of C parameter declarations
          from a list of ACL2 formal parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ACL2 formal parameters are actually passed as an alist,
     from the formals to their C types,
     as calculated by @(tsee atc-typed-formals).")
   (xdoc::p
    "We check that the name of the parameter is a portable C identifier,
     and distinct from the names of the other parameters.")
   (xdoc::p
    "If a parameter represents an access to an external object,
     we skip it, i.e. we do not generate a declaration for it."))
  (b* (((when (endp typed-formals)) (acl2::value nil))
       ((cons formal type) (car typed-formals))
       (name (symbol-name formal))
       ((unless (paident-stringp name))
        (er-soft+ ctx t nil
                  "The symbol name ~s0 of ~
                   the formal parameter ~x1 of the function ~x2 ~
                   must be a portable ASCII C identifier, but it is not."
                  name formal fn))
       (cdr-formals (strip-cars (cdr typed-formals)))
       ((when (member-equal name (symbol-name-lst cdr-formals)))
        (er-soft+ ctx t nil
                  "The formal parameter ~x0 of the function ~x1 ~
                   has the same symbol name as ~
                   another formal parameter among ~x2; ~
                   this is disallowed, even if the package names differ."
                  formal fn cdr-formals))
       ((when (b* ((info (cdr (assoc-equal (symbol-name formal) prec-objs)))
                   ((unless info) nil)
                   ((unless (atc-obj-infop info))
                    (raise "Internal error: ~
                            malformed ATC-OBJ-INFO ~x0."
                           info))
                   (info (atc-obj-info->defobject info)))
                (eq (defobject-info->name-symbol info) formal)))
        (atc-gen-param-declon-list (cdr typed-formals) fn prec-objs ctx state))
       ((mv tyspec declor) (ident+type-to-tyspec+declor (make-ident :name name)
                                                        type))
       (param (make-param-declon :tyspec tyspec
                                 :declor declor))
       ((er params)
        (atc-gen-param-declon-list (cdr typed-formals) fn prec-objs ctx state)))
    (acl2::value (cons param params)))
  :prepwork ((local
              (in-theory
               (e/d
                (symbol-listp-of-strip-cars-when-atc-symbol-type-alistp)
                ;; for speed:
                (always$
                 member-equal
                 symbol-name-lst))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-guard ((fn symbolp)
                          (names-to-avoid symbol-listp)
                          state)
  :returns (mv (local-event pseudo-event-formp)
               (name symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate a local function for the guard of @('fn')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This will be just used (in the future) in theorems,
     so there is no need to guard-verify it."))
  (b* ((wrld (w state))
       (name (pack fn "-GUARD"))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name
                                           'function
                                           names-to-avoid
                                           wrld))
       (guard (uguard+ fn wrld))
       ((mv event &)
        (evmac-generate-defun name
                              :formals (formals+ fn wrld)
                              :body (untranslate$ guard t state)
                              :verify-guards nil
                              :enable nil)))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfun-fun-env-thm ((fn symbolp)
                                  (prog-const symbolp)
                                  (finfo? fun-info-optionp)
                                  (init-fun-env-thm symbolp)
                                  (names-to-avoid symbol-listp)
                                  (wrld plist-worldp))
  :returns (mv (local-events pseudo-event-form-listp)
               (name symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorem saying that
          looking up a certain C function in the function environment
          yields the information for that function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This serves to speed up the proofs
     when there is a large number of functions involved.
     A previous version of ATC was generating proofs
     that were executing function lookups,
     which worked fine for small programs,
     but not for larger programs."))
  (b* (((unless (fun-infop finfo?)) (mv nil nil names-to-avoid))
       (thm-name (add-suffix fn "-FUN-ENV"))
       ((mv thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix thm-name nil names-to-avoid wrld))
       (fn-name (symbol-name fn))
       (formula `(equal (fun-env-lookup (ident ,fn-name)
                                        (init-fun-env (preprocess ,prog-const)))
                        ',finfo?))
       (hints `(("Goal" :in-theory '((:e fun-env-lookup)
                                     (:e ident)
                                     ,init-fun-env-thm))))
       ((mv event &)
        (evmac-generate-defthm thm-name
                               :formula formula
                               :hints hints
                               :enable nil)))
    (mv (list event) thm-name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-result-thm ((fn symbolp)
                               (type? type-optionp)
                               (affect symbol-listp)
                               (typed-formals atc-symbol-type-alistp)
                               (prec-fns atc-symbol-fninfo-alistp)
                               (prec-tags atc-string-taginfo-alistp)
                               (prec-objs atc-string-objinfo-alistp)
                               (names-to-avoid symbol-listp)
                               state)
  :guard (not (eq fn 'quote))
  :returns (mv (events pseudo-event-form-listp)
               (name symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorem about the result(s) of @('fn')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a local theorem for now.")
   (xdoc::p
    "The restrictions on the form of the functions that ATC translates to C
     ensures that, under the guard, these functions always return C values.
     This is fairly easy to see,
     thinking of the different allowed forms of these functions' bodies:")
   (xdoc::ul
    (xdoc::li
     "A formal parameter is constrained to be a C value by the guard.")
    (xdoc::li
     "Calls of @(tsee sint-dec-const), @(tsee add-sint-sint), etc.
      are known to return C values.")
    (xdoc::li
     "Calls of array and structure readers and writers
      are known to return C values.")
    (xdoc::li
     "A @(tsee let) or @(tsee mv-let) variable is equal to a term that,
      recursively, always returns a C value.")
    (xdoc::li
     "A call of a preceding function returns (a) C value(s),
      as proved by the same theorems for the preceding functions.")
    (xdoc::li
     "An @(tsee if) returns the same as its branches,
      when the test is not @(tsee mbt) or @(tsee mbt$).")
    (xdoc::li
     "An @(tsee if) return the same as its `then' branch,
      when the test is @(tsee mbt) or @(tsee mbt$),
      because the guard excludes the `else' branch from consideration.")
    (xdoc::li
     "An @(tsee mv) returns C values,
      because either they are parameters or bound variables,
      or they are terms that recursively return C values
      (the latter case is for non-recursive functions
      that return a non-@('void') result
      and also affect arrays and structures)."))
   (xdoc::p
    "This suggests a coarse but adequate proof strategy:
     We use the theory consisting of
     the definition of @('fn'),
     the return type theorems of @(tsee sint-dec-const) and related functions,
     the return type theorems for array and structure readers and writers,
     and the theorems about the preceding functions.
     We also include the definitions of the recognizers
     of the external objects that precede @('fn'),
     which certainly include any external object used in @('fn'):
     this is needed if @('fn') returns the external object,
     because the guard uses its recognizer,
     which implies but differs from a type predicate.
     We also add a @(':use') hint for the guard theorem of @('fn').
     The theorems about structure readers and writers
     are taken from the alist of the preceding structure tags.")
   (xdoc::p
    "In the absence of @(tsee mbt) or @(tsee mbt$),
     we would not need all of the guard as hypothesis,
     but only the part that constrains the formal parameters to be C values.
     These hypotheses are needed when the function returns them;
     when instead the function returns a representation of some operation,
     e.g. a call of @(tsee sint-dec-const) or @(tsee add-sint-sint),
     these return C values unconditionally, so no hypotheses are needed.
     This is because ATC, when generating C code,
     ensures that the ACL2 terms follow the C typing rules,
     whether the terms are reachable under the guards or not.
     However, in the presence of @(tsee mbt) or @(tsee mbt$),
     we need the guard to exclude the `else' branches,
     which are otherwise unconstrained.")
   (xdoc::p
    "As explained in the user documentation,
     an ACL2 function may return a combination of
     an optional C result
     and zero or more affected variables or arrays or structures.
     We collect all of them.
     The C result is determined from the optional C type of the function,
     which is @('nil') for recursive functions,
     and may or may not be @('void') for non-recursive functions.
     The affected variables are also considered as results.
     We concatenate zero or one types from @('type?')
     with zero or more types from @('affect') and @('typed-formals').
     More precisely, we make an alist instead of a list,
     whose values are the types in question
     and whose keys are @('nil') for the C result (if present)
     and the names in @('affect') for the other ones.
     Then we operate on the resulting alist,
     which forms all the results of the function
     with their names (and @('nil') for the result, if present).
     The alist is never empty (an ACL2 function must always return something).
     If the alist is a singleton,
     we generate assertions about the function call.
     If the list has multiple elements,
     we generate assertions for the @(tsee mv-nth)s of the function call.")
   (xdoc::p
    "If @('fn') is recursive, we generate a hint to induct on the function.
     Since ACL2 disallows @(':use') and @(':induct') hints on the goal,
     we make the @(':use') hint a computed hint;
     we do that whether @('fn') is recursive or not, for simplicity.")
   (xdoc::p
    "Terms may appear during the proof of this theorem, where
     @(tsee mv-nth)s are applied to @(tsee list)s (i.e. @(tsee cons) nests).
     So we add the rule" (xdoc::@def "mv-nth-of-cons") " to the theory,
     in order to simplify those terms.
     We also enable the executable counterpart of @(tsee zp)
     to simplify the test in the right-hand side of that rule.")
   (xdoc::p
    "For each result of the function,
     we always generate an assertion about its C type.")
   (xdoc::p
    "We also generate assertions saying that the results are not @('nil').
     Without this, some proofs fail with a subgoal saying that
     a function result is @('nil'), which is false.
     This seems to happen only with functions returning multiple results,
     where the results in question have the form @('(mv-nth ...)').
     So we generate these non-@('nil') theorems only for multiple results.
     These theorems have to be rewrite rules:
     with type prescription rules,
     the example theorems mentioned above still fail.
     To prove these non-@('nil') theorems,
     it seems sufficient to enable
     the executable counterparts of the type recognizers;
     the subgoals that arise without them have the form
     @('(<recognizer> nil)').")
   (xdoc::p
    "We also generate assertions saying that
     each array returned by the function
     has the same length as the corresponding input array.
     This is necessary for the correctness proofs of
     functions that call this function."))
  (b* ((wrld (w state))
       (results1 (and type?
                      (not (type-case type? :void))
                      (list (cons nil type?))))
       (results2 (atc-gen-fn-result-thm-aux1 affect typed-formals))
       (results (append results1 results2))
       ((unless (consp results))
        (raise "Internal error: the function ~x0 has no results." fn)
        (mv nil nil names-to-avoid))
       (formals (formals+ fn wrld))
       (fn-call `(,fn ,@formals))
       (conjuncts (atc-gen-fn-result-thm-aux2 results
                                              (if (consp (cdr results))
                                                  0
                                                nil)
                                              fn-call
                                              wrld))
       (conclusion
        (if (and (consp conjuncts)
                 (not (consp (cdr conjuncts))))
            (car conjuncts)
          `(and ,@conjuncts)))
       (name (add-suffix fn
                         (if (consp (cdr results))
                             "-RESULTS"
                           "-RESULT")))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name nil names-to-avoid wrld))
       (guard (untranslate$ (uguard+ fn wrld) t state))
       (formula `(implies ,guard ,conclusion))
       (hints `(("Goal"
                 ,@(and (irecursivep+ fn wrld)
                        `(:induct ,fn-call))
                 :in-theory
                 (append
                  *atc-integer-ops-1-return-rewrite-rules*
                  *atc-integer-ops-2-return-rewrite-rules*
                  *atc-integer-convs-return-rewrite-rules*
                  *atc-array-read-return-rewrite-rules*
                  *atc-array-write-return-rewrite-rules*
                  *atc-array-length-write-rules*
                  *atc-wrapper-rules*
                  ',(atc-string-taginfo-alist-to-reader-return-thms prec-tags)
                  ',(atc-string-taginfo-alist-to-writer-return-thms prec-tags)
                  ',(atc-string-objinfo-alist-to-recognizers prec-objs)
                  '(,fn
                    ,@(atc-symbol-fninfo-alist-to-result-thms
                       prec-fns (all-fnnames (ubody+ fn wrld)))
                    sintp-of-sint-dec-const
                    sintp-of-sint-oct-const
                    sintp-of-sint-hex-const
                    uintp-of-uint-dec-const
                    uintp-of-uint-oct-const
                    uintp-of-uint-hex-const
                    slongp-of-slong-dec-const
                    slongp-of-slong-oct-const
                    slongp-of-slong-hex-const
                    ulongp-of-ulong-dec-const
                    ulongp-of-ulong-oct-const
                    ulongp-of-ulong-hex-const
                    sllongp-of-sllong-dec-const
                    sllongp-of-sllong-oct-const
                    sllongp-of-sllong-hex-const
                    ullongp-of-ullong-dec-const
                    ullongp-of-ullong-oct-const
                    ullongp-of-ullong-hex-const
                    sintp-of-sint-from-boolean
                    mv-nth-of-cons
                    (:e zp)
                    (:e ucharp)
                    (:e scharp)
                    (:e ushortp)
                    (:e sshortp)
                    (:e uintp)
                    (:e sintp)
                    (:e ulongp)
                    (:e slongp)
                    (:e ullongp)
                    (:e sllongp)
                    (:e uchar-arrayp)
                    (:e schar-arrayp)
                    (:e ushort-arrayp)
                    (:e sshort-arrayp)
                    (:e uint-arrayp)
                    (:e sint-arrayp)
                    (:e ulong-arrayp)
                    (:e slong-arrayp)
                    (:e ullong-arrayp)
                    (:e sllong-arrayp)
                    ,@(loop$ for recog
                             in (atc-string-taginfo-alist-to-recognizers
                                 prec-tags)
                             collect `(:e ,recog)))))
                '(:use (:guard-theorem ,fn))))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (mv (list event) name names-to-avoid))

  :prepwork

  ((define atc-gen-fn-result-thm-aux1 ((affect symbol-listp)
                                       (typed-formals atc-symbol-type-alistp))
     :returns (results atc-symbol-type-alistp :hyp (symbol-listp affect))
     :parents nil
     (cond ((endp affect) nil)
           (t (b* ((type (cdr (assoc-eq (car affect)
                                        typed-formals))))
                (if (typep type)
                    (acons (car affect)
                           type
                           (atc-gen-fn-result-thm-aux1 (cdr affect)
                                                       typed-formals))
                  (raise "Internal error: variable ~x0 not found in ~x1."
                         (car affect) typed-formals))))))

   (define atc-gen-fn-result-thm-aux2 ((results atc-symbol-type-alistp)
                                       (index? maybe-natp)
                                       (fn-call pseudo-termp)
                                       (wrld plist-worldp))
     :returns conjuncts
     :parents nil
     (b* (((when (endp results)) nil)
          (theresult (if index?
                         `(mv-nth ,index? ,fn-call)
                       fn-call))
          ((cons name type) (car results))
          (type-conjunct `(,(atc-type-to-recognizer type wrld) ,theresult))
          (nonnil-conjunct? (and index? (list theresult)))
          (arraylength-conjunct?
           (b* (((unless (type-case type :pointer)) nil)
                (reftype (type-pointer->to type))
                ((unless (type-nonchar-integerp reftype)) nil)
                (reftype-array-length (pack (integer-type-to-fixtype reftype)
                                            '-array-length)))
             (list `(equal (,reftype-array-length ,theresult)
                           (,reftype-array-length ,name))))))
       (append (list type-conjunct)
               nonnil-conjunct?
               arraylength-conjunct?
               (atc-gen-fn-result-thm-aux2 (cdr results)
                                           (and index? (1+ index?))
                                           fn-call
                                           wrld))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-outer-bindings-and-hyps ((typed-formals atc-symbol-type-alistp)
                                         (compst-var symbolp)
                                         (fn-recursivep booleanp)
                                         (prec-objs atc-string-objinfo-alistp))
  :returns (mv (bindings doublet-listp)
               (hyps true-listp)
               (subst symbol-symbol-alistp
                      :hyp (atc-symbol-type-alistp typed-formals))
               (instantiation symbol-pseudoterm-alistp
                              :hyp (and (atc-symbol-type-alistp typed-formals)
                                        (symbolp compst-var))))
  :short "Generate the outer bindings,
          pointer hypotheses,
          pointer substitutions,
          and lemma instantiation,
          for a correctness theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "Both C functions and C loops have correctness theorems of the form
     @('(b* (<bindings>) ...)').
     Here we generate the @('<bindings>'),
     which we designate as `outer' since they are
     at the outermost level of the theorem's formula.
     We also generate some of the hypotheses
     used in the correctness theorems
     that relate to the bindings,
     explained below.
     We also generate a variable substitution, explained below.
     We also generate an instantiation
     for lemmas used in the hints of generated theorems;
     the instantiation is in alist form,
     so that we can use a readily available stronger type for it.")
   (xdoc::p
    "The (outer) bindings can be determined from
     the formals of the ACL2 function @('fn') that represents
     the C function or C loop.
     The bindings differ between C functions and loops,
     but there is also commonality,
     which justifies having this one ACL2 code generation function
     that handles both cases.")
   (xdoc::p
    "Consider a non-recursive @('fn'), which represents a C function.
     Its correctness theorem equates (roughly speaking)
     a call of @(tsee exec-fun) with a call of @('fn').
     However, while @('fn') takes arrays and structures in the heap
     as arguments,
     @(tsee exec-fun) takes pointers to those arrays and structures
     as arguments.
     So we introduce variables for the pointers,
     named after the formals of @('fn') that are arrays or structures:
     we add @('-PTR') to the formals of @('fn'),
     which should not cause name conflicts because
     the names of the formals must be portable C identifiers.
     For each array or structure formal @('a') of @('fn'),
     we generate a pointer variable @('a-ptr') as explained,
     along with a binding
     @('(a (read-object (value-pointer->designator a-ptr) compst))'):
     this binding relates the two variables,
     and lets us use the guard of @('fn') as hypothesis in the theorem,
     which uses @('a'),
     which the binding replaces with the array or structure
     pointed to by @('a-ptr').
     Along with this binding, we also generate hypotheses saying that
     @('a-ptr') is a top-level pointer of the appropriate type;
     the type is determined from the type of the formal @('a').
     Along with the binding and the hypotheses,
     we also generate an alist element @('(a . a-ptr)'),
     returned as part of the @('subst') result,
     that is used to generate the argument list of @(tsee exec-fun),
     by applying the substitution @('subst') to the formals of @('fn'):
     this way, @('a') gets substituted with @('a-ptr'),
     which is what we want since @(tsee exec-fun) takes pointers, not arrays.
     The substitution is also used to calculate the final computation state,
     in @(tsee atc-gen-cfun-final-compustate).")
   (xdoc::p
    "The treatment of arrays that are external objects is different.
     Similarly to heap arrays,
     @('fn') takes the whole external arrays as arguments.
     But @(tsee exec-fun) takes nothing for these as arguments:
     those arrays are found in the static storage of the computation state.
     We still need to generate a binding that relates
     the variables passed to @('fn') that contain these arrays
     to the computation state:
     we do it via bindings of the form
     @('((a (read-static-var (ident ...) compst)))'),
     which we generate here.
     We generate no hypotheses in this case:
     we do not introduce a pointer variable,
     so there is no need for hypotheses about it;
     the pointer is generated internally during symbolic execution,
     with an object designator for the variable in static storage.
     We generate no pointer substitution in this case:
     again, there is no pointer variable introduced here.
     Finally, we generate an instantiation pair consisting of
     the formal and the @('(read-static-var (ident ...) compst)') call.")
   (xdoc::p
    "The non-array non-structure formals of a non-recursive @('fn')
     do not cause any bindings, hypotheses, or substitutions to be generated.
     They are passed to both @(tsee exec-fun) and @('fn') in the theorem,
     and it is the guard of @('fn') that constrains them
     in the hypotheses of the theorem.")
   (xdoc::p
    "The treatment of a recursive @('fn') is a bit more complicated.
     The correctness theorem for the loop represented by @('fn')
     equates (roughly speaking)
     a call of @(tsee exec-stmt) with a call of @('fn').
     However, @(tsee exec-stmt) is called on a computation state,
     not on anything that corresponds to the formals of @('fn'),
     as is the case for a non-recursive @('fn') as explained above.
     There is still a correspondence, of course:
     the formals of @('fn') correspond to variables in the computation state.
     We consider separately
     the case of arrays or structures in the heap,
     the case of arrays in static storage,
     and the case of non-arrays and non-structures.")
   (xdoc::p
    "If @('a') is a non-array non-structure formal of a recursive @('fn'),
     it corresponds to @('(read-var <a> compst)'),
     where @('<a>') is the identifier derived from the name of @('a').
     Thus, in this case we generate the binding @('(a (read-var <a> compst))').
     Since no pointers are involved, in this case we generate
     no hypotheses and no substitutions;
     we generate an instantiation that instantiates
     the formal with @('(read-var <a> compst)').")
   (xdoc::p
    "If @('a') is a heap array or structure formal of a recursive @('fn'),
     we introduce an additional @('a-ptr') variable,
     similarly to the case of non-recursive @('fn').
     We generate two bindings @('(a-ptr (read-var <a> compst))')
     and @('(a (read-object (value-pointer->designator a-ptr) compst))'),
     in that order.
     The first binding serves to tie @('a-ptr')
     to the corresponding variable in the computation state,
     which has the name of @('a'), but it holds a pointer.
     The second binding is analogous in purpose
     to the case of a non-recursive @('fn') explained above:
     it lets us use the guard of @('fn'), which references @('a'),
     in the hypotheses of the generated theorem
     without having to make an explicit substitution,
     because the bindings are in fact doing the substitution.
     It should be clear why the two bindings have to be in that order;
     the bindings are put into a @(tsee b*),
     which enforces the order.
     We generate a substitution of @('a') with @('a-ptr'),
     for use by @(tsee atc-gen-loop-final-compustate)
     (not to calculate the arguments of @(tsee exec-fun),
     because no @(tsee exec-fun) call is involved in the theorem for loops.
     The instantiation combines @(tsee read-var) and @(tsee read-object).")
   (xdoc::p
    "If @('a') is an array in static storage,
     things are more similar to the case in which @('fn') is not recursive.
     The binding is with @(tsee read-static-var), i.e. the same.
     We generate a different hypothesis from all other cases:
     the hypothesis is that the variable is not in automatic storage,
     i.e. that it is found in static storage.
     This is necessary for theorems for C loops,
     because a @(tsee read-var) during execution cannot reach @(tsee add-frame)
     and be turned into @(tsee read-static-var) as done for C functions.
     This hypothesis is relieved in the correctness theorem
     of the non-recursive function that calls the recursive one:
     the symbolic execution for the non-recursive one
     can have @(tsee read-var) reach @(tsee add-frame)
     and turn that into @(tsee read-static-var).
     We generate no substitution, since there are no pointer variables.
     We generate an instantiation that instantiates the formal
     with the @(tsee read-static-var) call.")
   (xdoc::p
    "The reason for generating and using the described bindings in the theorems,
     as opposed to making the substitutions in the theorem's formula,
     is greater readability of the theorems.
     Particularly in the case of loop theorems,
     if @('a') occurs a few times in the guard,
     the guard with just @('a') in those occurrences is more readable than
     if all those occurrences are replaced with @('(read-var <a> compst)').")
   (xdoc::p
    "The lemma instantiation is similar to the bindings,
     but it only concerns the formals of @('fn'), not the @('a-ptr') variables.
     The instantiation is used on the guard and termination theorems of @('fn'),
     and therefore it can only concern the formals of @('fn').")
   (xdoc::p
    "There is an intentional discrepancy between the fact that
     an array pointer points to the whole array
     while the type of the pointer is the array element type.
     The reason is the approximate, but correct in our C subset,
     treatment of arrays and pointers discussed in @(tsee exec-arrsub)."))
  (b* (((when (endp typed-formals)) (mv nil nil nil nil))
       ((cons formal type) (car typed-formals))
       (formal-ptr (add-suffix-to-fn formal "-PTR"))
       (formal-objdes `(value-pointer->designator ,formal-ptr))
       (formal-id `(ident ',(symbol-name formal)))
       (pointerp (type-case type :pointer))
       (extobjp (assoc-equal (symbol-name formal) prec-objs))
       (bindings
        (if fn-recursivep
            (if pointerp
                (if extobjp
                    (list `(,formal
                            (read-static-var ,formal-id ,compst-var)))
                  (list `(,formal-ptr (read-var ,formal-id ,compst-var))
                        `(,formal (read-object ,formal-objdes ,compst-var))))
              (list `(,formal (read-var ,formal-id ,compst-var))))
          (if pointerp
              (if extobjp
                  (list `(,formal
                          (read-static-var ,formal-id ,compst-var)))
                (list `(,formal (read-object ,formal-objdes ,compst-var))))
            nil)))
       (subst (and pointerp
                   (not extobjp)
                   (list (cons formal formal-ptr))))
       (hyps (and pointerp
                  (if extobjp
                      (list `(not (var-autop ,formal-id ,compst-var)))
                    (list `(valuep ,formal-ptr)
                          `(value-case ,formal-ptr :pointer)
                          `(not (value-pointer-nullp ,formal-ptr))
                          `(equal (objdesign-kind
                                   (value-pointer->designator ,formal-ptr))
                                  :address)
                          `(equal (value-pointer->reftype ,formal-ptr)
                                  ,(type-to-maker (type-pointer->to type)))))))
       (inst (if fn-recursivep
                 (if pointerp
                     (if extobjp
                         (list
                          (cons formal
                                `(read-static-var ,formal-id ,compst-var)))
                       (list
                        (cons formal
                              `(read-object (value-pointer->designator
                                             (read-var ,formal-id ,compst-var))
                                            ,compst-var))))
                   (list
                    (cons formal
                          `(read-var ,formal-id ,compst-var))))
               (if pointerp
                   (if extobjp
                       (list
                        (cons formal
                              `(read-static-var ,formal-id ,compst-var)))
                     (list
                      (cons formal
                            `(read-object ,formal-objdes ,compst-var))))
                 nil)))
       ((mv more-bindings more-hyps more-subst more-inst)
        (atc-gen-outer-bindings-and-hyps (cdr typed-formals)
                                         compst-var
                                         fn-recursivep
                                         prec-objs)))
    (mv (append bindings more-bindings)
        (append hyps more-hyps)
        (append subst more-subst)
        (append inst more-inst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-object-disjoint-hyps ((pointer-vars symbol-listp))
  :returns (hyps true-listp)
  :short "Generate hypotheses saying that the pointers
          designate disjoint objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ACL2 functions that represent C functions and loops
     take and return whole arrays and structured as inputs:
     thus, the possible modification to each array or structure
     only applies to that array or structure.
     In the generated C code,
     arrays and structures are passed as pointers instead.
     If two of these pointers, for different arrays or structures in ACL2,
     were equal, then the C code would not be correct in general,
     because modifying one array or structure would also modify the other one:
     there is, in fact, just one array or structure,
     which both pointers point to,
     but here we are talking about the two different arrays or structures
     in the ACL2 representation.
     It is thus critical that the generated correctness theorems
     include the assumption that all the pointers are distinct.
     This is the case
     not only for the arrays and structures that may be modified,
     but also for the ones that may not:
     otherwise, we could not rely on the latter to be unmodified,
     during the symbolic execution proof.")
   (xdoc::p
    "We generate these hypotheses here,
     by going through the pointer variables involved in
     the correctness theorem of the C function or loop.
     More precisely, we generate hypotheses saying that
     the object designated by the pointers are pairwise disjoint."))
  (b* (((when (endp pointer-vars)) nil)
       (var (car pointer-vars))
       (hyps (loop$ for var2 in (cdr pointer-vars)
                    collect `(object-disjointp
                              (value-pointer->designator ,var)
                              (value-pointer->designator ,var2))))
       (more-hyps (atc-gen-object-disjoint-hyps (cdr pointer-vars))))
    (append hyps more-hyps))
  :prepwork ((local (in-theory (enable acl2::loop-book-theory)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-filter-exec-fun-args ((formals symbol-listp)
                                  (prec-objs atc-string-objinfo-alistp))
  :returns (args symbol-listp :hyp (symbol-listp formals))
  :short "Filter external objects out of the formals,
          for passing to @(tsee exec-fun),"
  :long
  (xdoc::topstring
   (xdoc::p
    "In the generated correctness theorem for each non-recursive function,
     we generally pass to @(tsee exec-fun)
     an argument for each formal of the function.
     Except for formals that represent external objects:
     those are accessed in the computation state.
     Thus, here we filter, out of a list of formals,
     the ones that represent external objects."))
  (b* (((when (endp formals)) nil)
       (formal (car formals)))
    (if (assoc-equal (symbol-name formal) prec-objs)
        (atc-filter-exec-fun-args (cdr formals) prec-objs)
      (cons formal (atc-filter-exec-fun-args (cdr formals) prec-objs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfun-final-compustate ((affect symbol-listp)
                                       (typed-formals atc-symbol-type-alistp)
                                       (subst symbol-symbol-alistp)
                                       (compst-var symbolp)
                                       (prec-objs atc-string-objinfo-alistp))
  :returns (term "An untranslated term.")
  :short "Generate a term representing the final computation state
          after the execution of a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The correctness theorem of a C function says that
     executing the function on a generic computation state
     (satisfying conditions in the hypotheses of the theorem)
     and on generic arguments
     yields an optional result (absent if the function is @('void'))
     and a computation state obtained by modifying
     zero or more arrays and structures in the computation state.
     These are the arrays and structures affected by the C function,
     which the correctness theorem binds to the results of
     the ACL2 function that represents the C function.
     The modified computation state is expressed as
     a nest of @(tsee write-object) and @(tsee write-static-var) calls,
     based on whether the affected object are in the heap or in static storage.
     This ACL2 code here generates that nest.")
   (xdoc::p
    "The parameter @('affect') passed to this code
     consists of the formals of @('fn') that represent arrays and structures
     affected by the body of the ACL2 function that represents the C function.
     The parameter @('subst') is
     the result of @(tsee atc-gen-outer-bindings-and-hyps)
     that maps array and structure formals of the ACL2 function
     to the corresponding pointer variables used by the correctness theorems.
     Thus, we go through @('affect'),
     looking up the corresponding pointer variables in @('subst'),
     and we construct
     each nested @(tsee write-object) call,
     which needs both a pointer and an array or structure;
     we distinguish between arrays and structures
     via the types of the formals.
     This is the case for arrays and structures in the heap;
     for arrays in static storage,
     we generate a call of @(tsee write-static-var),
     and there are no pointers involved.")
   (xdoc::p
    "Note that, in the correctness theorem,
     the new array and structure variables are bound to
     the possibly modified arrays and structures returned by the ACL2 function:
     these new array and structure variables are obtained by adding @('-NEW')
     to the corresponding formals of the ACL2 function;
     these new names should not cause any conflicts,
     because the names of the formals must be portable C identifiers."))
  (b* (((when (endp affect)) compst-var)
       (formal (car affect))
       (type (cdr (assoc-eq formal typed-formals)))
       ((when (not type))
        (raise "Internal error: formal ~x0 not found." formal))
       ((unless (type-case type :pointer))
        (raise "Internal error: affected formal ~x0 has type ~x1."
               formal type)))
    (if (consp (assoc-equal (symbol-name formal) prec-objs))
        `(write-static-var (ident ,(symbol-name formal))
                           ,(add-suffix-to-fn formal "-NEW")
                           ,(atc-gen-cfun-final-compustate (cdr affect)
                                                           typed-formals
                                                           subst
                                                           compst-var
                                                           prec-objs))
      `(write-object (value-pointer->designator ,(cdr (assoc-eq formal subst)))
                     ,(add-suffix-to-fn formal "-NEW")
                     ,(atc-gen-cfun-final-compustate (cdr affect)
                                                     typed-formals
                                                     subst
                                                     compst-var
                                                     prec-objs))))
  :prepwork
  ((defrulel lemma
     (implies (symbol-symbol-alistp x)
              (alistp x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfun-correct-thm ((fn symbolp)
                                  (typed-formals atc-symbol-type-alistp)
                                  (type typep)
                                  (affect symbol-listp)
                                  (prec-fns atc-symbol-fninfo-alistp)
                                  (prec-tags atc-string-taginfo-alistp)
                                  (prec-objs atc-string-objinfo-alistp)
                                  (prog-const symbolp)
                                  (fn-thms symbol-symbol-alistp)
                                  (fn-fun-env-thm symbolp)
                                  (limit pseudo-termp)
                                  state)
  :returns (mv (local-events pseudo-event-form-listp)
               (exported-events pseudo-event-form-listp)
               (name symbolp :hyp (symbol-symbol-alistp fn-thms)))
  :short "Generate the correctness theorem for a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "In a computation state @('compst'),
     the execution of the C function is expressed by calling @(tsee exec-fun)
     on the name of @('fn'),
     the formals of @('fn'),
     the computation state @('compst'),
     the function environment for the translation unit,
     and a suitably large limit (more on this below).
     In this generated theorem,
     the first result of @(tsee exec-fun) is equated to
     either (i) the first (possibly only) result of
     a call of @('fn') when it represents a non-@('void') C function,
     or (ii) @('nil') when @('fn') represents a @('void') C function.
     The second result of @(tsee exec-fun) is equated to
     the computation state
     calculated by @(tsee atc-gen-cfun-final-compustate).")
   (xdoc::p
    "The function @('fn') returns
     an optional C result and zero or more modified arrays and structures.
     If it returns a C result (i.e. if the C function is not @('void')),
     we bind a result variable to it;
     the value is @('nil') if the C function is @('void').
     We also bind the formals that are arrays or structures
     to the (other or only) results of @('fn') (if any).
     We actually use new variables for the latter,
     for greater clarity in the theorem formulation:
     the new variables are obtained by adding @('-NEW')
     to the corresponding array and structure formals of @('fn');
     these new names should not cause any conflicts,
     because the names of the formals must be portable C identifiers.")
   (xdoc::p
    "The guard of @('fn') is used as hypothesis,
     along with the fact that @('compst') is a computation state.")
   (xdoc::p
    "We use a variable for the function environment,
     which we equate to the translation unit's function environment
     in a hypothesis.
     Note that, when we execute the ACL2 code in this function,
     we do not have the function environment
     of the generated translation unit yet,
     because we generate these correctness theorems
     along with the function definitions that form the translation unit
     (currently we could generate these theorems after the translation unit,
     but we prefer to do them at the same time for easier future extensions,
     in which we may generate ``smaller'' theorems,
     possibly for subterms/subexpressions/substatements).
     Thus, we cannot use a quoted constant for the function environment here.
     The reason why we introduce a variable and equate it in the hypothesis,
     as opposed to using @('(init-fun-env <program>)')
     directly as argument of @(tsee exec-fun),
     is that we want to use this theorem as a rewrite rule,
     and using a variable makes the rule easier to match with,
     in particular since the @(tsee init-fun-env) call gets rewritten
     via the theorem about @(tsee init-fun-env).")
   (xdoc::p
    "The limit passed to @(tsee exec-fun) is a variable,
     which is assumed (in a hypothesis of the generated theorem)
     to be no smaller than a value
     that is calculated by the code generation code
     as sufficient to run @(tsee exec-fun) to completion.")
   (xdoc::p
    "The proof is a symbolic execution of the generated translation unit,
     which is a constant: see @(see atc-symbolic-execution-rules).
     The proof is carried out in the theory that consists of exactly
     the general rules in @(tsee *atc-all-rules*),
     some structure-specific rules that are similar to
     rules for arrays in @(tsee *atc-all-rules*),
     plus the definition of @(tsee not) (more on this below),
     plus the definition of @('fn') (clearly),
     plus the theorems about the results of the functions called by @('fn'),
     plust the type prescriptions of the functions called by @('fn'),
     plus the correctness theorems of the functions called by @('fn'),
     plus the theorems asserting that
     the measures of the called recursive functions are naturals,
     plus the theorem about the current function in the function environment;
     here `called' means `directly called'.
     During symbolic execution, the initial limit for @('fn')
     is progressively decremented,
     so by the time we get to functions called by @('fn')
     it will have different symbolic values from the initial variable;
     thus, we need to match that to the variable @('limit')
     in the correctness theorems for the callees,
     which are used as rewrite rules to turn calls of @(tsee exec-fun)
     into calls of the corresponding ACL2 functions.
     These will thus match the calls in the definition of @('fn'),
     and the called functions can stay disabled in the proof.
     The theorems about the called functions' results
     are needed to exclude, in the proof, the case that
     these functions return errors.
     The type prescriptions of the callable functions
     are needed to discharge some proof subgoal that arise.
     We enable @(tsee not) because, without it,
     we have found at least one case in which some ACL2 heuristic defeats
     what should be a propositional inference;
     the issue is related to clausification,
     and enabling @(tsee not) seems to overcome the issue,
     at least in that case we found.")
   (xdoc::p
    "Furthermore, we generate a @(':use') hint
     to augment the theorem's formula with the guard theorem of @('fn'),
     with the pointer arguments replaced by
     the dereferenced arrays and structures.
     This is critical to ensure that the symbolic execution of the C operators
     does not split on the error cases:
     the fact that @('fn') is guard-verified
     ensures that @(tsee add-sint-sint) and similar functions are always called
     on values such that the exact result fit into the type,
     which is the same condition under which the dynamic semantics
     does not error on the corresponding operators.")
   (xdoc::p
    "We also generate a hint to expand all lambdas (i.e. beta reduction).
     We found at least one instance in which ACL2's heuristics
     were preventing a lambda expansion that was preventing a proof.")
   (xdoc::p
    "Given that we pass correctness theorems for the called functions,
     we expect that the opener rule for @(tsee exec-fun)
     only applies to the call of the function that this theorem refers to,
     because the correctness theorems come later in the ACL2 history
     and thus are tried first.")
   (xdoc::p
    "We use @(tsee b*) bindings in parts of the theorem
     to make certain variable substitution.
     Using bindings results in more readable formulas, in general,
     than generating terms with the substitutions applied,
     particularly if the same substituted variable occurs more than once.
     With the bindings, we let ACL2 perform the substitution at proof time.")
   (xdoc::p
    "If @('fn') has conditional (i.e. @(tsee if)s),
     the C function has corresponding (expression and statement) conditionals.
     During the proof, all these condtionals, in @('fn') and in the C function,
     may cause case splits, which make the proof slow.
     In an attempt to improve speed,
     we perform the symbolic execution execution of the C function
     while keeping @('fn') closed,
     so that @('fn') does not cause case splits during the symbolic execution.
     Then, once we reach stability (see @(tsee stable-under-simplificationp)),
     we open @('fn'), which may cause case splits, and complete the proof.
     The second part of the proof probably does not need
     all the rules from the first part, which for now we use for simplicity;
     so we should be able to use simpler hints there eventually.")
   (xdoc::p
    "This theorem is not generated if @(':proofs') is @('nil')."))
  (b* ((wrld (w state))
       (name (cdr (assoc-eq fn fn-thms)))
       (formals (strip-cars typed-formals))
       (compst-var (genvar$ 'atc "COMPST" nil formals state))
       (fenv-var (genvar$ 'atc "FENV" nil formals state))
       (limit-var (genvar$ 'atc "LIMIT" nil formals state))
       (result-var (if (type-case type :void)
                       nil
                     (genvar$ 'atc "RESULT" nil formals state)))
       ((mv formals-bindings hyps subst instantiation)
        (atc-gen-outer-bindings-and-hyps typed-formals
                                         compst-var
                                         nil
                                         prec-objs))
       (diff-pointer-hyps
        (atc-gen-object-disjoint-hyps (strip-cdrs subst)))
       (hyps `(and (compustatep ,compst-var)
                   (equal ,fenv-var
                          (init-fun-env (preprocess ,prog-const)))
                   (integerp ,limit-var)
                   (>= ,limit-var ,limit)
                   ,@hyps
                   ,@diff-pointer-hyps
                   ,(untranslate$ (uguard+ fn wrld) nil state)))
       (exec-fun-args (fsublis-var-lst subst
                                       (atc-filter-exec-fun-args formals
                                                                 prec-objs)))
       (affect-new (acl2::add-suffix-to-fn-lst affect "-NEW"))
       (fn-results (append (if (type-case type :void)
                               nil
                             (list result-var))
                           affect-new))
       (fn-binder (if (endp (cdr fn-results))
                      (car fn-results)
                    `(mv ,@fn-results)))
       (final-compst
        (atc-gen-cfun-final-compustate affect
                                       typed-formals
                                       subst
                                       compst-var
                                       prec-objs))
       (concl `(equal (exec-fun (ident ,(symbol-name fn))
                                (list ,@exec-fun-args)
                                ,compst-var
                                ,fenv-var
                                ,limit-var)
                      (b* ((,fn-binder (,fn ,@formals)))
                        (mv ,result-var ,final-compst))))
       (formula `(b* (,@formals-bindings) (implies ,hyps ,concl)))
       (called-fns (all-fnnames (ubody+ fn wrld)))
       (not-error-thms (atc-string-taginfo-alist-to-not-error-thms prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (value-kind-thms (atc-string-taginfo-alist-to-value-kind-thms prec-tags))
       (result-thms
        (atc-symbol-fninfo-alist-to-result-thms prec-fns called-fns))
       (struct-reader-return-thms
        (atc-string-taginfo-alist-to-reader-return-thms prec-tags))
       (struct-writer-return-thms
        (atc-string-taginfo-alist-to-writer-return-thms prec-tags))
       (correct-thms
        (atc-symbol-fninfo-alist-to-correct-thms prec-fns called-fns))
       (measure-thms
        (atc-symbol-fninfo-alist-to-measure-nat-thms prec-fns called-fns))
       (type-prescriptions-called
        (loop$ for called in (strip-cars prec-fns)
               collect `(:t ,called)))
       (type-prescriptions-struct-readers
        (loop$ for reader in (atc-string-taginfo-alist-to-readers prec-tags)
               collect `(:t ,reader)))
       (type-of-value-thms
        (atc-string-taginfo-alist-to-type-of-value-thms prec-tags))
       (flexiblep-thms
        (atc-string-taginfo-alist-to-flexiblep-thms prec-tags))
       (member-read-thms
        (atc-string-taginfo-alist-to-member-read-thms prec-tags))
       (member-write-thms
        (atc-string-taginfo-alist-to-member-write-thms prec-tags))
       (extobj-recognizers (atc-string-objinfo-alist-to-recognizers prec-objs))
       (hints `(("Goal"
                 :in-theory (union-theories
                             (theory 'atc-all-rules)
                             '(,@not-error-thms
                               ,@valuep-thms
                               ,@value-kind-thms
                               not
                               ,@result-thms
                               ,@struct-reader-return-thms
                               ,@struct-writer-return-thms
                               ,@type-of-value-thms
                               ,@flexiblep-thms
                               ,@member-read-thms
                               ,@member-write-thms
                               ,@type-prescriptions-called
                               ,@type-prescriptions-struct-readers
                               ,@extobj-recognizers
                               ,@correct-thms
                               ,@measure-thms
                               ,fn-fun-env-thm))
                 :use (:instance (:guard-theorem ,fn)
                       :extra-bindings-ok ,@(alist-to-doublets instantiation))
                 :expand (:lambdas))
                (and stable-under-simplificationp
                     '(:in-theory (union-theories
                                   (theory 'atc-all-rules)
                                   '(,fn
                                     ,@not-error-thms
                                     ,@valuep-thms
                                     ,@value-kind-thms
                                     not
                                     ,@result-thms
                                     ,@struct-reader-return-thms
                                     ,@struct-writer-return-thms
                                     ,@type-of-value-thms
                                     ,@flexiblep-thms
                                     ,@member-read-thms
                                     ,@member-write-thms
                                     ,@type-prescriptions-called
                                     ,@type-prescriptions-struct-readers
                                     ,@extobj-recognizers
                                     ,@correct-thms
                                     ,@measure-thms
                                     ,fn-fun-env-thm))))))
       ((mv local-event exported-event)
        (evmac-generate-defthm name
                               :formula formula
                               :hints hints
                               :enable nil)))
    (mv (list local-event) (list exported-event) name))
  :guard-hints
  (("Goal"
    :in-theory
    (enable acl2::symbol-listp-of-strip-cdrs-when-symbol-symbol-alistp
            acl2::symbol-alistp-when-symbol-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-formal-pointerp ((formal symbolp)
                             (typed-formals atc-symbol-type-alistp))
  :returns (yes/no booleanp)
  :short "Check if a formal parameter has a C pointer type."
  (b* ((pair (assoc-eq (symbol-fix formal)
                       (atc-symbol-type-alist-fix typed-formals))))
    (and (consp pair)
         (type-case (cdr pair) :pointer)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist atc-formal-pointer-listp (x typed-formals)
  :guard (and (symbol-listp x)
              (atc-symbol-type-alistp typed-formals))
  :short "Lift @(tsee atc-formal-pointerp) to lists."
  (atc-formal-pointerp x typed-formals)
  :true-listp t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-find-affected ((fn symbolp)
                           (term pseudo-termp)
                           (typed-formals atc-symbol-type-alistp)
                           (prec-fns atc-symbol-fninfo-alistp)
                           (ctx ctxp)
                           state)
  :returns (mv erp
               (affected symbol-listp
                         :hyp (atc-symbol-type-alistp typed-formals))
               state)
  :short "Find the variables affected by a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used on the body of each non-recursive target function @('fn'),
     in order to determine the variables affected by it,
     according to the nomenclature in the user documentation.
     We visit the leaves of the term
     according to the @(tsee if) and @(tsee let) structure,
     and ensure that they all have the same form,
     which must be one of the following forms:")
   (xdoc::ul
    (xdoc::li
     "A call of a (recursive or non-recursive) target function @('fn0')
      that precedes @('fn') in the list of targets.
      In this case, @('term') affects the same variables as @('fn0').
      We use @(tsee atc-check-cfun-call) and @(tsee atc-check-loop-call)
      to check if the term is a call of a target function
      and to retrieve that function's affected variables:
      we pass @('nil') as the variable-term alist,
      because it does not change the returned affected variables,
      which is the only thing we care about here,
      ignoring all the other results.")
    (xdoc::li
     "A formal parameter @('var') of @('fn') with pointer type.
      In this case, @('term') affects the list of variables @('(var)').")
    (xdoc::li
     "A term @('ret') that is not a call of @('fn0') as above
      and is not a formal parameter of @('fn') of pointer type.
      In this case, @('term') affects no variables.")
    (xdoc::li
     "A term @('(mv var1 ... varn)') where each @('vari') is
      a formal parameter of the function that has pointer type.
      In this case, @('term') affects
      the list of variables @('(var1 ... varn)').")
    (xdoc::li
     "A term @('(mv ret var1 ... varn)') where each @('vari') is
      a formal parameter of the function that has pointer type
      and @('ret') is not.
      In this case, @('term') affects
      the list of variables @('(var1 ... varn)')."))
   (xdoc::p
    "In checking that the terms at the leaves have the same form,
     we allow @('ret') to vary, but the other parts must coincide.")
   (xdoc::p
    "When we encounter @(tsee if)s with @(tsee mbt) or @(tsee mbt$) tests,
     we recursively process the `then' branch, skipping the `else' branch.
     This is because only the `then' branch represents C code."))
  (b* (((mv okp test then else) (fty-check-if-call term))
       ((when okp)
        (b* (((mv mbtp &) (check-mbt-call test))
             ((when mbtp) (atc-find-affected fn
                                             then
                                             typed-formals
                                             prec-fns
                                             ctx
                                             state))
             ((mv mbt$p &) (check-mbt$-call test))
             ((when mbt$p) (atc-find-affected fn
                                              then
                                              typed-formals
                                              prec-fns
                                              ctx
                                              state))
             ((er then-affected) (atc-find-affected fn
                                                    then
                                                    typed-formals
                                                    prec-fns
                                                    ctx
                                                    state))
             ((er else-affected) (atc-find-affected fn
                                                    else
                                                    typed-formals
                                                    prec-fns
                                                    ctx
                                                    state)))
          (if (equal then-affected else-affected)
              (acl2::value then-affected)
            (er-soft+ ctx t nil
                      "When generating code for function ~x0, ~
                       an IF branch affects variables ~x1, ~
                       while the other branch affects variables ~x2: ~
                       this is disallowed."
                      fn then-affected else-affected))))
       ((mv okp & body &) (fty-check-lambda-call term))
       ((when okp) (atc-find-affected fn
                                      body
                                      typed-formals
                                      prec-fns
                                      ctx
                                      state))
       ((mv okp & & & & affected &)
        (atc-check-cfun-call term nil prec-fns (w state)))
       ((when okp) (acl2::value affected))
       ((mv okp & & & affected & &)
        (atc-check-loop-call term nil prec-fns))
       ((when okp) (acl2::value affected))
       ((when (pseudo-term-case term :var))
        (b* ((var (pseudo-term-var->name term)))
          (if (atc-formal-pointerp var typed-formals)
              (acl2::value (list var))
            (acl2::value nil))))
       ((mv okp terms) (fty-check-list-call term))
       ((when okp)
        (cond ((and (symbol-listp terms)
                    (atc-formal-pointer-listp terms typed-formals))
               (acl2::value terms))
              ((and (symbol-listp (cdr terms))
                    (atc-formal-pointer-listp (cdr terms) typed-formals))
               (acl2::value (cdr terms)))
              (t (er-soft+ ctx t nil
                           "When generating code for function ~x0, ~
                            a term ~x1 was encountered that ~
                            returns multiple values but they, ~
                            or at least all of them except the first one, ~
                            are not all formal parameters of ~x0 ~
                            of pointer type."
                           fn term)))))
    (acl2::value nil))
  :measure (pseudo-term-count term)
  :prepwork
  ((local (in-theory
           (enable symbol-listp-of-strip-cars-when-atc-symbol-type-alistp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fundef ((fn symbolp)
                        (prec-fns atc-symbol-fninfo-alistp)
                        (prec-tags atc-string-taginfo-alistp)
                        (prec-objs atc-string-objinfo-alistp)
                        (proofs booleanp)
                        (prog-const symbolp)
                        (init-fun-env-thm symbolp)
                        (fn-thms symbol-symbol-alistp)
                        (print evmac-input-print-p)
                        (names-to-avoid symbol-listp)
                        (ctx ctxp)
                        state)
  :guard (not (eq fn 'quote))
  :returns (mv erp
               (val (tuple (fundef fundefp)
                           (local-events pseudo-event-form-listp)
                           (exported-events pseudo-event-form-listp)
                           (updated-prec-fns atc-symbol-fninfo-alistp)
                           (updated-names-to-avoid symbol-listp)
                           val)
                    :hyp (and (atc-symbol-fninfo-alistp prec-fns)
                              (symbol-listp names-to-avoid)))
               state)
  :short "Generate a C function definition
          from a non-recursive ACL2 function, with accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return local and exported events for the theorems about
     the correctness of the C function definition.")
   (xdoc::p
    "We extend the alist @('prec-fns') with information about the function.")
   (xdoc::p
    "We use the type of the value returned by the statement for the body
     as the result type of the C function.")
   (xdoc::p
    "For the limit, we need 1 to go from @(tsee exec-fun) to @(tsee exec-stmt),
     another 1 from there to @(tsee exec-block-item-list)
     in the @(':compound') case,
     and then we use the limit for the block."))
  (b* (((acl2::fun (irr))
        (list (ec-call (fundef-fix :irrelevant)) nil nil nil nil))
       (name (symbol-name fn))
       ((unless (paident-stringp name))
        (er-soft+ ctx t (irr)
                  "The symbol name ~s0 of the function ~x1 ~
                   must be a portable ASCII C identifier, but it is not."
                  name fn))
       (wrld (w state))
       ((er typed-formals :iferr (irr))
        (atc-typed-formals fn prec-tags prec-objs ctx state))
       ((er params :iferr (irr))
        (atc-gen-param-declon-list typed-formals fn prec-objs ctx state))
       (body (ubody+ fn wrld))
       ((er affect :iferr (irr))
        (atc-find-affected fn body typed-formals prec-fns ctx state))
       ((er (stmt-gout body) :iferr (irr))
        (atc-gen-stmt body
                      (make-stmt-gin
                       :var-term-alist nil
                       :inscope (list typed-formals)
                       :loop-flag nil
                       :affect affect
                       :fn fn
                       :prec-fns prec-fns
                       :prec-tags prec-tags
                       :prec-objs prec-objs
                       :thm-index 1
                       :names-to-avoid names-to-avoid
                       :proofs proofs)
                      ctx
                      state))
       ((when (and (type-case body.type :void)
                   (not affect)))
        (raise "Internal error: ~
                the function ~x0 returns void and affects no variables."
               fn)
        (acl2::value (irr)))
       ((unless (or (type-nonchar-integerp body.type)
                    (type-case body.type :struct)
                    (type-case body.type :void)))
        (raise "Internal error: ~
                the function ~x0 has return type ~x1."
               fn body.type)
        (acl2::value (irr)))
       (id (make-ident :name name))
       ((mv tyspec &) (ident+type-to-tyspec+declor id body.type))
       (fundef (make-fundef :tyspec tyspec
                            :declor (make-fun-declor-base :name id
                                                          :params params)
                            :body body.items))
       (finfo (fun-info-from-fundef fundef))
       (limit `(binary-+ '2 ,body.limit))
       ((mv local-events
            exported-events
            fn-fun-env-thm
            fn-result-thm
            fn-correct-thm
            names-to-avoid)
        (if proofs
            (b* (((mv fn-guard-event
                      & ; fn-guard
                      names-to-avoid)
                  (atc-gen-fn-guard fn body.names-to-avoid state))
                 ((mv fn-fun-env-events
                      fn-fun-env-thm
                      names-to-avoid)
                  (atc-gen-cfun-fun-env-thm fn
                                            prog-const
                                            finfo
                                            init-fun-env-thm
                                            names-to-avoid
                                            wrld))
                 ((mv fn-result-events
                      fn-result-thm
                      names-to-avoid)
                  (atc-gen-fn-result-thm fn
                                         body.type
                                         affect
                                         typed-formals
                                         prec-fns
                                         prec-tags
                                         prec-objs
                                         names-to-avoid
                                         state))
                 ((mv fn-correct-local-events
                      fn-correct-exported-events
                      fn-correct-thm)
                  (atc-gen-cfun-correct-thm fn
                                            typed-formals
                                            body.type
                                            affect
                                            prec-fns
                                            prec-tags
                                            prec-objs
                                            prog-const
                                            fn-thms
                                            fn-fun-env-thm
                                            limit
                                            state))
                 (progress-start?
                  (and (evmac-input-print->= print :info)
                       `((cw-event "~%Generating the proofs for ~x0..." ',fn))))
                 (progress-end? (and (evmac-input-print->= print :info)
                                     `((cw-event " done.~%"))))
                 (local-events (append body.events
                                       progress-start?
                                       (list fn-guard-event)
                                       fn-fun-env-events
                                       fn-result-events
                                       fn-correct-local-events
                                       progress-end?))
                 (exported-events fn-correct-exported-events))
              (mv local-events
                  exported-events
                  fn-fun-env-thm
                  fn-result-thm
                  fn-correct-thm
                  names-to-avoid))
          (mv nil nil nil nil nil names-to-avoid)))
       (info (make-atc-fn-info
              :out-type body.type
              :in-types (strip-cdrs typed-formals)
              :loop? nil
              :affect affect
              :result-thm fn-result-thm
              :correct-thm fn-correct-thm
              :measure-nat-thm nil
              :fun-env-thm fn-fun-env-thm
              :limit limit)))
    (acl2::value (list fundef
                       local-events
                       exported-events
                       (acons fn info prec-fns)
                       names-to-avoid)))
  ///

  (more-returns
   (val true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-measure-fn ((fn symbolp)
                                 (names-to-avoid symbol-listp)
                                 state)
  :guard (irecursivep+ fn (w state))
  :returns (mv (event pseudo-event-formp)
               (name symbolp)
               (formals symbol-listp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate a measure function for a recursive target function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The correctness theorem for a loop involves
     the measure of the loop function.
     The measure may be a complex term.
     An early version of ATC was using the measure terms
     directly in the generated theorems,
     but that caused proof failures sometimes,
     due to ACL2 sometimes modifying those measure terms during a proof
     (e.g. due to equalities involving measure subterms
     arising from case analyses):
     after the terms were modified,
     some of the generated theorems about the measure terms
     no longer apply, making the proof fail.
     Thus, we ``protect'' the measure terms from modifications
     by generating functions for them,
     and using those functions in the generated theorems.")
   (xdoc::p
    "The code of this ACL2 function generates a measure function
     for the recursive target function @('fn').
     The funcion is not guard-verified,
     because its is only logical.
     It is important that we take,
     as formal parameters of the generated measure function,
     only the variables that occur in the measure term.
     This facilitates the generation of
     the loop function's termination theorem
     expressed over the  generated measure function."))
  (b* ((wrld (w state))
       (name (packn-pos (list 'measure-of- fn) fn))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name 'function names-to-avoid wrld))
       ((when (eq name 'quote))
        (raise "Internal error: name is QUOTE.")
        (mv '(_) nil nil nil))
       (measure-term (measure+ fn wrld))
       (measure-vars (all-vars measure-term))
       ((mv & event)
        (evmac-generate-defun
         name
         :formals measure-vars
         :body (untranslate$ measure-term nil state)
         :verify-guards nil
         :enable nil)))
    (mv event name measure-vars names-to-avoid))
  ///

  (defret atc-gen-loop-measure-fn-name-not-quote
    (not (equal name 'quote))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atc-gen-loop-tthm-formula
  :short "Generate the formula for the loop termination theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is obtained from the loop function's termination theorem,
     transformed as follows.")
   (xdoc::p
    "The @(tsee o<) relation is replaced with @(tsee <).
     This is justified by the fact that the measure yields a natural number,
     as guaranteed by the applicability condition.")
   (xdoc::p
    "Furthermore, the measure term is replaced
     with a call of the generated measure function.
     More precisely, this is done in every term of the form @('(o< A B)')
     (at the same replacing @(tsee o<) with @(tsee <) as mentioned above),
     where we expect @('B') to be the measure term,
     and @('A') to be the instantiation of the measure term
     to one of the recursive calls of the loop function.
     We replace @('B') with a generic call of the measure function,
     and @('A') with an instantiated call of the measure function;
     we obtain the instantiation by matching @('B') to @('A').
     It is not yet clear whether this approach will work in all cases."))

  (define atc-gen-loop-tthm-formula ((term pseudo-termp)
                                     (fn symbolp)
                                     (measure-of-fn symbolp)
                                     (measure-formals symbol-listp)
                                     (ctx ctxp)
                                     state)
    :guard (not (eq measure-of-fn 'quote))
    :returns (mv erp
                 new-term ; PSEUDO-TERMP proved below
                 state)
    (b* (((when (variablep term)) (acl2::value term))
         ((when (fquotep term)) (acl2::value term))
         (term-fn (ffn-symb term))
         ((when (eq term-fn 'o<))
          (b* ((meas-gen (fargn term 2))
               (meas-inst (fargn term 1))
               ((mv okp subst) (one-way-unify$ meas-gen meas-inst state))
               ((when (not okp))
                (er-soft+ ctx t nil
                          "Failed to match istantiated measure ~x0 ~
                           to general measure ~x1 of function ~x2."
                          meas-inst meas-gen fn))
               (measure-args (fty-fsublis-var-lst subst measure-formals)))
            (acl2::value
             `(< (,measure-of-fn ,@measure-args)
                 (,measure-of-fn ,@measure-formals)))))
         ((er new-args :iferr nil)
          (atc-gen-loop-tthm-formula-lst (fargs term)
                                         fn
                                         measure-of-fn
                                         measure-formals
                                         ctx
                                         state)))
      (acl2::value (fcons-term term-fn new-args))))

  (define atc-gen-loop-tthm-formula-lst ((terms pseudo-term-listp)
                                         (fn symbolp)
                                         (measure-of-fn symbolp)
                                         (measure-formals symbol-listp)
                                         (ctx ctxp)
                                         state)
    :guard (not (eq measure-of-fn 'quote))
    :returns (mv erp
                 new-terms ; PSEUDO-TERM-LISTP proved below
                 state)
    (b* (((when (endp terms)) (acl2::value nil))
         ((er new-term :iferr nil)
          (atc-gen-loop-tthm-formula (car terms)
                                     fn
                                     measure-of-fn
                                     measure-formals
                                     ctx
                                     state))
         ((er new-terms) (atc-gen-loop-tthm-formula-lst (cdr terms)
                                                        fn
                                                        measure-of-fn
                                                        measure-formals
                                                        ctx
                                                        state)))
      (acl2::value (cons new-term new-terms))))

  ///

  (defret-mutual len-of-atc-gen-loop-tthm-formula/lst
    (defret len-of-atc-gen-loop-tthm-formula
      t
      :rule-classes nil
      :fn atc-gen-loop-tthm-formula)
    (defret len-of-atc-gen-loop-tthm-formula-lst
      (implies (not erp)
               (equal (len new-terms)
                      (len terms)))
      :fn atc-gen-loop-tthm-formula-lst))

  (defret-mutual return-types-of-atc-gen-loop-tthm-formula/lst
    (defret pseudo-termp-of-atc-gen-loop-tthm-formula
      (pseudo-termp new-term)
      :hyp (and (pseudo-termp term)
                (symbolp measure-of-fn)
                (not (eq measure-of-fn 'quote))
                (symbol-listp measure-formals))
      :fn atc-gen-loop-tthm-formula)
    (defret pseudo-termp-of-atc-gen-loop-tthm-formula-lst
      (pseudo-term-listp new-terms)
      :hyp (and (pseudo-term-listp terms)
                (symbolp measure-of-fn)
                (not (eq measure-of-fn 'quote))
                (symbol-listp measure-formals))
      :fn atc-gen-loop-tthm-formula-lst)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-exec-stmt-while-for-loop ((fn symbolp)
                                          (loop-stmt stmtp)
                                          (prog-const symbolp)
                                          (names-to-avoid symbol-listp)
                                          (wrld plist-worldp))
  :guard (and (irecursivep+ fn wrld)
              (stmt-case loop-stmt :while))
  :returns (mv (events pseudo-event-form-listp)
               (exec-stmt-while-for-fn symbolp)
               (exec-stmt-while-for-fn-thm symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate a version of @(tsee exec-stmt-while)
          specialized to the loop represented by @('fn')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The correctness theorem for a loop says that
     the execution of the loop (via @(tsee exec-stmt-while))
     is suitably equivalent to
     the corresponding ACL2 recursive function @('fn').
     The theorem is proved by induction, unsurprisingly.
     However, due to the form in which the function appears in the theorem,
     namely that the function is not applied to ACL2 variables,
     we cannot use the function's induction scheme.
     But we cannot readily use
     the induction scheme of the execution functions
     of the C dynamic semantics,
     or at least it looks cumbersome to do so,
     because there are several of them, mutually recursive.")
   (xdoc::p
    "What we really need is an induction scheme related to the loop.
     Thus we introduce a local function that is like @(tsee exec-stmt-while)
     but specialized to the loop generated from @('fn');
     this function is singly recursive, providing the needed induction scheme.
     The function does not need to be guard-verified,
     because it is only used for logic.
     We also generate a theorem saying that this new function
     is equivalent to @(tsee exec-stmt-while) applied to the loop;
     this is critical, because eventually the proof must be
     about the execution functions of the C dynamic semantics.
     For robustness, the termination proof for this new function,
     and the proof of the associated theorem,
     are carried out in exactly specified theories
     that should always work."))
  (b* ((loop-test (stmt-while->test loop-stmt))
       (loop-body (stmt-while->body loop-stmt))
       (exec-stmt-while-for-fn
        (packn-pos (list 'exec-stmt-while-for- fn) fn))
       ((mv exec-stmt-while-for-fn names-to-avoid)
        (fresh-logical-name-with-$s-suffix exec-stmt-while-for-fn
                                           'function
                                           names-to-avoid
                                           wrld))
       (exec-stmt-while-for-fn-body
        `(b* ((fenv (init-fun-env (preprocess ,prog-const)))
              ((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
              (test (exec-expr-pure ',loop-test compst))
              ((when (errorp test)) (mv test (compustate-fix compst)))
              (continuep (test-value test))
              ((when (errorp continuep)) (mv continuep (compustate-fix compst)))
              ((when (not continuep)) (mv nil (compustate-fix compst)))
              ((mv val? compst) (exec-stmt ',loop-body compst fenv (1- limit)))
              ((when (errorp val?)) (mv val? compst))
              ((when (valuep val?)) (mv val? compst)))
           (,exec-stmt-while-for-fn compst (1- limit))))
       (exec-stmt-while-for-fn-hints
        '(("Goal" :in-theory '(acl2::zp-compound-recognizer
                               nfix
                               natp
                               o-p
                               o-finp
                               o<))))
       ((mv exec-stmt-while-for-fn-event &)
        (evmac-generate-defun
         exec-stmt-while-for-fn
         :formals (list 'compst 'limit)
         :body exec-stmt-while-for-fn-body
         :measure '(nfix limit)
         :well-founded-relation 'o<
         :hints exec-stmt-while-for-fn-hints
         :verify-guards nil
         :enable nil))
       (exec-stmt-while-for-fn-thm
        (add-suffix exec-stmt-while-for-fn "-TO-EXEC-STMT-WHILE"))
       ((mv exec-stmt-while-for-fn-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix exec-stmt-while-for-fn-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       ((mv exec-stmt-while-for-fn-thm-event &)
        (evmac-generate-defthm
         exec-stmt-while-for-fn-thm
         :formula `(equal (,exec-stmt-while-for-fn compst limit)
                          (exec-stmt-while ',loop-test
                                           ',loop-body
                                           compst
                                           (init-fun-env
                                            (preprocess ,prog-const))
                                           limit))
         :rule-classes nil
         :hints `(("Goal" :in-theory '(,exec-stmt-while-for-fn
                                       exec-stmt-while))))))
    (mv (list exec-stmt-while-for-fn-event
              exec-stmt-while-for-fn-thm-event)
        exec-stmt-while-for-fn
        exec-stmt-while-for-fn-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-measure-thm ((fn symbolp)
                                  (fn-appconds symbol-symbol-alistp)
                                  (appcond-thms keyword-symbol-alistp)
                                  (measure-of-fn symbolp)
                                  (measure-formals symbol-listp)
                                  (names-to-avoid symbol-listp)
                                  (wrld plist-worldp))
  :guard (irecursivep+ fn wrld)
  :returns (mv (event pseudo-event-formp)
               (name symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate type prescription theorem asserting that
          the measure of the recursive function @('fn')
          yields a natural number."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like the applicability condition,
     except that it uses the generated measure function
     (to treat the measure as a black box,
     as discussed in @(tsee atc-gen-loop-measure-fn)),
     and that it is a type prescription rule
     (which seems needed, as opposed a rewrite rule,
     based on proof experiments)."))
  (b* ((appcond-thm
        (cdr (assoc-eq (cdr (assoc-eq fn fn-appconds)) appcond-thms)))
       (natp-of-measure-of-fn-thm
        (packn-pos (list 'natp-of-measure-of- fn) fn))
       ((mv natp-of-measure-of-fn-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix natp-of-measure-of-fn-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       ((mv natp-of-measure-of-fn-thm-event &)
        (evmac-generate-defthm
         natp-of-measure-of-fn-thm
         :formula `(natp (,measure-of-fn ,@measure-formals))
         :rule-classes :type-prescription
         :enable nil
         :hints `(("Goal"
                   :in-theory '(,measure-of-fn)
                   :use ,appcond-thm)))))
    (mv natp-of-measure-of-fn-thm-event
        natp-of-measure-of-fn-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-termination-thm ((fn symbolp)
                                      (measure-of-fn symbolp)
                                      (measure-formals symbol-listp)
                                      (natp-of-measure-of-fn-thm symbolp)
                                      (names-to-avoid symbol-listp)
                                      (ctx ctxp)
                                      state)
  :guard (and (function-symbolp fn (w state))
              (logicp fn (w state))
              (irecursivep+ fn (w state))
              (not (eq measure-of-fn 'quote)))
  :returns (mv erp
               (val (tuple (event pseudo-event-formp)
                           (name symbolp)
                           (updated-names-to-avoid
                            symbol-listp
                            :hyp (symbol-listp names-to-avoid))
                           val))
               state)
  :short "Generate the version of the termination theorem
          tailored to the limits and measure function."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a local theorem that is
     just like the termination theorem of the function
     except that @(tsee o<) is replaced with @(tsee <),
     and that the measure terms are abstracted to
     calls of the generated measure functions.
     The theorem is proved using the fact that
     the measure yields a natural number,
     which means that @(tsee o<) reduces to @(tsee <) (see above).
     The purpose of this variant of the termination theorem
     is to help establish the induction hypothesis
     in the loop correctness theorem, as explained below."))
  (b* (((acl2::fun (irr)) (list '(_) nil nil))
       (wrld (w state))
       (termination-of-fn-thm
        (packn-pos (list 'termination-of- fn) fn))
       ((mv termination-of-fn-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix termination-of-fn-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       (tthm (termination-theorem$ fn state))
       ((when (eq (car tthm) :failed))
        (raise "Internal error: cannot find termination theorem of ~x0." fn)
        (acl2::value (irr)))
       ((er tthm-formula :iferr (irr))
        (atc-gen-loop-tthm-formula tthm
                                   fn
                                   measure-of-fn
                                   measure-formals
                                   ctx
                                   state))
       ((mv termination-of-fn-thm-event &)
        (evmac-generate-defthm
         termination-of-fn-thm
         :formula tthm-formula
         :rule-classes nil
         :hints `(("Goal"
                   :use ((:termination-theorem ,fn)
                         ,natp-of-measure-of-fn-thm)
                   :in-theory '(,measure-of-fn
                                acl2::natp-compound-recognizer
                                o-p
                                o-finp
                                o<))))))
    (acl2::value
     (list termination-of-fn-thm-event
           termination-of-fn-thm
           names-to-avoid)))
  ///

  (more-returns
   (val true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atc-loop-body-term-subst
  :short "In a term that represents the body of a loop,
          replace each recursive call with
          a term that returns the affected variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is needed to express the correctness theorem for the loop body.
     The theorem needs to relate the execution of the loop body statement
     to the ACL2 term that represents it.
     However, the latter has recursive calls in it,
     which we therefore replace with terms
     that just return the affected variables.
     This ACL2 function does that.
     This gives us the appropriate ACL2 term
     to relate to the execution of the loop body statement,
     because the execution of the loop body statement
     just ends with the affected variables,
     i.e. it does not go back to the loop,
     which would be the equivalent of making the recursive call.")
   (xdoc::p
    "Note that we apply the substitution without regard to lambda variables,
     because we only use this ACL2 function on terms
     that satisfy the restrictions for loop body terms
     described in the user documentation.
     In particular, this means that the recursive calls
     are always on the formals of the loop function,
     and the affected variables also always have the same meaning."))

  (define atc-loop-body-term-subst ((term pseudo-termp)
                                    (fn symbolp)
                                    (affect symbol-listp))
    :returns (new-term pseudo-termp)
    :parents nil
    (b* (((when (member-eq (pseudo-term-kind term) '(:null :quote :var)))
          (pseudo-term-fix term))
         (fn/lam (pseudo-term-call->fn term))
         ((when (eq fn/lam fn))
          (if (consp (cdr affect))
              `(mv ,@(symbol-list-fix affect))
            (symbol-fix (car affect))))
         (args (pseudo-term-call->args term))
         (new-args (atc-loop-body-term-subst-lst args fn affect))
         (new-fn/lam (if (pseudo-lambda-p fn/lam)
                         (pseudo-lambda (pseudo-lambda->formals fn/lam)
                                        (atc-loop-body-term-subst
                                         (pseudo-lambda->body fn/lam)
                                         fn affect))
                       fn/lam)))
      (pseudo-term-call new-fn/lam new-args))
    :measure (pseudo-term-count term))

  (define atc-loop-body-term-subst-lst ((terms pseudo-term-listp)
                                        (fn symbolp)
                                        (affect symbol-listp))
    :returns (new-terms pseudo-term-listp)
    :parents nil
    (cond ((endp terms) nil)
          (t (cons (atc-loop-body-term-subst (car terms) fn affect)
                   (atc-loop-body-term-subst-lst (cdr terms) fn affect))))
    :measure (pseudo-term-list-count terms)
    ///
    (defret len-of-atc-loop-body-term-subst-lst
      (equal (len new-terms)
             (len terms))))

  :ruler-extenders :all

  :returns-hints nil ; for speed

  :verify-guards nil ; done below
  ///
  (verify-guards atc-loop-body-term-subst
    :hints (("Goal" :in-theory (enable pseudo-fn-args-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-test-correct-thm ((fn symbolp)
                                       (typed-formals atc-symbol-type-alistp)
                                       (loop-test exprp)
                                       (test-term pseudo-termp)
                                       (fn-thms symbol-symbol-alistp)
                                       (prec-tags atc-string-taginfo-alistp)
                                       (prec-objs atc-string-objinfo-alistp)
                                       (names-to-avoid symbol-listp)
                                       state)
  :returns (mv (local-events pseudo-event-form-listp)
               (correct-test-thm symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the correctness theorem for the test of a loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a step towards generating more modular and controlled loop proofs.
     The hints are more than needed for now,
     as they include rules about statement execution,
     which does not apply here.
     We will make the hints more nuanced later.")
   (xdoc::p
    "We generate two conjuncts in the conclusion.
     One conjunct, as expected, says that
     executing the test yields the same as
     the ACL2 term @('test-term') that represents the test.
     Note that we need to wrap @(tsee exec-expr-pure) into @(tsee test-value),
     because the ACL2 term is boolean,
     and so we need to convert the C value to a boolean.
     The other conjunct says that @(tsee exec-expr-pure)
     does not return an error.
     This is needed in the generated proof for the whole loop,
     which equates the function generated
     by @(tsee atc-gen-exec-stmt-while-for-loop)
     to the execution of the loop:
     that function's body includes a check that @(tsee exec-expr-pure)
     does not yield an error,
     and so this other conjunct here serves to
     eliminate the case that that check fails."))
  (b* ((wrld (w state))
       (correct-thm (cdr (assoc-eq fn fn-thms)))
       (correct-test-thm (add-suffix correct-thm "-TEST"))
       ((mv correct-test-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix correct-test-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       (formals (strip-cars typed-formals))
       (compst-var (genvar$ 'atc "COMPST" nil formals state))
       ((mv formals-bindings hyps & instantiation)
        (atc-gen-outer-bindings-and-hyps typed-formals compst-var t prec-objs))
       (hyps `(and (compustatep ,compst-var)
                   (> (compustate-frames-number ,compst-var) 0)
                   ,@hyps
                   ,(untranslate$ (uguard+ fn wrld) nil state)))
       (concl `(and (not (errorp (exec-expr-pure ',loop-test ,compst-var)))
                    (equal (test-value (exec-expr-pure ',loop-test ,compst-var))
                           ,test-term)))
       (formula `(b* (,@formals-bindings) (implies ,hyps ,concl)))
       (not-error-thms (atc-string-taginfo-alist-to-not-error-thms prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (value-kind-thms (atc-string-taginfo-alist-to-value-kind-thms prec-tags))
       (struct-reader-return-thms
        (atc-string-taginfo-alist-to-reader-return-thms prec-tags))
       (member-read-thms
        (atc-string-taginfo-alist-to-member-read-thms prec-tags))
       (extobj-recognizers (atc-string-objinfo-alist-to-recognizers prec-objs))
       (hints `(("Goal"
                 :do-not-induct t
                 :in-theory (union-theories
                             (theory 'atc-all-rules)
                             '(not
                               ,@not-error-thms
                               ,@valuep-thms
                               ,@value-kind-thms
                               ,@struct-reader-return-thms
                               ,@member-read-thms
                               ,@extobj-recognizers))
                 :use ((:instance (:guard-theorem ,fn)
                                  :extra-bindings-ok ,@(alist-to-doublets
                                                        instantiation)))
                 :expand :lambdas)))
       ((mv correct-test-thm-event &)
        (evmac-generate-defthm correct-test-thm
                               :formula formula
                               :hints hints
                               :enable nil)))
    (mv (list correct-test-thm-event)
        correct-test-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-final-compustate ((mod-vars symbol-listp)
                                       (typed-formals atc-symbol-type-alistp)
                                       (subst symbol-symbol-alistp)
                                       (compst-var symbolp)
                                       (prec-objs atc-string-objinfo-alistp))
  :returns (term "An untranslated term.")
  :short "Generate a term representing the final computation state
          after the execution of a C loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "The correctness theorem of a C loop says that
     executing the loop on a generic computation state
     (satisfying conditions in the hypotheses of the theorem)
     yields a computation state obtained by modifying
     one or more variables and zero or more arrays in the computation state.
     These are the variables and arrays affected by the loop,
     which the correctness theorem binds to the results of the loop function,
     and which have corresponding named variables and heap arrays
     in the computation state.
     The modified computation state is expressed as
     a nest of @(tsee write-var),
     @(tsee write-static-var),
     and @(tsee write-object) calls.
     This ACL2 code here generates that nest.")
   (xdoc::p
    "Note that, in the correctness theorem,
     the new array variables are bound to
     the possibly modified arrays returned by the ACL2 function:
     these new array variables are obtained by adding @('-NEW')
     to the corresponding formals of the ACL2 function;
     these new names should not cause any conflicts,
     because the names of the formals must be portable C identifiers."))
  (b* (((when (endp mod-vars)) compst-var)
       (mod-var (car mod-vars))
       (type (cdr (assoc-eq mod-var typed-formals)))
       ((when (not type))
        (raise "Internal error: formal ~x0 not found." mod-var))
       (ptrp (type-case type :pointer))
       (ptr (cdr (assoc-eq mod-var subst))))
    (if ptrp
        (if (consp (assoc-equal (symbol-name mod-var) prec-objs))
            `(write-static-var (ident ,(symbol-name mod-var))
                               ,(add-suffix-to-fn mod-var "-NEW")
                               ,(atc-gen-loop-final-compustate (cdr mod-vars)
                                                               typed-formals
                                                               subst
                                                               compst-var
                                                               prec-objs))
          `(write-object (value-pointer->designator ,ptr)
                         ,(add-suffix-to-fn mod-var "-NEW")
                         ,(atc-gen-loop-final-compustate (cdr mod-vars)
                                                         typed-formals
                                                         subst
                                                         compst-var
                                                         prec-objs)))
      `(write-var (ident ,(symbol-name (car mod-vars)))
                  ,(add-suffix-to-fn (car mod-vars) "-NEW")
                  ,(atc-gen-loop-final-compustate (cdr mod-vars)
                                                  typed-formals
                                                  subst
                                                  compst-var
                                                  prec-objs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-body-correct-thm ((fn symbolp)
                                       (typed-formals atc-symbol-type-alistp)
                                       (affect symbol-listp)
                                       (loop-body stmtp)
                                       (test-term pseudo-termp)
                                       (body-term pseudo-termp)
                                       (prec-fns atc-symbol-fninfo-alistp)
                                       (prec-tags atc-string-taginfo-alistp)
                                       (prec-objs atc-string-objinfo-alistp)
                                       (prog-const symbolp)
                                       (fn-thms symbol-symbol-alistp)
                                       (limit pseudo-termp)
                                       (names-to-avoid symbol-listp)
                                       state)
  :returns (mv (local-events pseudo-event-form-listp)
               (correct-body-thm symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the correctness theorem for the body of a loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "For the purpose of making the proofs generated by ATC more modular,
     we generate a separate local theorem for
     the correctness of each generated loop body;
     we plan to change the loop correctness theorem
     to make use of this theorem,
     instead of proving the whole loop, including its body."))
  (b* ((wrld (w state))
       (correct-thm (cdr (assoc-eq fn fn-thms)))
       (correct-body-thm (add-suffix correct-thm "-BODY"))
       ((mv correct-body-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix correct-body-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       (formals (formals+ fn wrld))
       (compst-var (genvar$ 'atc "COMPST" nil formals state))
       (fenv-var (genvar$ 'atc "FENV" nil formals state))
       (limit-var (genvar$ 'atc "LIMIT" nil formals state))
       ((mv formals-bindings hyps subst instantiation)
        (atc-gen-outer-bindings-and-hyps typed-formals compst-var t prec-objs))
       (diff-pointer-hyps
        (atc-gen-object-disjoint-hyps (strip-cdrs subst)))
       (hyps `(and (compustatep ,compst-var)
                   (> (compustate-frames-number ,compst-var) 0)
                   (equal ,fenv-var (init-fun-env (preprocess ,prog-const)))
                   (integerp ,limit-var)
                   (>= ,limit-var ,limit)
                   ,@hyps
                   ,@diff-pointer-hyps
                   ,(untranslate$ (uguard+ fn wrld) nil state)
                   ,(untranslate$ test-term nil state)))
       (affect-new (acl2::add-suffix-to-fn-lst affect "-NEW"))
       (affect-binder (if (endp (cdr affect-new))
                          (car affect-new)
                        `(mv ,@affect-new)))
       (final-compst (atc-gen-loop-final-compustate affect
                                                    typed-formals
                                                    subst
                                                    compst-var
                                                    prec-objs))
       (body-term (atc-loop-body-term-subst body-term fn affect))
       (concl `(equal (exec-stmt ',loop-body ,compst-var ,fenv-var ,limit-var)
                      (b* ((,affect-binder ,body-term))
                        (mv nil ,final-compst))))
       (formula `(b* (,@formals-bindings) (implies ,hyps ,concl)))
       (called-fns (all-fnnames (ubody+ fn wrld)))
       (not-error-thms (atc-string-taginfo-alist-to-not-error-thms prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (value-kind-thms (atc-string-taginfo-alist-to-value-kind-thms prec-tags))
       (result-thms
        (atc-symbol-fninfo-alist-to-result-thms prec-fns called-fns))
       (struct-reader-return-thms
        (atc-string-taginfo-alist-to-reader-return-thms prec-tags))
       (struct-writer-return-thms
        (atc-string-taginfo-alist-to-writer-return-thms prec-tags))
       (correct-thms
        (atc-symbol-fninfo-alist-to-correct-thms prec-fns called-fns))
       (measure-thms
        (atc-symbol-fninfo-alist-to-measure-nat-thms prec-fns called-fns))
       (type-prescriptions-called
        (loop$ for callable in (strip-cars prec-fns)
               collect `(:t ,callable)))
       (type-prescriptions-struct-readers
        (loop$ for reader in (atc-string-taginfo-alist-to-readers prec-tags)
               collect `(:t ,reader)))
       (type-of-value-thms
        (atc-string-taginfo-alist-to-type-of-value-thms prec-tags))
       (flexiblep-thms
        (atc-string-taginfo-alist-to-flexiblep-thms prec-tags))
       (member-read-thms
        (atc-string-taginfo-alist-to-member-read-thms prec-tags))
       (member-write-thms
        (atc-string-taginfo-alist-to-member-write-thms prec-tags))
       (extobj-recognizers (atc-string-objinfo-alist-to-recognizers prec-objs))
       (hints `(("Goal"
                 :do-not-induct t
                 :in-theory (union-theories
                             (theory 'atc-all-rules)
                             '(,@not-error-thms
                               ,@valuep-thms
                               ,@value-kind-thms
                               not
                               ,@struct-reader-return-thms
                               ,@struct-writer-return-thms
                               ,@type-of-value-thms
                               ,@flexiblep-thms
                               ,@member-read-thms
                               ,@member-write-thms
                               ,@type-prescriptions-called
                               ,@type-prescriptions-struct-readers
                               ,@extobj-recognizers
                               ,@result-thms
                               ,@correct-thms
                               ,@measure-thms))
                 :use ((:instance (:guard-theorem ,fn)
                        :extra-bindings-ok ,@(alist-to-doublets instantiation)))
                 :expand :lambdas)))
       ((mv correct-body-thm-event &)
        (evmac-generate-defthm correct-body-thm
                               :formula formula
                               :hints hints
                               :enable nil)))
    (mv (list correct-body-thm-event)
        correct-body-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-correct-thm ((fn symbolp)
                                  (typed-formals atc-symbol-type-alistp)
                                  (affect symbol-listp)
                                  (loop-test exprp)
                                  (loop-body stmtp)
                                  (prec-fns atc-symbol-fninfo-alistp)
                                  (prec-tags atc-string-taginfo-alistp)
                                  (prec-objs atc-string-objinfo-alistp)
                                  (prog-const symbolp)
                                  (fn-thms symbol-symbol-alistp)
                                  (fn-result-thm symbolp)
                                  (exec-stmt-while-for-fn symbolp)
                                  (exec-stmt-while-for-fn-thm symbolp)
                                  (termination-of-fn-thm symbolp)
                                  (natp-of-measure-of-fn-thm symbolp)
                                  (correct-test-thm symbolp)
                                  (correct-body-thm symbolp)
                                  (limit pseudo-termp)
                                  (names-to-avoid symbol-listp)
                                  state)
  :guard (irecursivep+ fn (w state))
  :returns (mv (local-events pseudo-event-form-listp)
               (exported-events pseudo-event-form-listp)
               (fn-correct-thm symbolp :hyp (symbol-symbol-alistp fn-thms))
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the correctness theorem for a C loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate the correctness theorem as a lemma first,
     then the actual theorem.
     The only difference between the two is that
     the lemma uses the specialization of @(tsee exec-stmt-while)
     that is generated as discussed above,
     while the theorem uses the general @(tsee exec-stmt-while);
     the reason is so we can have the right induction, as discussed above.
     As explained shortly,
     the formula involves (some of) the loop function's formals,
     so we take those into account to generate variables for
     the computation state, the function environment, and the limit.
     The hypotheses include the guard of the loop function,
     but we need to replace any pointers with their dereferenced arrays,
     and in addition we need to replace the parameters of the loop function
     with @(tsee read-var) calls that read the corresponding variables.
     The other hypotheses are the same as in @(tsee atc-gen-cfun-correct-thm),
     with the addition of a hypothesis that
     the number of frames in the computation state is not zero;
     this is always the case when executing a loop.
     The arguments of the loop function call are obtained by
     replacing its formals with the corresponding @(tsee read-var) calls.
     The lemma is proved via proof builder instructions,
     by first applying induction
     and then calling the prover on all the induction subgoals.
     For robustness, first we set the theory to contain
     just the specialized @(tsee exec-stmt-while),
     then we apply induction, which therefore must be on that function.
     The theory for the subgoal includes
     fewer rules than the ones for the full symbolic execution,
     because we use the correctness theorems for the loop test and body
     as rewrite rules instead, which take care of most of the execution.
     The @(':expand') hint applies to the loop function,
     for robustness (as ACL2's heuristics sometimes prevent
     the opening of recursive function definitions,
     but here we know that we always want to open it).
     The hints also include:
     (i) the return value theorem of the loop function,
     which is reasonable since the function is recursive,
     and so it is called inside its body;
     (ii) the definition of the specialized @(tsee exec-stmt-while);
     (iii) the rule saying that the measure yields a natural number; and
     (iv) the termination theorem of the loop function, suitably instantiated.
     Given the correctness lemma, the correctness theorem is easily proved,
     via the lemma and the generate theorem that equates
     the specialized @(tsee exec-stmt-while) to the general one.")
   (xdoc::p
    "Similarly to @(tsee atc-gen-cfun-correct-thm),
     we stage the proof of the lemma in two phases:
     see the documentation of that function for motivation."))
  (b* ((wrld (w state))
       (correct-thm (cdr (assoc-eq fn fn-thms)))
       (correct-lemma (add-suffix correct-thm "-LEMMA"))
       ((mv correct-lemma names-to-avoid)
        (fresh-logical-name-with-$s-suffix correct-lemma
                                           nil
                                           names-to-avoid
                                           wrld))
       (formals (formals+ fn wrld))
       (compst-var (genvar$ 'atc "COMPST" nil formals state))
       (fenv-var (genvar$ 'atc "FENV" nil formals state))
       (limit-var (genvar$ 'atc "LIMIT" nil formals state))
       ((mv formals-bindings hyps subst instantiation)
        (atc-gen-outer-bindings-and-hyps typed-formals compst-var t prec-objs))
       (diff-pointer-hyps
        (atc-gen-object-disjoint-hyps (strip-cdrs subst)))
       (hyps `(and (compustatep ,compst-var)
                   (> (compustate-frames-number ,compst-var) 0)
                   (equal ,fenv-var
                          (init-fun-env (preprocess ,prog-const)))
                   (integerp ,limit-var)
                   (>= ,limit-var ,limit)
                   ,@hyps
                   ,@diff-pointer-hyps
                   ,(untranslate$ (uguard+ fn wrld) nil state)))
       (affect-new (acl2::add-suffix-to-fn-lst affect "-NEW"))
       (affect-binder (if (endp (cdr affect-new))
                          (car affect-new)
                        `(mv ,@affect-new)))
       (final-compst (atc-gen-loop-final-compustate affect
                                                    typed-formals
                                                    subst
                                                    compst-var
                                                    prec-objs))
       (concl-lemma `(equal (,exec-stmt-while-for-fn ,compst-var ,limit-var)
                            (b* ((,affect-binder (,fn ,@formals)))
                              (mv nil ,final-compst))))
       (concl-thm `(equal (exec-stmt-while ',loop-test
                                           ',loop-body
                                           ,compst-var
                                           ,fenv-var
                                           ,limit-var)
                          (b* ((,affect-binder (,fn ,@formals)))
                            (mv nil ,final-compst))))
       (formula-lemma `(b* (,@formals-bindings) (implies ,hyps ,concl-lemma)))
       (formula-thm `(b* (,@formals-bindings) (implies ,hyps ,concl-thm)))
       (called-fns (all-fnnames (ubody+ fn wrld)))
       (not-error-thms (atc-string-taginfo-alist-to-not-error-thms prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (result-thms
        (atc-symbol-fninfo-alist-to-result-thms prec-fns called-fns))
       (result-thms (cons fn-result-thm result-thms))
       (struct-reader-return-thms
        (atc-string-taginfo-alist-to-reader-return-thms prec-tags))
       (struct-writer-return-thms
        (atc-string-taginfo-alist-to-writer-return-thms prec-tags))
       (correct-thms
        (atc-symbol-fninfo-alist-to-correct-thms prec-fns called-fns))
       (measure-thms
        (atc-symbol-fninfo-alist-to-measure-nat-thms prec-fns called-fns))
       (type-prescriptions-called
        (loop$ for callable in (strip-cars prec-fns)
               collect `(:t ,callable)))
       (type-prescriptions-struct-readers
        (loop$ for reader in (atc-string-taginfo-alist-to-readers prec-tags)
               collect `(:t ,reader)))
       (type-of-value-thms
        (atc-string-taginfo-alist-to-type-of-value-thms prec-tags))
       (flexiblep-thms
        (atc-string-taginfo-alist-to-flexiblep-thms prec-tags))
       (member-read-thms
        (atc-string-taginfo-alist-to-member-read-thms prec-tags))
       (member-write-thms
        (atc-string-taginfo-alist-to-member-write-thms prec-tags))
       (extobj-recognizers (atc-string-objinfo-alist-to-recognizers prec-objs))
       (lemma-hints `(("Goal"
                       :do-not-induct t
                       :in-theory (append
                                   *atc-symbolic-computation-state-rules*
                                   *atc-valuep-rules*
                                   *atc-value-listp-rules*
                                   *atc-value-optionp-rules*
                                   *atc-type-of-value-rules*
                                   *atc-type-of-value-option-rules*
                                   *atc-value-array->elemtype-rules*
                                   *atc-array-length-rules*
                                   *atc-array-length-write-rules*
                                   *atc-other-executable-counterpart-rules*
                                   *atc-wrapper-rules*
                                   *atc-distributivity-over-if-rewrite-rules*
                                   *atc-identifier-rules*
                                   *atc-not-rules*
                                   *atc-integer-size-rules*
                                   *atc-limit-rules*
                                   *atc-not-error-rules*
                                   *atc-integer-ops-1-return-rewrite-rules*
                                   *atc-integer-ops-2-return-rewrite-rules*
                                   *atc-integer-convs-return-rewrite-rules*
                                   *atc-array-read-return-rewrite-rules*
                                   *atc-array-write-return-rewrite-rules*
                                   *atc-misc-rewrite-rules*
                                   *atc-computation-state-return-rules*
                                   *atc-boolean-from-integer-return-rules*
                                   *atc-type-prescription-rules*
                                   *atc-compound-recognizer-rules*
                                   *integer-value-disjoint-rules*
                                   *array-value-disjoint-rules*
                                   *atc-value-fix-rules*
                                   *atc-flexible-array-member-rules*
                                   '(,@not-error-thms
                                     ,@valuep-thms
                                     not
                                     ,exec-stmt-while-for-fn
                                     ,@struct-reader-return-thms
                                     ,@struct-writer-return-thms
                                     ,@type-of-value-thms
                                     ,@flexiblep-thms
                                     ,@member-read-thms
                                     ,@member-write-thms
                                     ,@type-prescriptions-called
                                     ,@type-prescriptions-struct-readers
                                     ,@result-thms
                                     ,@correct-thms
                                     ,@measure-thms
                                     ,natp-of-measure-of-fn-thm
                                     ,@extobj-recognizers
                                     ,correct-test-thm
                                     ,correct-body-thm))
                       :use ((:instance (:guard-theorem ,fn)
                                        :extra-bindings-ok ,@(alist-to-doublets
                                                              instantiation))
                             (:instance ,termination-of-fn-thm
                                        :extra-bindings-ok ,@(alist-to-doublets
                                                              instantiation))))
                      (and stable-under-simplificationp
                           '(:in-theory
                             (append
                              *atc-symbolic-computation-state-rules*
                              *atc-valuep-rules*
                              *atc-value-listp-rules*
                              *atc-value-optionp-rules*
                              *atc-type-of-value-rules*
                              *atc-type-of-value-option-rules*
                              *atc-value-array->elemtype-rules*
                              *atc-array-length-rules*
                              *atc-array-length-write-rules*
                              *atc-other-executable-counterpart-rules*
                              *atc-wrapper-rules*
                              *atc-distributivity-over-if-rewrite-rules*
                              *atc-identifier-rules*
                              *atc-not-rules*
                              *atc-integer-size-rules*
                              *atc-limit-rules*
                              *atc-not-error-rules*
                              *atc-integer-ops-1-return-rewrite-rules*
                              *atc-integer-ops-2-return-rewrite-rules*
                              *atc-integer-convs-return-rewrite-rules*
                              *atc-array-read-return-rewrite-rules*
                              *atc-array-write-return-rewrite-rules*
                              *atc-misc-rewrite-rules*
                              *atc-computation-state-return-rules*
                              *atc-boolean-from-integer-return-rules*
                              *atc-type-prescription-rules*
                              *atc-compound-recognizer-rules*
                              *integer-value-disjoint-rules*
                              *array-value-disjoint-rules*
                              *atc-value-fix-rules*
                              *atc-flexible-array-member-rules*
                              '(,@not-error-thms
                                ,@valuep-thms
                                not
                                ,exec-stmt-while-for-fn
                                ,@struct-reader-return-thms
                                ,@struct-writer-return-thms
                                ,@type-of-value-thms
                                ,@flexiblep-thms
                                ,@member-read-thms
                                ,@member-write-thms
                                ,@type-prescriptions-called
                                ,@type-prescriptions-struct-readers
                                ,@result-thms
                                ,@correct-thms
                                ,@measure-thms
                                ,natp-of-measure-of-fn-thm
                                ,@extobj-recognizers
                                ,correct-test-thm
                                ,correct-body-thm))
                             :expand (:lambdas
                                      (,fn ,@(fsublis-var-lst
                                              instantiation
                                              formals)))))))
       (lemma-instructions
        `((:in-theory '(,exec-stmt-while-for-fn))
          (:induct (,exec-stmt-while-for-fn ,compst-var ,limit-var))
          (:repeat (:prove :hints ,lemma-hints))))
       (thm-hints `(("Goal"
                     :in-theory nil
                     :use (,correct-lemma ,exec-stmt-while-for-fn-thm))))
       ((mv correct-lemma-event &)
        (evmac-generate-defthm correct-lemma
                               :formula formula-lemma
                               :instructions lemma-instructions
                               :enable nil))
       ((mv correct-thm-local-event correct-thm-exported-event)
        (evmac-generate-defthm correct-thm
                               :formula formula-thm
                               :hints thm-hints
                               :enable nil))
       (local-events (list correct-lemma-event
                           correct-thm-local-event))
       (exported-events (list correct-thm-exported-event)))
    (mv local-events
        exported-events
        correct-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop ((fn symbolp)
                      (prec-fns atc-symbol-fninfo-alistp)
                      (prec-tags atc-string-taginfo-alistp)
                      (prec-objs atc-string-objinfo-alistp)
                      (proofs booleanp)
                      (prog-const symbolp)
                      (fn-thms symbol-symbol-alistp)
                      (fn-appconds symbol-symbol-alistp)
                      (appcond-thms keyword-symbol-alistp)
                      (print evmac-input-print-p)
                      (names-to-avoid symbol-listp)
                      (ctx ctxp)
                      state)
  :guard (and (function-symbolp fn (w state))
              (logicp fn (w state))
              (irecursivep+ fn (w state))
              (not (eq fn 'quote)))
  :returns (mv erp
               (val (tuple (local-events pseudo-event-form-listp)
                           (exported-events pseudo-event-form-listp)
                           (updated-prec-fns atc-symbol-fninfo-alistp)
                           (updated-names-to-avoid symbol-listp)
                           val)
                    :hyp (and (atc-symbol-fninfo-alistp prec-fns)
                              (symbol-listp names-to-avoid)))
               state)
  :short "Generate a C loop from a recursive ACL2 function,
          with accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called if @('fn') is a recursive target function.
     We process the function body as a loop term,
     and update the @('prec-fns') alist with information about the function.")
   (xdoc::p
    "We also generate the measure function for @('fn') here.
     See @(tsee atc-gen-loop-measure-fn).")
   (xdoc::p
    "No C external declaration is generated for this function,
     because this function just represents a loop used in oher functions."))
  (b* (((acl2::fun (irr)) (list nil nil nil nil))
       (wrld (w state))
       ((mv measure-of-fn-event
            measure-of-fn
            measure-formals
            names-to-avoid)
        (if proofs
            (atc-gen-loop-measure-fn fn names-to-avoid state)
          (mv '(_) nil nil names-to-avoid)))
       ((er typed-formals :iferr (irr))
        (atc-typed-formals fn prec-tags prec-objs ctx state))
       (body (ubody+ fn wrld))
       ((er (lstmt-gout loop) :iferr (irr))
        (atc-gen-loop-stmt body
                           (make-lstmt-gin :inscope (list typed-formals)
                                           :fn fn
                                           :measure-for-fn measure-of-fn
                                           :measure-formals measure-formals
                                           :prec-fns prec-fns
                                           :prec-tags prec-tags
                                           :prec-objs prec-objs
                                           :thm-index 1
                                           :names-to-avoid names-to-avoid
                                           :proofs proofs)
                           ctx
                           state))
       (names-to-avoid loop.names-to-avoid)
       ((unless (and (plist-worldp (w state))
                     (function-symbolp fn (w state))
                     (logicp fn (w state))
                     (irecursivep+ fn (w state))))
        (raise "Internal error with W of STATE.")
        (acl2::value (irr)))
       ((er (list local-events
                  exported-events
                  natp-of-measure-of-fn-thm
                  fn-result-thm
                  fn-correct-thm
                  names-to-avoid)
            :iferr (irr))
        (if proofs
            (b* (((mv fn-result-events
                      fn-result-thm
                      names-to-avoid)
                  (atc-gen-fn-result-thm fn
                                         nil
                                         loop.affect
                                         typed-formals
                                         prec-fns
                                         prec-tags
                                         prec-objs
                                         names-to-avoid
                                         state))
                 (loop-test (stmt-while->test loop.stmt))
                 (loop-body (stmt-while->body loop.stmt))
                 ((mv exec-stmt-while-events
                      exec-stmt-while-for-fn
                      exec-stmt-while-for-fn-thm
                      names-to-avoid)
                  (atc-gen-exec-stmt-while-for-loop fn
                                                    loop.stmt
                                                    prog-const
                                                    names-to-avoid
                                                    wrld))
                 ((mv natp-of-measure-of-fn-thm-event
                      natp-of-measure-of-fn-thm
                      names-to-avoid)
                  (atc-gen-loop-measure-thm fn
                                            fn-appconds
                                            appcond-thms
                                            measure-of-fn
                                            measure-formals
                                            names-to-avoid
                                            wrld))
                 ((er (list termination-of-fn-thm-event
                            termination-of-fn-thm)
                      :iferr (list nil nil nil nil nil nil))
                  (atc-gen-loop-termination-thm fn
                                                measure-of-fn
                                                measure-formals
                                                natp-of-measure-of-fn-thm
                                                names-to-avoid
                                                ctx
                                                state))
                 ((unless (and (plist-worldp (w state))
                               (irecursivep+ fn (w state))))
                  (raise "Internal error with W of STATE.")
                  (acl2::value (irr)))
                 ((mv test-local-events
                      correct-test-thm
                      names-to-avoid)
                  (atc-gen-loop-test-correct-thm fn
                                                 typed-formals
                                                 loop-test
                                                 loop.test-term
                                                 fn-thms
                                                 prec-tags
                                                 prec-objs
                                                 names-to-avoid
                                                 state))
                 ((mv body-local-events
                      correct-body-thm
                      names-to-avoid)
                  (atc-gen-loop-body-correct-thm fn
                                                 typed-formals
                                                 loop.affect
                                                 loop-body
                                                 loop.test-term
                                                 loop.body-term
                                                 prec-fns
                                                 prec-tags
                                                 prec-objs
                                                 prog-const
                                                 fn-thms
                                                 loop.limit-body
                                                 names-to-avoid
                                                 state))
                 ((mv correct-local-events
                      correct-exported-events
                      fn-correct-thm
                      names-to-avoid)
                  (atc-gen-loop-correct-thm fn
                                            typed-formals
                                            loop.affect
                                            loop-test
                                            loop-body
                                            prec-fns
                                            prec-tags
                                            prec-objs
                                            prog-const
                                            fn-thms
                                            fn-result-thm
                                            exec-stmt-while-for-fn
                                            exec-stmt-while-for-fn-thm
                                            termination-of-fn-thm
                                            natp-of-measure-of-fn-thm
                                            correct-test-thm
                                            correct-body-thm
                                            loop.limit-all
                                            names-to-avoid
                                            state))
                 (progress-start?
                  (and (evmac-input-print->= print :info)
                       `((cw-event "~%Generating the proofs for ~x0..." ',fn))))
                 (progress-end? (and (evmac-input-print->= print :info)
                                     `((cw-event " done.~%"))))
                 (local-events (append loop.events
                                       progress-start?
                                       (and measure-of-fn
                                            (list measure-of-fn-event))
                                       fn-result-events
                                       exec-stmt-while-events
                                       (list natp-of-measure-of-fn-thm-event)
                                       (list termination-of-fn-thm-event)
                                       test-local-events
                                       body-local-events
                                       correct-local-events
                                       progress-end?))
                 (exported-events correct-exported-events))
              (acl2::value
               (list local-events
                     exported-events
                     natp-of-measure-of-fn-thm
                     fn-result-thm
                     fn-correct-thm
                     names-to-avoid)))
          (acl2::value (list nil nil nil nil nil names-to-avoid))))
       (info (make-atc-fn-info :out-type nil
                               :in-types (strip-cdrs typed-formals)
                               :loop? loop.stmt
                               :affect loop.affect
                               :result-thm fn-result-thm
                               :correct-thm fn-correct-thm
                               :measure-nat-thm natp-of-measure-of-fn-thm
                               :fun-env-thm nil
                               :limit loop.limit-all)))
    (acl2::value (list local-events
                       exported-events
                       (acons fn info prec-fns)
                       names-to-avoid)))
  ///

  (more-returns
   (val true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tag-member-read-thms ((tag identp)
                                      (recognizer symbolp)
                                      (fixer-recognizer-thm symbolp)
                                      (not-error-thm symbolp)
                                      (meminfo defstruct-member-infop)
                                      (names-to-avoid symbol-listp)
                                      (wrld plist-worldp))
  :returns (mv (local-events pseudo-event-form-listp)
               (member-read-thms symbol-listp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorems to rewrite
          the execution of certain pure expressions to structure reads,
          for a member of a structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This class of theorems are the structure counterpart of
     the ones that rewrite @(tsee exec-arrsub) to array readers,
     generated in @(see atc-exec-arrsub-rules-generation).")
   (xdoc::p
    "For a scalar member (which must have integer type),
     we generate two theorems that
     rewrite calls of @(tsee exec-member) and @(tsee exec-memberp)
     to calls of the reader.")
   (xdoc::p
    "For an array member (which must have integer element type),
     we generate 20 theorems,
     for each integer index type (10)
     and for each of @(tsee exec-member) and @(tsee exec-memberp).
     The theorems rewrite calls of
     @(tsee exec-arrsub-of-member) or @(tsee exec-arrsub-of-memberp)
     to calls of the readers.
     The generation of these theorems relies on the fact that
     the order of the readers and the checkers matches the order of
     the types in @(tsee *nonchar-integer-types**).
     Note that the @(tsee defstruct-member-info)
     contains 11 readers and 11 checkers,
     where the first reader and checker operate on ACL2 integers,
     while the other 10 readers and 10 checkers operate on C integers.
     We iterate through the 10 readers and checkers on C integers,
     while using the reader and checker on ACL2 integers at each iteration.")
   (xdoc::p
    "If the structure type has a flexible array member,
     we avoid generating theorems for accessing members by structure value,
     because in ATC-generated code we only allow access by pointer."))
  (b* ((memtype (defstruct-member-info->memtype meminfo))
       (memname (member-type->name memtype))
       (type (member-type->type memtype))
       (length (defstruct-member-info->length meminfo))
       (readers (defstruct-member-info->readers meminfo))
       (checkers (defstruct-member-info->checkers meminfo))
       ((when (type-nonchar-integerp type))
        (b* (((unless (and (consp readers)
                           (endp (cdr readers))))
              (prog2$
               (raise "Internal error: not one reader ~x0." readers)
               (mv nil nil nil)))
             (reader (car readers))
             (thm-member-name (pack 'exec-member-read-when-
                                    recognizer
                                    '-and-
                                    (ident->name memname)))
             ((mv thm-member-name names-to-avoid)
              (fresh-logical-name-with-$s-suffix thm-member-name
                                                 nil
                                                 names-to-avoid
                                                 wrld))
             (thm-memberp-name (pack 'exec-memberp-read-when-
                                     recognizer
                                     '-and-
                                     (ident->name memname)))
             ((mv thm-memberp-name names-to-avoid)
              (fresh-logical-name-with-$s-suffix thm-memberp-name
                                                 nil
                                                 names-to-avoid
                                                 wrld))
             (formula-member
              `(implies (and ,(atc-syntaxp-hyp-for-expr-pure 'struct)
                             (,recognizer struct))
                        (equal (exec-member struct
                                            (ident ,(ident->name memname)))
                               (,reader struct))))
             (formula-memberp
              `(implies (and ,(atc-syntaxp-hyp-for-expr-pure 'ptr)
                             (valuep ptr)
                             (value-case ptr :pointer)
                             (not (value-pointer-nullp ptr))
                             (equal (value-pointer->reftype ptr)
                                    (type-struct (ident ,(ident->name tag))))
                             (equal struct
                                    (read-object (value-pointer->designator ptr)
                                                 compst))
                             (,recognizer struct))
                        (equal (exec-memberp ptr
                                             (ident ,(ident->name memname))
                                             compst)
                               (,reader struct))))
             (hints `(("Goal"
                       :in-theory
                       '(exec-member
                         exec-memberp
                         not-errorp-when-valuep
                         value-resultp-when-valuep
                         value-result-fix-when-value-resultp
                         ,recognizer
                         ,reader
                         ,not-error-thm
                         ,fixer-recognizer-thm))))
             ((mv event-member &)
              (evmac-generate-defthm thm-member-name
                                     :formula formula-member
                                     :hints hints
                                     :enable nil))
             ((mv event-memberp &)
              (evmac-generate-defthm thm-memberp-name
                                     :formula formula-memberp
                                     :hints hints
                                     :enable nil)))
          (mv (list event-member event-memberp)
              (list thm-member-name thm-memberp-name)
              names-to-avoid)))
       ((unless (type-case type :array))
        (prog2$
         (raise "Internal error: member type ~x0." type)
         (mv nil nil nil)))
       (elemtype (type-array->of type))
       ((unless (type-nonchar-integerp elemtype))
        (prog2$
         (raise "Internal error: array member element type ~x0." elemtype)
         (mv nil nil nil))))
    (atc-gen-tag-member-read-thms-aux tag
                                      recognizer
                                      fixer-recognizer-thm
                                      memname
                                      elemtype
                                      *nonchar-integer-types**
                                      (car readers)
                                      (car checkers)
                                      (cdr readers)
                                      (cdr checkers)
                                      length
                                      names-to-avoid
                                      wrld))

  :prepwork
  ((define atc-gen-tag-member-read-thms-aux ((tag identp)
                                             (recognizer symbolp)
                                             (fixer-recognizer-thm symbolp)
                                             (memname identp)
                                             (elemtype typep)
                                             (indextypes type-listp)
                                             (reader-acl2int symbolp)
                                             (checker-acl2int symbolp)
                                             (readers symbol-listp)
                                             (checkers symbol-listp)
                                             (length symbolp)
                                             (names-to-avoid symbol-listp)
                                             (wrld plist-worldp))
     :guard (and (type-nonchar-integerp elemtype)
                 (type-nonchar-integer-listp indextypes))
     :returns (mv (local-events pseudo-event-form-listp)
                  (member-read-thms symbol-listp)
                  (updated-names-to-avoid symbol-listp
                                          :hyp (symbol-listp names-to-avoid)))
     :parents nil
     (b* (((when (endp indextypes)) (mv nil nil nil))
          (indextype (car indextypes))
          (reader (car readers))
          (checker (car checkers))
          (indexfixtype (integer-type-to-fixtype indextype))
          (elemfixtype (integer-type-to-fixtype elemtype))
          (indextypep (pack indexfixtype 'p))
          (array-reader (pack elemfixtype '-array-read-alt-def))
          (array-checker (pack elemfixtype '-array-index-okp))
          (not-error-array-thm (pack 'not-errorp-when- elemfixtype '-arrayp))
          (kind-array-thm (pack 'value-kind-when- elemfixtype '-arrayp))
          (valuep-when-indextype (pack 'valuep-when- indextypep))
          (type-thm (pack indexfixtype '->get$inline))
          (thm-member-name (pack 'exec-member-read-when-
                                 recognizer
                                 '-and-
                                 (ident->name memname)
                                 '-
                                 indexfixtype))
          ((mv thm-member-name names-to-avoid)
           (fresh-logical-name-with-$s-suffix thm-member-name
                                              nil
                                              names-to-avoid
                                              wrld))
          (thm-memberp-name (pack 'exec-memberp-read-when-
                                  recognizer
                                  '-and-
                                  (ident->name memname)
                                  '-
                                  indexfixtype))
          ((mv thm-memberp-name names-to-avoid)
           (fresh-logical-name-with-$s-suffix thm-memberp-name
                                              nil
                                              names-to-avoid
                                              wrld))
          (check-hyp (if length
                         `(,checker index struct)
                       `(,checker index)))
          (formula-member
           `(implies (and ,(atc-syntaxp-hyp-for-expr-pure 'struct)
                          (,recognizer struct)
                          (equal array
                                 (value-struct-read (ident
                                                     ,(ident->name memname))
                                                    struct))
                          (,indextypep index)
                          ,check-hyp)
                     (equal (exec-arrsub-of-member struct
                                                   (ident
                                                    ,(ident->name memname))
                                                   index)
                            (,reader index struct))))
          (formula-memberp
           `(implies (and ,(atc-syntaxp-hyp-for-expr-pure 'ptr)
                          (valuep ptr)
                          (value-case ptr :pointer)
                          (not (value-pointer-nullp ptr))
                          (equal (value-pointer->reftype ptr)
                                 (type-struct (ident ,(ident->name tag))))
                          (equal struct
                                 (read-object (value-pointer->designator ptr)
                                              compst))
                          (,recognizer struct)
                          (equal array
                                 (value-struct-read (ident
                                                     ,(ident->name memname))
                                                    struct))
                          (,indextypep index)
                          ,check-hyp)
                     (equal (exec-arrsub-of-memberp ptr
                                                    (ident
                                                     ,(ident->name memname))
                                                    index
                                                    compst)
                            (,reader index struct))))
          (hints `(("Goal"
                    :in-theory
                    '(exec-arrsub-of-member
                      exec-arrsub-of-memberp
                      value-struct-read
                      value-integer->get
                      value-schar->get-to-schar->get
                      value-uchar->get-to-uchar->get
                      value-sshort->get-to-sshort->get
                      value-ushort->get-to-ushort->get
                      value-sint->get-to-sint->get
                      value-uint->get-to-uint->get
                      value-slong->get-to-slong->get
                      value-ulong->get-to-ulong->get
                      value-sllong->get-to-sllong->get
                      value-ullong->get-to-ullong->get
                      value-kind-when-scharp
                      value-kind-when-ucharp
                      value-kind-when-sshortp
                      value-kind-when-ushortp
                      value-kind-when-sintp
                      value-kind-when-uintp
                      value-kind-when-slongp
                      value-kind-when-ulongp
                      value-kind-when-sllongp
                      value-kind-when-ullongp
                      ifix
                      integer-range-p
                      not-errorp-when-valuep
                      value-fix-when-valuep
                      value-result-fix-when-value-resultp
                      value-resultp-when-valuep
                      value-integerp
                      value-unsigned-integerp-alt-def
                      value-signed-integerp-alt-def
                      (:e ident)
                      ,@*integer-value-disjoint-rules*
                      ,recognizer
                      ,fixer-recognizer-thm
                      ,checker
                      ,checker-acl2int
                      ,reader
                      ,reader-acl2int
                      ,array-reader
                      ,array-checker
                      ,not-error-array-thm
                      ,kind-array-thm
                      ,valuep-when-indextype
                      (:t ,type-thm)
                      ,@(and length
                             (list length
                                   'value-struct-read))))))
          ((mv event-member &)
           (evmac-generate-defthm thm-member-name
                                  :formula formula-member
                                  :hints hints
                                  :enable nil))
          ((mv event-memberp &)
           (evmac-generate-defthm thm-memberp-name
                                  :formula formula-memberp
                                  :hints hints
                                  :enable nil))
          ((mv events thm-names names-to-avoid)
           (atc-gen-tag-member-read-thms-aux tag
                                             recognizer
                                             fixer-recognizer-thm
                                             memname
                                             elemtype
                                             (cdr indextypes)
                                             reader-acl2int
                                             checker-acl2int
                                             (cdr readers)
                                             (cdr checkers)
                                             length
                                             names-to-avoid
                                             wrld)))
       (mv (append (and (not length)
                        (list event-member))
                   (list event-memberp)
                   events)
           (append (and (not length)
                        (list thm-member-name))
                   (list thm-memberp-name)
                   thm-names)
           names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tag-member-read-all-thms ((tag identp)
                                          (recognizer symbolp)
                                          (fixer-recognizer-thm symbolp)
                                          (not-error-thm symbolp)
                                          (meminfos defstruct-member-info-listp)
                                          (names-to-avoid symbol-listp)
                                          (wrld plist-worldp))
  :returns (mv (local-events pseudo-event-form-listp)
               (member-read-thms symbol-listp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorems to rewrite
          the execution of certain pure expressions to structure reads,
          for all the members of a structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This relies on @('readers') to be in the same order as @('members')."))
  (b* (((when (endp meminfos)) (mv nil nil names-to-avoid))
       ((mv events thms names-to-avoid)
        (atc-gen-tag-member-read-thms tag
                                      recognizer
                                      fixer-recognizer-thm
                                      not-error-thm
                                      (car meminfos)
                                      names-to-avoid
                                      wrld))
       ((mv more-events more-thms names-to-avoid)
        (atc-gen-tag-member-read-all-thms tag
                                          recognizer
                                          fixer-recognizer-thm
                                          not-error-thm
                                          (cdr meminfos)
                                          names-to-avoid
                                          wrld)))
    (mv (append events more-events)
        (append thms more-thms)
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tag-member-write-thms ((tag identp)
                                       (recognizer symbolp)
                                       (fixer-recognizer-thm symbolp)
                                       (not-error-thm symbolp)
                                       (type-of-value-thm symbolp)
                                       (meminfo defstruct-member-infop)
                                       (names-to-avoid symbol-listp)
                                       (wrld plist-worldp))
  :returns (mv (local-events pseudo-event-form-listp)
               (member-write-thms symbol-listp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorems to rewrite
          the execution of certain assignment expressions to structure writes,
          for a member of a structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This class of theorems are the structure counterpart of
     the ones that rewrite @(tsee exec-expr-asg)
     that have @(':arrsub') left expressions
     to array writers,
     in @(see atc-exec-expr-asg-arrsub-rules-generation).")
   (xdoc::p
    "For a scalar member (which must have integer type),
     we generate two theorems that
     rewrite calls of @(tsee exec-expr-asg),
     where the assignee is a @(':member') or @(':memberp') expression,
     to calls of the writer.")
   (xdoc::p
    "For an array member (which must have integer element type),
     we generate 10 theorems, one for each integer index type.
     The theorem rewrites certain calls of @(tsee exec-expr-asg)
     to calls of the writers.
     The generation of these theorems relies on the fact that
     the order of the writers and the checkers matches the order of
     the types in @(tsee *nonchar-integer-types**).
     Note that the @(tsee defstruct-member-info)
     contains 11 writers and 11 checkers,
     where the first writer and checker operate on ACL2 integers,
     while the other 10 writers and 10 checkers operate on C integers.
     We iterate through the 10 writers and checkers on C integers,
     while using the writer and checker on ACL2 integers at each iteration.")
   (xdoc::p
    "If the structure type has a flexible array member,
     we avoid generating theorems for accessing members by structure value,
     because in ATC-generated code we only allow access by pointer."))
  (b* ((memtype (defstruct-member-info->memtype meminfo))
       (memname (member-type->name memtype))
       (type (member-type->type memtype))
       (length (defstruct-member-info->length meminfo))
       (writers (defstruct-member-info->writers meminfo))
       (writer-return-thms (defstruct-member-info->writer-return-thms meminfo))
       (writer-return-thm (car writer-return-thms))
       (checkers (defstruct-member-info->checkers meminfo))
       ((when (type-nonchar-integerp type))
        (b* (((unless (and (consp writers)
                           (endp (cdr writers))))
              (prog2$
               (raise "Internal error: not one writer ~x0." writers)
               (mv nil nil nil)))
             (writer (car writers))
             (thm-member-name (pack 'exec-member-write-when-
                                    recognizer
                                    '-and-
                                    (ident->name memname)))
             ((mv thm-member-name names-to-avoid)
              (fresh-logical-name-with-$s-suffix thm-member-name
                                                 nil
                                                 names-to-avoid
                                                 wrld))
             (thm-memberp-name (pack 'exec-memberp-write-when-
                                     recognizer
                                     '-and-
                                     (ident->name memname)))
             ((mv thm-memberp-name names-to-avoid)
              (fresh-logical-name-with-$s-suffix thm-memberp-name
                                                 nil
                                                 names-to-avoid
                                                 wrld))
             (typep (atc-type-to-recognizer type wrld))
             ((unless typep)
              (raise "Internal error: unsupported member type ~x0." type)
              (mv nil nil nil))
             (formula-member
              `(implies (and (syntaxp (quotep e))
                             (equal (expr-kind e) :binary)
                             (equal (binop-kind (expr-binary->op e)) :asg)
                             (equal left (expr-binary->arg1 e))
                             (equal right (expr-binary->arg2 e))
                             (equal (expr-kind left) :member)
                             (equal target (expr-member->target left))
                             (equal member (expr-member->name left))
                             (equal (expr-kind target) :ident)
                             (equal member (ident ,(ident->name memname)))
                             (not (zp limit))
                             (equal var (expr-ident->get target))
                             (equal struct (read-var var compst))
                             (,recognizer struct)
                             (equal val (exec-expr-pure right compst))
                             (,typep val))
                        (equal (exec-expr-asg e compst fenv limit)
                               (write-var var
                                          (,writer val struct)
                                          compst))))
             (formula-memberp
              `(implies (and (syntaxp (quotep e))
                             (equal (expr-kind e) :binary)
                             (equal (binop-kind (expr-binary->op e)) :asg)
                             (equal left (expr-binary->arg1 e))
                             (equal right (expr-binary->arg2 e))
                             (equal (expr-kind left) :memberp)
                             (equal target (expr-memberp->target left))
                             (equal member (expr-memberp->name left))
                             (equal (expr-kind target) :ident)
                             (equal member (ident ,(ident->name memname)))
                             (not (zp limit))
                             (equal ptr (read-var (expr-ident->get target)
                                                  compst))
                             (valuep ptr)
                             (value-case ptr :pointer)
                             (not (value-pointer-nullp ptr))
                             (equal (value-pointer->reftype ptr)
                                    (type-struct (ident ,(ident->name tag))))
                             (equal struct
                                    (read-object (value-pointer->designator ptr)
                                                 compst))
                             (,recognizer struct)
                             (equal val (exec-expr-pure right compst))
                             (,typep val))
                        (equal (exec-expr-asg e compst fenv limit)
                               (write-object (value-pointer->designator ptr)
                                             (,writer val struct)
                                             compst))))
             (hints-member
              `(("Goal"
                 :in-theory
                 '(exec-expr-asg
                   not-errorp-when-valuep
                   valuep-when-ucharp
                   valuep-when-scharp
                   valuep-when-ushortp
                   valuep-when-sshortp
                   valuep-when-uintp
                   valuep-when-sintp
                   valuep-when-ulongp
                   valuep-when-slongp
                   valuep-when-ullongp
                   valuep-when-sllongp
                   consp-when-ucharp
                   consp-when-scharp
                   consp-when-ushortp
                   consp-when-sshortp
                   consp-when-uintp
                   consp-when-sintp
                   consp-when-ulongp
                   consp-when-slongp
                   consp-when-ullongp
                   consp-when-sllongp
                   uchar-fix-when-ucharp
                   schar-fix-when-scharp
                   ushort-fix-when-ushortp
                   sshort-fix-when-sshortp
                   uint-fix-when-uintp
                   sint-fix-when-sintp
                   ulong-fix-when-ulongp
                   slong-fix-when-slongp
                   ullong-fix-when-ullongp
                   sllong-fix-when-sllongp
                   ,writer
                   ,not-error-thm
                   ,recognizer
                   ,fixer-recognizer-thm
                   ,type-of-value-thm)
                 :use
                 (:instance
                  ,writer-return-thm
                  (val (b* ((left (expr-binary->arg1 e)))
                         (exec-expr-pure (expr-binary->arg2 e) compst)))
                  (struct (b* ((left (expr-binary->arg1 e))
                               (target (expr-member->target left))
                               (var (expr-ident->get target))
                               (struct (read-var var compst)))
                            struct))))))
             (hints-memberp
              `(("Goal"
                 :in-theory
                 '(exec-expr-asg
                   not-errorp-when-valuep
                   valuep-when-ucharp
                   valuep-when-scharp
                   valuep-when-ushortp
                   valuep-when-sshortp
                   valuep-when-uintp
                   valuep-when-sintp
                   valuep-when-ulongp
                   valuep-when-slongp
                   valuep-when-ullongp
                   valuep-when-sllongp
                   consp-when-ucharp
                   consp-when-scharp
                   consp-when-ushortp
                   consp-when-sshortp
                   consp-when-uintp
                   consp-when-sintp
                   consp-when-ulongp
                   consp-when-slongp
                   consp-when-ullongp
                   consp-when-sllongp
                   uchar-fix-when-ucharp
                   schar-fix-when-scharp
                   ushort-fix-when-ushortp
                   sshort-fix-when-sshortp
                   uint-fix-when-uintp
                   sint-fix-when-sintp
                   ulong-fix-when-ulongp
                   slong-fix-when-slongp
                   ullong-fix-when-ullongp
                   sllong-fix-when-sllongp
                   ,writer
                   ,not-error-thm
                   ,recognizer
                   ,fixer-recognizer-thm
                   ,type-of-value-thm)
                 :use
                 (:instance
                  ,writer-return-thm
                  (val (b* ((left (expr-binary->arg1 e)))
                         (exec-expr-pure (expr-binary->arg2 e) compst)))
                  (struct (b* ((left (expr-binary->arg1 e))
                               (target (expr-memberp->target left))
                               (ptr (read-var (expr-ident->get target)
                                              compst))
                               (struct (read-object
                                        (value-pointer->designator ptr)
                                        compst)))
                            struct))))))
             ((mv event-member &)
              (evmac-generate-defthm thm-member-name
                                     :formula formula-member
                                     :hints hints-member
                                     :enable nil))
             ((mv event-memberp &)
              (evmac-generate-defthm thm-memberp-name
                                     :formula formula-memberp
                                     :hints hints-memberp
                                     :enable nil)))
          (mv (list event-member event-memberp)
              (list thm-member-name thm-memberp-name)
              names-to-avoid)))
       ((unless (type-case type :array))
        (prog2$
         (raise "Internal error: member type ~x0." type)
         (mv nil nil nil)))
       (elemtype (type-array->of type))
       ((unless (type-nonchar-integerp elemtype))
        (prog2$
         (raise "Internal error: array member element type ~x0." elemtype)
         (mv nil nil nil))))
    (atc-gen-tag-member-write-thms-aux tag
                                       recognizer
                                       fixer-recognizer-thm
                                       memname
                                       elemtype
                                       *nonchar-integer-types**
                                       (car writers)
                                       (car checkers)
                                       (cdr writers)
                                       (cdr checkers)
                                       writer-return-thm
                                       not-error-thm
                                       type-of-value-thm
                                       length
                                       names-to-avoid
                                       wrld))

  :prepwork
  ((define atc-gen-tag-member-write-thms-aux ((tag identp)
                                              (recognizer symbolp)
                                              (fixer-recognizer-thm symbolp)
                                              (memname identp)
                                              (elemtype typep)
                                              (indextypes type-listp)
                                              (writer-acl2int symbolp)
                                              (checker-acl2int symbolp)
                                              (writers symbol-listp)
                                              (checkers symbol-listp)
                                              (writer-return-thm symbolp)
                                              (not-error-thm symbolp)
                                              (type-of-value-thm symbolp)
                                              (length symbolp)
                                              (names-to-avoid symbol-listp)
                                              (wrld plist-worldp))
     :guard (and (type-nonchar-integerp elemtype)
                 (type-nonchar-integer-listp indextypes))
     :returns (mv (local-events pseudo-event-form-listp)
                  (member-write-thms symbol-listp)
                  (updated-names-to-avoid symbol-listp
                                          :hyp (symbol-listp names-to-avoid)))
     :parents nil
     (b* (((when (endp indextypes)) (mv nil nil nil))
          (indextype (car indextypes))
          (writer (car writers))
          (checker (car checkers))
          (indexfixtype (integer-type-to-fixtype indextype))
          (elemfixtype (integer-type-to-fixtype elemtype))
          (indextypep (pack indexfixtype 'p))
          (elemtypep (pack elemfixtype 'p))
          (indextype->get (pack indexfixtype '->get))
          (array-writer (pack elemfixtype '-array-write-alt-def))
          (array-checker (pack elemfixtype '-array-index-okp))
          (not-error-array-thm (pack 'not-errorp-when- elemfixtype '-arrayp))
          (kind-array-thm (pack 'value-kind-when- elemfixtype '-arrayp))
          (valuep-when-indextype (pack 'valuep-when- indextypep))
          (valuep-when-elemtypep (pack 'valuep-when- elemtypep))
          (type-thm (pack indexfixtype '->get$inline))
          (thm-member-name (pack 'exec-member-write-when-
                                 recognizer
                                 '-and-
                                 (ident->name memname)
                                 '-
                                 indexfixtype))
          ((mv thm-member-name names-to-avoid)
           (fresh-logical-name-with-$s-suffix thm-member-name
                                              nil
                                              names-to-avoid
                                              wrld))
          (thm-memberp-name (pack 'exec-memberp-write-when-
                                  recognizer
                                  '-and-
                                  (ident->name memname)
                                  '-
                                  indexfixtype))
          ((mv thm-memberp-name names-to-avoid)
           (fresh-logical-name-with-$s-suffix thm-memberp-name
                                              nil
                                              names-to-avoid
                                              wrld))
          (arrayp-of-arrary-write
           (pack elemfixtype '-arrayp-of- elemfixtype '-array-write))
          (check-hyp (if length
                         `(,checker idx struct)
                       `(,checker idx)))
          (formula-member
           `(implies (and (syntaxp (quotep e))
                          (equal (expr-kind e) :binary)
                          (equal (binop-kind (expr-binary->op e)) :asg)
                          (equal left (expr-binary->arg1 e))
                          (equal right (expr-binary->arg2 e))
                          (equal (expr-kind left) :arrsub)
                          (equal array (expr-arrsub->arr left))
                          (equal index (expr-arrsub->sub left))
                          (equal (expr-kind array) :member)
                          (equal target (expr-member->target array))
                          (equal member (expr-member->name array))
                          (equal (expr-kind target) :ident)
                          (equal member (ident ,(ident->name memname)))
                          (not (zp limit))
                          (equal var (expr-ident->get target))
                          (equal struct (read-var var compst))
                          (,recognizer struct)
                          (equal idx (exec-expr-pure index compst))
                          (,indextypep idx)
                          ,check-hyp
                          (equal val (exec-expr-pure right compst))
                          (,elemtypep val))
                     (equal (exec-expr-asg e compst fenv limit)
                            (write-var var
                                       (,writer idx val struct)
                                       compst))))
          (formula-memberp
           `(implies (and (syntaxp (quotep e))
                          (equal (expr-kind e) :binary)
                          (equal (binop-kind (expr-binary->op e)) :asg)
                          (equal left (expr-binary->arg1 e))
                          (equal right (expr-binary->arg2 e))
                          (equal (expr-kind left) :arrsub)
                          (equal array (expr-arrsub->arr left))
                          (equal index (expr-arrsub->sub left))
                          (equal (expr-kind array) :memberp)
                          (equal target (expr-memberp->target array))
                          (equal member (expr-memberp->name array))
                          (equal (expr-kind target) :ident)
                          (equal member (ident ,(ident->name memname)))
                          (not (zp limit))
                          (equal ptr (read-var (expr-ident->get target)
                                               compst))
                          (valuep ptr)
                          (value-case ptr :pointer)
                          (not (value-pointer-nullp ptr))
                          (equal (value-pointer->reftype ptr)
                                 (type-struct (ident ,(ident->name tag))))
                          (equal struct
                                 (read-object (value-pointer->designator ptr)
                                              compst))
                          (,recognizer struct)
                          (equal idx (exec-expr-pure index compst))
                          (,indextypep idx)
                          ,check-hyp
                          (equal val (exec-expr-pure right compst))
                          (,elemtypep val))
                     (equal (exec-expr-asg e compst fenv limit)
                            (write-object (value-pointer->designator ptr)
                                          (,writer idx val struct)
                                          compst))))
          (hints-member
           `(("Goal"
              :in-theory
              '(exec-expr-asg
                value-integer->get
                value-schar->get-to-schar->get
                value-uchar->get-to-uchar->get
                value-sshort->get-to-sshort->get
                value-ushort->get-to-ushort->get
                value-sint->get-to-sint->get
                value-uint->get-to-uint->get
                value-slong->get-to-slong->get
                value-ulong->get-to-ulong->get
                value-sllong->get-to-sllong->get
                value-ullong->get-to-ullong->get
                value-kind-when-scharp
                value-kind-when-ucharp
                value-kind-when-sshortp
                value-kind-when-ushortp
                value-kind-when-sintp
                value-kind-when-uintp
                value-kind-when-slongp
                value-kind-when-ulongp
                value-kind-when-sllongp
                value-kind-when-ullongp
                value-struct-read
                value-struct-write
                not-errorp-when-valuep
                value-integerp
                value-unsigned-integerp-alt-def
                value-signed-integerp-alt-def
                value-fix-when-valuep
                ifix
                integer-range-p
                (:e ident)
                (:compound-recognizer consp-when-ucharp)
                ,recognizer
                ,fixer-recognizer-thm
                ,not-error-thm
                ,type-of-value-thm
                ,kind-array-thm
                ,checker
                ,checker-acl2int
                ,writer
                ,writer-acl2int
                ,not-error-array-thm
                ,array-writer
                ,array-checker
                ,valuep-when-elemtypep
                ,valuep-when-indextype
                ,@*integer-value-disjoint-rules*
                (:t ,type-thm)
                ,@(and length (list length)))
              :use
              ((:instance
                ,writer-return-thm
                (index
                 (,indextype->get
                  (exec-expr-pure (expr-arrsub->sub (expr-binary->arg1 e))
                                  compst)))
                (val
                 (exec-expr-pure (expr-binary->arg2 e) compst))
                (struct
                 (read-var
                  (expr-ident->get
                   (expr-member->target
                    (expr-arrsub->arr (expr-binary->arg1 e))))
                  compst)))
               (:instance
                ,arrayp-of-arrary-write
                (array
                 (value-struct-read-aux
                  (ident ,(ident->name memname))
                  (value-struct->members
                   (read-var
                    (expr-ident->get
                     (expr-member->target
                      (expr-arrsub->arr (expr-binary->arg1 e))))
                    compst))))
                (index
                 (,indextype->get
                  (exec-expr-pure
                   (expr-arrsub->sub (expr-binary->arg1 e))
                   compst)))
                (element
                 (exec-expr-pure (expr-binary->arg2 e) compst)))))))
          (hints-memberp
           `(("Goal"
              :in-theory
              '(exec-expr-asg
                value-integer->get
                value-schar->get-to-schar->get
                value-uchar->get-to-uchar->get
                value-sshort->get-to-sshort->get
                value-ushort->get-to-ushort->get
                value-sint->get-to-sint->get
                value-uint->get-to-uint->get
                value-slong->get-to-slong->get
                value-ulong->get-to-ulong->get
                value-sllong->get-to-sllong->get
                value-ullong->get-to-ullong->get
                value-kind-when-scharp
                value-kind-when-ucharp
                value-kind-when-sshortp
                value-kind-when-ushortp
                value-kind-when-sintp
                value-kind-when-uintp
                value-kind-when-slongp
                value-kind-when-ulongp
                value-kind-when-sllongp
                value-kind-when-ullongp
                value-struct-read
                value-struct-write
                not-errorp-when-valuep
                value-integerp
                value-unsigned-integerp-alt-def
                value-signed-integerp-alt-def
                value-fix-when-valuep
                ifix
                integer-range-p
                (:e ident)
                (:compound-recognizer consp-when-ucharp)
                ,recognizer
                ,fixer-recognizer-thm
                ,not-error-thm
                ,type-of-value-thm
                ,kind-array-thm
                ,checker
                ,checker-acl2int
                ,writer
                ,writer-acl2int
                ,not-error-array-thm
                ,array-writer
                ,array-checker
                ,valuep-when-elemtypep
                ,valuep-when-indextype
                ,@*integer-value-disjoint-rules*
                (:t ,type-thm)
                ,@(and length (list length)))
              :use
              ((:instance
                ,writer-return-thm
                (index
                 (,indextype->get
                  (exec-expr-pure (expr-arrsub->sub (expr-binary->arg1 e))
                                  compst)))
                (val
                 (exec-expr-pure (expr-binary->arg2 e) compst))
                (struct
                 (read-object
                  (value-pointer->designator
                   (read-var
                    (expr-ident->get
                     (expr-memberp->target
                      (expr-arrsub->arr (expr-binary->arg1 e))))
                    compst))
                  compst)))
               (:instance
                ,arrayp-of-arrary-write
                (array
                 (value-struct-read-aux
                  (ident ,(ident->name memname))
                  (value-struct->members
                   (read-object
                    (value-pointer->designator
                     (read-var
                      (expr-ident->get
                       (expr-memberp->target
                        (expr-arrsub->arr (expr-binary->arg1 e))))
                      compst))
                    compst))))
                (index
                 (,indextype->get
                  (exec-expr-pure
                   (expr-arrsub->sub (expr-binary->arg1 e))
                   compst)))
                (element
                 (exec-expr-pure (expr-binary->arg2 e) compst)))))))
          ((mv event-member &)
           (evmac-generate-defthm thm-member-name
                                  :formula formula-member
                                  :hints hints-member
                                  :enable nil))
          ((mv event-memberp &)
           (evmac-generate-defthm thm-memberp-name
                                  :formula formula-memberp
                                  :hints hints-memberp
                                  :enable nil))
          ((mv events thm-names names-to-avoid)
           (atc-gen-tag-member-write-thms-aux tag
                                              recognizer
                                              fixer-recognizer-thm
                                              memname
                                              elemtype
                                              (cdr indextypes)
                                              writer-acl2int
                                              checker-acl2int
                                              (cdr writers)
                                              (cdr checkers)
                                              writer-return-thm
                                              not-error-thm
                                              type-of-value-thm
                                              length
                                              names-to-avoid
                                              wrld)))
       (mv (append (and (not length)
                        (list event-member))
                   (list event-memberp)
                   events)
           (append (and (not length)
                        (list thm-member-name))
                   (list thm-memberp-name)
                   thm-names)
           names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tag-member-write-all-thms
  ((tag identp)
   (recognizer symbolp)
   (fixer-recognizer-thm symbolp)
   (not-error-thm symbolp)
   (type-of-value-thm symbolp)
   (meminfos defstruct-member-info-listp)
   (names-to-avoid symbol-listp)
   (wrld plist-worldp))
  :returns (mv (local-events pseudo-event-form-listp)
               (member-write-thms symbol-listp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorems to rewrite @(tsee exec-expr-asg)
          with a @(':memberp') left expression
          to a structure writer,
          for all the members of a structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This relies on @('writers') and @('writer-return-thms')
     to be in the same order as @('members')."))
  (b* (((when (endp meminfos)) (mv nil nil names-to-avoid))
       ((mv events thms names-to-avoid)
        (atc-gen-tag-member-write-thms tag
                                       recognizer
                                       fixer-recognizer-thm
                                       not-error-thm
                                       type-of-value-thm
                                       (car meminfos)
                                       names-to-avoid
                                       wrld))
       ((mv more-events more-thms names-to-avoid)
        (atc-gen-tag-member-write-all-thms tag
                                           recognizer
                                           fixer-recognizer-thm
                                           not-error-thm
                                           type-of-value-thm
                                           (cdr meminfos)
                                           names-to-avoid
                                           wrld)))
    (mv (append events more-events)
        (append thms more-thms)
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-struct-declon-list ((meminfos member-type-listp))
  :returns (declons struct-declon-listp)
  :short "Generate a list of C structure declarations
          from a list of member types."
  (b* (((when (endp meminfos)) nil)
       (meminfo (car meminfos))
       ((member-type meminfo) meminfo)
       ((mv tyspec declor) (ident+type-to-tyspec+declor meminfo.name
                                                        meminfo.type))
       (declon (make-struct-declon :tyspec tyspec :declor declor))
       (declons (atc-gen-struct-declon-list (cdr meminfos))))
    (cons declon declons)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tag-declon ((tag stringp)
                            (info defstruct-infop)
                            (prec-tags atc-string-taginfo-alistp)
                            (proofs booleanp)
                            (names-to-avoid symbol-listp)
                            (wrld plist-worldp))
  :returns (mv (declon tag-declonp)
               (local-events pseudo-event-form-listp)
               (updated-prec-tags
                atc-string-taginfo-alistp
                :hyp (and (stringp tag)
                          (atc-string-taginfo-alistp prec-tags)))
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate a C structure type declaration,
          with accompanying theorems."
  (b* ((meminfos (defstruct-info->members info))
       (memtypes (defstruct-member-info-list->memtype-list meminfos))
       (tag-ident (defstruct-info->tag info))
       (recognizer (defstruct-info->recognizer info))
       (fixer-recognizer-thm (defstruct-info->fixer-recognizer-thm info))
       (not-error-thm (defstruct-info->not-error-thm info))
       (type-of-value-thm (defstruct-info->type-of-value-thm info))
       (struct-declons (atc-gen-struct-declon-list memtypes))
       ((mv read-thm-events read-thm-names names-to-avoid)
        (if proofs
            (atc-gen-tag-member-read-all-thms tag-ident
                                              recognizer
                                              fixer-recognizer-thm
                                              not-error-thm
                                              meminfos
                                              names-to-avoid
                                              wrld)
          (mv nil nil names-to-avoid)))
       ((mv write-thm-events write-thm-names names-to-avoid)
        (if proofs
            (atc-gen-tag-member-write-all-thms tag-ident
                                               recognizer
                                               fixer-recognizer-thm
                                               not-error-thm
                                               type-of-value-thm
                                               meminfos
                                               names-to-avoid
                                               wrld)
          (mv nil nil names-to-avoid)))
       (thm-events (append read-thm-events write-thm-events))
       (info (make-atc-tag-info :defstruct info
                                :member-read-thms read-thm-names
                                :member-write-thms write-thm-names))
       (prec-tags (acons tag info prec-tags)))
    (mv (make-tag-declon-struct :tag tag-ident :members struct-declons)
        thm-events
        prec-tags
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-obj-declon ((name stringp)
                            (info defobject-infop)
                            (prec-objs atc-string-objinfo-alistp))
  :returns (mv (declon obj-declonp)
               (updated-prec-objs atc-string-objinfo-alistp))
  :short "Generate a C external object definition."
  (b* ((id (defobject-info->name-ident info))
       (type (defobject-info->type info))
       (exprs (defobject-info->init info))
       ((mv tyspec declor) (ident+type-to-tyspec+declor id type))
       (initer? (if (consp exprs) (initer-list exprs) nil))
       (declon (make-obj-declon :tyspec tyspec
                                :declor declor
                                :init? initer?))
       (info (atc-obj-info info))
       (prec-objs (acons (str-fix name)
                         info
                         (atc-string-objinfo-alist-fix prec-objs))))
    (mv declon prec-objs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-ext-declon-list ((targets symbol-listp)
                                 (prec-fns atc-symbol-fninfo-alistp)
                                 (prec-tags atc-string-taginfo-alistp)
                                 (prec-objs atc-string-objinfo-alistp)
                                 (proofs booleanp)
                                 (prog-const symbolp)
                                 (init-fun-env-thm symbolp)
                                 (fn-thms symbol-symbol-alistp)
                                 (fn-appconds symbol-symbol-alistp)
                                 (appcond-thms keyword-symbol-alistp)
                                 (print evmac-input-print-p)
                                 (names-to-avoid symbol-listp)
                                 (ctx ctxp)
                                 state)
  :returns (mv erp
               (val (tuple (exts ext-declon-listp)
                           (local-events pseudo-event-form-listp)
                           (exported-events pseudo-event-form-listp)
                           (updated-names-to-avoid symbol-listp)
                           val)
                    :hyp (and (atc-symbol-fninfo-alistp prec-fns)
                              (symbol-listp names-to-avoid)))
               state)
  :short "Generate a list of C external declarations from the targets,
          including generating C loops from recursive ACL2 functions."
  (b* (((acl2::fun (irr)) (list nil nil nil nil))
       ((when (endp targets)) (acl2::value (list nil nil nil names-to-avoid)))
       (target (car targets))
       ((er (list exts
                  prec-fns
                  prec-tags
                  prec-objs
                  local-events
                  exported-events
                  names-to-avoid)
            :iferr (irr))
        (b* (((when (function-symbolp target (w state)))
              (b* ((fn target)
                   ((when (eq fn 'quote))
                    (raise "Internal error: QUOTE target function.")
                    (acl2::value (list nil nil nil nil nil nil nil)))
                   ((unless (logicp fn (w state)))
                    (raise "Internal error: ~x0 not in logic mode." fn)
                    (acl2::value (list nil nil nil nil nil nil nil)))
                   ((er (list exts
                              prec-fns
                              local-events
                              exported-events
                              names-to-avoid)
                        :iferr (list nil nil nil nil nil))
                    (if (irecursivep+ fn (w state))
                        (b* (((er (list local-events
                                        exported-events
                                        prec-fns
                                        names-to-avoid)
                                  :iferr (list nil nil nil nil nil))
                              (atc-gen-loop fn prec-fns prec-tags prec-objs
                                            proofs prog-const
                                            fn-thms fn-appconds appcond-thms
                                            print names-to-avoid ctx state)))
                          (acl2::value (list nil
                                             prec-fns
                                             local-events
                                             exported-events
                                             names-to-avoid)))
                      (b* (((er (list fundef
                                      local-events
                                      exported-events
                                      prec-fns
                                      names-to-avoid)
                                :iferr (list nil nil nil nil nil))
                            (atc-gen-fundef fn prec-fns prec-tags prec-objs
                                            proofs
                                            prog-const
                                            init-fun-env-thm fn-thms
                                            print names-to-avoid ctx state))
                           (ext (ext-declon-fundef fundef)))
                        (acl2::value (list (list ext)
                                           prec-fns
                                           local-events
                                           exported-events
                                           names-to-avoid))))))
                (acl2::value
                 (list exts
                       prec-fns
                       prec-tags
                       prec-objs
                       local-events
                       exported-events
                       names-to-avoid))))
             (name (symbol-name target))
             (info (defstruct-table-lookup name (w state)))
             ((when info)
              (b* (((mv tag-declon tag-thms prec-tags names-to-avoid)
                    (atc-gen-tag-declon name info prec-tags proofs
                                        names-to-avoid (w state)))
                   (ext (ext-declon-tag-declon tag-declon)))
                (acl2::value
                 (list (list ext)
                       prec-fns
                       prec-tags
                       prec-objs
                       tag-thms
                       nil
                       names-to-avoid))))
             (info (defobject-table-lookup name (w state)))
             ((when info)
              (b* (((mv obj-declon prec-objs)
                    (atc-gen-obj-declon name info prec-objs))
                   (ext (ext-declon-obj-declon obj-declon)))
                (acl2::value
                 (list (list ext)
                       prec-fns
                       prec-tags
                       prec-objs
                       nil
                       nil
                       names-to-avoid)))))
          (acl2::value
           (prog2$ (raise "Internal error: ~
                           target ~x0 is not ~
                           a function or DEFSTRUCT or DEFOBJECT."
                          target)
                   (list nil nil nil nil nil nil nil)))))
       ((er (list more-exts
                  more-local-events
                  more-exported-events
                  names-to-avoid))
        (atc-gen-ext-declon-list (cdr targets) prec-fns prec-tags prec-objs
                                 proofs prog-const
                                 init-fun-env-thm fn-thms
                                 fn-appconds appcond-thms
                                 print names-to-avoid ctx state)))
    (acl2::value (list (append exts more-exts)
                       (append local-events more-local-events)
                       (append exported-events more-exported-events)
                       names-to-avoid)))

  :prepwork
  ((local
    (in-theory
     ;; to speed up proofs, based on accumulated persistence:
     (disable
      acl2::consp-of-car-when-alistp
      acl2::subsetp-when-atom-right
      acl2::subsetp-car-member
      acl2::alistp-of-cdr
      default-symbol-name
      acl2::symbolp-when-member-equal-of-symbol-listp
      omap::alistp-when-mapp
      pseudo-event-form-listp
      acl2::alistp-when-hons-duplicity-alist-p
      acl2::pseudo-event-formp-when-member-equal-of-pseudo-event-form-listp
      acl2::subsetp-when-atom-left
      acl2::alistp-when-atom
      acl2::hons-duplicity-alist-p-when-not-consp
      member-equal
      acl2::subsetp-implies-subsetp-cdr
      acl2::pseudo-event-form-listp-of-cdr-when-pseudo-event-form-listp
      omap::mfix-implies-mapp
      mapp-when-scopep
      omap::mapp-when-not-empty
      default-cdr))))

  :verify-guards nil ; done below

  ///

  (more-returns
   (val true-listp :rule-classes :type-prescription))

  (verify-guards atc-gen-ext-declon-list
    :hints
    (("Goal"
      :in-theory
      (enable acl2::true-listp-when-pseudo-event-form-listp-rewrite)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-prog-const ((prog-const symbolp)
                            (file filep)
                            (print evmac-input-print-p))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the named constant for the abstract syntax tree
          of the generated C code (i.e. C file)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This constant is not generated if @(':proofs') is @('nil')."))
  (b* ((progress-start?
        (and (evmac-input-print->= print :info)
             `((cw-event "~%Generating the named constant..."))))
       (progress-end? (and (evmac-input-print->= print :info)
                           `((cw-event " done.~%"))))
       (defconst-event `(defconst ,prog-const ',file))
       (local-event `(progn ,@progress-start?
                            (local ,defconst-event)
                            ,@progress-end?)))
    (mv local-event defconst-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-wf-thm ((proofs booleanp)
                        (prog-const symbolp)
                        (wf-thm symbolp)
                        (print evmac-input-print-p))
  :returns (mv (local-events pseudo-event-form-listp)
               (exported-events pseudo-event-form-listp))
  :short "Generate the theorem asserting
          the static well-formedness of the generated C code
          (referenced as the named constant)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since this is a ground theorem,
     we expect that it should be easily provable
     using just the executable counterpart of @(tsee check-file),
     which is an executable function.")
   (xdoc::p
    "We generate singleton lists of events if @(':proofs') is @('t'),
     empty lists otherwise."))
  (b* (((unless proofs) (mv nil nil))
       ((mv local-event exported-event)
        (evmac-generate-defthm
         wf-thm
         :formula `(equal (check-file ,prog-const) :wellformed)
         :hints '(("Goal" :in-theory '((:e check-file))))
         :enable nil))
       (progress-start?
        (and (evmac-input-print->= print :info)
             `((cw-event "~%Generating the well-formedness theorem..."))))
       (progress-end? (and (evmac-input-print->= print :info)
                           `((cw-event " done.~%"))))
       (local-event `(progn ,@progress-start?
                            ,local-event
                            ,@progress-end?)))
    (mv (list local-event)
        (list exported-event))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-init-fun-env-thm ((init-fun-env-thm symbolp)
                                  (proofs booleanp)
                                  (prog-const symbolp)
                                  (file filep))
  :returns (local-events pseudo-event-form-listp)
  :short "Generate the theorem asserting that
          applying @(tsee init-fun-env) to the translation unit
          gives the corresponding function environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The rationale for generating this theorem
     is explained in @(tsee atc-gen-cfile)."))
  (b* (((unless proofs) nil)
       (tunit (preprocess file))
       ((when (errorp tunit))
        (raise "Internal error: preprocessing of ~x0 fails with error ~x1."
               file tunit))
       (fenv (init-fun-env tunit))
       ((when (errorp fenv))
        (raise "Internal error: ~
                function environment initialization of ~x0 ~
                fails with error ~x1."
               tunit fenv))
       (formula `(equal (init-fun-env (preprocess ,prog-const))
                        ',fenv))
       (hints '(("Goal" :in-theory '((:e preprocess)
                                     (:e init-fun-env)))))
       ((mv event &)
        (evmac-generate-defthm init-fun-env-thm
                               :formula formula
                               :hints hints
                               :enable nil)))
    (list event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfile ((targets symbol-listp)
                       (proofs booleanp)
                       (prog-const symbolp)
                       (wf-thm symbolp)
                       (fn-thms symbol-symbol-alistp)
                       (print evmac-input-print-p)
                       (names-to-avoid symbol-listp)
                       (ctx ctxp)
                       state)
  :returns (mv erp
               (val (tuple (file filep)
                           (local-events pseudo-event-form-listp)
                           (exported-events pseudo-event-form-listp)
                           (updated-names-to-avoid symbol-listp)
                           val)
                    :hyp (symbol-listp names-to-avoid))
               state)
  :short "Generate a C file from the ATC targets, and accompanying events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does not yet generate an actual file in the file system;
     it generates an abstract syntactic C file.")
   (xdoc::p
    "In order to speed up the proofs of
     the generated theorems for the function environment
     for relatively large C programs,
     we generate a theorem to ``cache''
     the result of calling @(tsee init-fun-env)
     on the generated translation unit
     (obtained by preprocessing the generated C file),
     to avoid recomputing that for every function environment theorem.
     We need to generate the name of this (local) theorem
     before generating the function environment theorems,
     so that those theorems can use the name of this theorem in the hints;
     but we can only generate the theorem
     after generating the translation unit.
     So first we generate the name,
     then we generate the translation unit,
     and then we generate the theorem;
     however, in the generated events,
     we put that theorem before the ones for the functions."))
  (b* (((acl2::fun (irr)) (list (ec-call (file-fix :irrelevant)) nil nil nil))
       ((mv appcond-local-events fn-appconds appcond-thms names-to-avoid)
        (if proofs
            (b* (((mv appconds fn-appconds)
                  (atc-gen-appconds targets (w state)))
                 ((mv appcond-events appcond-thms & names-to-avoid)
                  (evmac-appcond-theorem-list appconds nil names-to-avoid
                                              print ctx state)))
              (mv appcond-events fn-appconds appcond-thms names-to-avoid))
          (mv nil nil nil nil)))
       ((mv wf-thm-local-events wf-thm-exported-events)
        (atc-gen-wf-thm proofs prog-const wf-thm print))
       (init-fun-env-thm (add-suffix prog-const "-FUN-ENV"))
       ((mv init-fun-env-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix init-fun-env-thm
                                           nil
                                           names-to-avoid
                                           (w state)))
       ((er (list exts
                  fn-thm-local-events
                  fn-thm-exported-events
                  names-to-avoid)
            :iferr (irr))
        (atc-gen-ext-declon-list targets nil nil nil proofs
                                 prog-const init-fun-env-thm
                                 fn-thms fn-appconds appcond-thms
                                 print names-to-avoid ctx state))
       (file (make-file :declons exts))
       (local-init-fun-env-events (atc-gen-init-fun-env-thm init-fun-env-thm
                                                            proofs
                                                            prog-const
                                                            file))
       ((mv local-const-event exported-const-event)
        (if proofs
            (atc-gen-prog-const prog-const file print)
          (mv nil nil)))
       (local-events (append appcond-local-events
                             (and proofs (list local-const-event))
                             wf-thm-local-events
                             local-init-fun-env-events
                             fn-thm-local-events))
       (exported-events (append (and proofs (list exported-const-event))
                                wf-thm-exported-events
                                fn-thm-exported-events)))
    (acl2::value (list file
                       local-events
                       exported-events
                       names-to-avoid)))
  ///
  (more-returns
   (val true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-outfile ((file filep)
                         (output-file stringp)
                         (pretty-printing pprint-options-p)
                         state)
  :returns (mv erp val state)
  :mode :program
  :short "Pretty-print the generated C code (i.e. C file) to the output file."
  :long
  (xdoc::topstring
   (xdoc::p
    "This actually writes the file to disk, in the file system."))
  (b* ((lines (pprint-file file pretty-printing)))
    (pprinted-lines-to-file lines output-file state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-outfile-event ((file filep)
                               (output-file stringp)
                               (pretty-printing pprint-options-p)
                               (print evmac-input-print-p)
                               state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Event to pretty-print the generated C code to the output file."
  :long
  (xdoc::topstring
   (xdoc::p
    "This serves to run @(tsee atc-gen-outfile)
     after the constant and theorem events have been submitted.
     This function generates an event form
     that is put (by @(tsee atc-gen-everything))
     after the constant and theorem events.
     When the events are submitted to and processed by ACL2,
     we get to this file generation event
     only if the previous events are successful.
     This is a sort of safety/security constraint:
     do not even generate the output file, unless it is correct.")
   (xdoc::p
    "If @(':print') is @(':info') or @(':all'),
     we also generate events to print progress messages,
     as done with the constant and theorem events.")
   (xdoc::p
    "In order to generate an embedded event form for output file generation,
     we generate a @(tsee make-event) whose argument generates the file.
     The argument must also return an embedded event form,
     so we use @(tsee value-triple) with @(':invisible'),
     so there is no extra screen output.
     This is a ``dummy'' event, which is not supposed to do anything:
     it is the execution of the @(tsee make-event) argument
     that matters, because it generates the output file.
     In essence, we use @(tsee make-event) to turn a computation
     (the one that generates the output file)
     into an event.
     But we cannot use just @(tsee value-triple)
     because our computation returns an error triple."))
  (b* ((progress-start?
        (and (evmac-input-print->= print :info)
             `((cw-event "~%Generating the file..." ',output-file))))
       (progress-end? (and (evmac-input-print->= print :info)
                           `((cw-event " done.~%"))))
       (file-gen-event
        `(make-event
          (b* (((er &) (atc-gen-outfile ',file
                                        ,output-file
                                        ',pretty-printing
                                        state)))
            (acl2::value '(value-triple :invisible))))))
    (acl2::value `(progn ,@progress-start?
                         ,file-gen-event
                         ,@progress-end?))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-print-result ((events pseudo-event-form-listp)
                              (output-file stringp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the events to print the results of ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used only if @(':print') is at least @(':result')."))
  (append (atc-gen-print-result-aux events)
          (list `(cw-event "~%File ~s0.~%" ,output-file)))
  :prepwork
  ((define atc-gen-print-result-aux ((events pseudo-event-form-listp))
     :returns (events pseudo-event-form-listp)
     (cond ((endp events) nil)
           (t (cons `(cw-event "~%~x0~|" ',(car events))
                    (atc-gen-print-result-aux (cdr events))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-everything ((targets symbol-listp)
                            (output-file stringp)
                            (pretty-printing pprint-options-p)
                            (proofs booleanp)
                            (prog-const symbolp)
                            (wf-thm symbolp)
                            (fn-thms symbol-symbol-alistp)
                            (print evmac-input-print-p)
                            (call pseudo-event-formp)
                            (ctx ctxp)
                            state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Generate the file and the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "We locally install the ``trivial ancestor check'' from the library.
     We found at least a case in which ACL2's default heuristic ancestor check
     prevented a valid functional correctness theorem from being proved.
     Since by construction the symbolic execution shoud always terminate,
     it does not seem like ACL2's heuristic ancestor check
     would ever be helpful (if this turns out to be wrong, we will re-evaluate).
     Thus, we locally install the simpler ancestor check.")
   (xdoc::p
    "We also (locally, implicitly) allow variables to be ignored.
     Ignored variables may arise in the correctness theorems for loop bodies:
     @(tsee atc-loop-body-term-subst) replaces recursive calls,
     which include all the formals of the loop function,
     with just the affected variables, which may be a subset of the formals;
     if the call is the body of a @(tsee let),
     the formals that are not affected then become ignored."))
  (b* ((names-to-avoid (list* prog-const wf-thm (strip-cdrs fn-thms)))
       ((er (list file local-events exported-events &) :iferr '(_))
        (atc-gen-cfile targets proofs prog-const wf-thm fn-thms
                       print names-to-avoid ctx state))
       ((er file-gen-event) (atc-gen-outfile-event file
                                                   output-file
                                                   pretty-printing
                                                   print
                                                   state))
       (print-events (and (evmac-input-print->= print :result)
                          (atc-gen-print-result exported-events output-file)))
       (encapsulate
           `(encapsulate ()
              (evmac-prepare-proofs)
              (local (acl2::use-trivial-ancestors-check))
              (set-ignore-ok t)
              ,@local-events
              ,@exported-events
              ,file-gen-event))
       (encapsulate+ (restore-output? (eq print :all) encapsulate))
       (info (make-atc-call-info :encapsulate encapsulate))
       (table-event (atc-table-record-event call info)))
    (acl2::value `(progn ,encapsulate+
                         ,table-event
                         ,@print-events
                         (value-triple :invisible))))
  :guard-hints
  (("Goal"
    :in-theory
    (enable acl2::true-listp-when-pseudo-event-form-listp-rewrite))))
