; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "proof-generation-theorems")

(include-book "../syntax/ascii-identifiers")
(include-book "../syntax/unambiguity")
(include-book "../syntax/validation-information")

(include-book "kestrel/fty/pseudo-event-form-list" :dir :system)

(local (include-book "std/typed-lists/atom-listp" :dir :system))

(local (in-theory (enable* c$::abstract-syntax-aidentp-rules)))
(local (in-theory (enable* c$::abstract-syntax-unambp-rules)))
(local (in-theory (enable* c$::abstract-syntax-annop-rules)))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ proof-generation
  :parents (transformation-tools)
  :short "Proof generation utilities."
  :long
  (xdoc::topstring
   (xdoc::p
    "We collect some proof generation utilities
     that should be of general use.")
   (xdoc::p
    "ACL2 functions that carry out proof-generating transformations
     have certain general inputs and outputs that are independent from
     the constructs being transformed and even the specific transformations.
     We provide data structures @(tsee gin) and @(tsee gout)
     for these general inputs and outputs (the @('g') stands for `general').")
   (xdoc::p
    "We provide functions to generate theorems for expression, statements, etc.
     These functions take the old and new constructs as inputs,
     which must be in the formalized subset,
     and in some cases must satisfy additional restrictions.
     The callers check these conditions,
     but they are double-checked here,
     throwing hard errors if not satisfied, which should never happen.")
   (xdoc::p
    "The theorems generated for the various constructs say that:")
   (xdoc::ul
    (xdoc::li
     "If the execution of the old construct does not yield an error,
      neither does the execution of the new construct,
      and the two executions return the same results.")
    (xdoc::li
     "If applicable to the construct,
      the type of the result is consistent with the type, or set of types,
      statically determined by the validator for the construct.
      For statements and some other constructs,
      the sets of types are actually sets of optional types,
      where @('nil') indicates termination without a @('return').
      A @('void') type indicates termination with a @('return') without value.
      Any other type indicates termination with a @('return')
      with a value of that type.")
    (xdoc::li
     "If applicable to the construct,
      if the computation state before the construct
      includes certain variables with values of certain types,
      the computation state after the construct
      includes certain variables with values of certain types.
      These are sometimes the same variables (e.g. for assignments),
      but other times there are more variables at the end
      (e.g. for declarations)."))
   (xdoc::p
    "Some transformations turn C constructs into semantically equal ones.
     If the sub-constructs of a super-construct
     are turned into semantically equal ones,
     with theorems asserting that semantic equalities,
     those equalities can be lifted to the super-construct,
     and a theorem for the super-construct can be generated,
     with a proof that makes use of the theorems for the sub-constructs.
     We provide some utilities to lift equalities in the manner just explained.
     Together with the equalities, the theorems also assert
     facts about the types of the constructs involved;
     perhaps these could be teased apart in the future.
     We also expect to generalize equalities to more complex relations,
     in these or in other utilities in the future.
     The utilities for these equality lifting have names
     starting with @('xeq'), to convey the idea of
     transformations (@('x')) according to equalities (@('eq'))."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod gin
  :short "General inputs for transformation functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The transformation functions take as input the construct to transform,
     which has a different type for each transformation function.
     But each function also takes certain common inputs,
     which we put into this data structure
     for modularity and to facilitate extension."))
  ((ienv ienv
         "The implementation environment from the code ensemble.")
   (const-new symbol
              "The @(':const-new') input of the transformation.")
   (vartys c::ident-type-map
           "Some variables in scope at the beginning of the construct.
            The generated theorem (if any)
            includes hypotheses about their presence in the computation state
            before the execution of the C construct.
            Currently this could be actually a subset of the variables in scope,
            but it is adequate to the current proof generation,
            and we are working on extending this.")
   (events pseudo-event-form-list
           "Theorems generated so far, in reverse order.")
   (thm-index pos
              "Index used to generate unique theorem names."))
  :pred ginp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod gout
  :short "General outputs for transformation functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The transformation functions return as output the transformed construct,
     which has a different type for each transformation function.
     But each function also returns certain common outputs,
     which we put into this data structure
     for modularity and to facilitate extension."))
  ((events pseudo-event-form-list
           "Theorems generated so far, in reverse order.")
   (thm-index pos
              "Index used to generate unique theorem names.")
   (thm-name symbol
             "Name of the theorem generated by the transformation function.
              The theorem concerns the transformation of the C construct
              that the transformation function operates on.
              This is @('nil') if no theorem is generated.")
   (vartys c::ident-type-map
           "Some variables in scope at the end of the construct.
            The generated theorem (if any)
            includes conclusions about their presence in the computation state
            after the execution of the construct.
            This does not necessarily include all the variables in scope,
            because for certain constructs (e.g. lists of block items)
            we only consider variables that are also in scope
            at the beginning of the construct, i.e. that occur in
            the @('vartys') component of @(tsee gin)."))
  :pred goutp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-gout
  :short "Irrelevant general outputs for transformation functions."
  :type goutp
  :body (make-gout :events nil
                   :thm-index 1
                   :thm-name nil
                   :vartys nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gin-update ((gin ginp) (gout goutp))
  :returns (new-gin ginp)
  :short "Update a @(tsee gin) with a @(tsee gout)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list of theorems generated so far
     and the index for unique theorem names
     are threaded through the transformation functions;
     both are common components of
     @(tsee gin) and @(tsee gout).
     This function updates an input
     (to the next call of a transformation function)
     with an output
     (from the previous call of a transformation function),
     by updating those common components.")
   (xdoc::p
    "Although both @(tsee gin) and @(tsee gout)
     have a @('vartys') component, that one is not threaded through;
     it is handled differently (see the transformation functions).
     Thus, this function does not involve that component."))
  (b* (((gout gout) gout))
    (change-gin gin
                :events gout.events
                :thm-index gout.thm-index))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gout-no-thm ((gin ginp))
  :returns (gout goutp)
  :short "Build a @(tsee gout) without a theorem name."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for constructs for which we do not generate proofs yet.
     The events, theorem index, and variable-type map
     are taken from a @(tsee gin),
     as they result from previous transformations."))
  (b* (((gin gin) gin))
    (make-gout :events gin.events
               :thm-index gin.thm-index
               :thm-name nil
               :vartys gin.vartys))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-var-assertions ((vartys c::ident-type-mapp)
                            (compst "An untranslated term."))
  :returns (assertions true-listp)
  :short "Generate assertions about certain variables
          having values of certain types in a computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variables and their types are in the @('vartys') map.
     For each variable in the map,
     we generate an assertion saying that
     the variable can be read from the computation state
     and it contains a value of the associated type.")
   (xdoc::p
    "The input @('compst') is the (untranslated) term
     to use for the computation state (often just a variable)."))
  (b* (((when (omap::emptyp (c::ident-type-map-fix vartys))) nil)
       ((mv var type) (omap::head vartys))
       (asrt `(c::compustate-has-var-with-type-p ',var ',type ,compst))
       (asrts (gen-var-assertions (omap::tail vartys) compst)))
    (cons asrt asrts))
  ///
  (fty::deffixequiv gen-var-assertions
    :args ((vartys c::ident-type-mapp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-thm-name ((const-new symbolp) (thm-index posp))
  :returns (mv (name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem name."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is formed from the name of the constant for the new code
     and an increasing index.
     This function also increases and return the index.")
   (xdoc::p
    "For greater robustness,
     this function should ensure that the theorem name
     is not already present in the ACL2 works,
     and is not already present in a list of names to avoid;
     the latter list would consist of names that
     have been already used for generating events
     that have not been submitted to ACL2 yet
     (e.g. theorem names from a tool used before this transformation).
     But for now we do not perform these checks,
     since they are unlikely to fail anyhow.
     Note that, due to the increasing indices,
     we would not use the list of names to avoid for
     the theorems generated by this transformation."))
  (b* ((name (packn-pos (list const-new '-thm- thm-index) const-new))
       (thm-index (1+ (pos-fix thm-index))))
    (mv name thm-index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-expr-pure-thm ((old exprp)
                           (new exprp)
                           (vartys c::ident-type-mapp)
                           (const-new symbolp)
                           (thm-index posp)
                           (hints true-listp))
  :guard (and (expr-unambp old)
              (expr-annop old)
              (expr-unambp new)
              (expr-annop new))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem for the transformation of a pure expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "We are in the process of transitioning theorem generation for expressions
     from this function to @(tsee gen-expr-thm),
     while at the same time we are extending and generalizing
     our dynamic semantics of C.
     When that transition is completed,
     we will eliminate this function."))
  (b* ((old (expr-fix old))
       (new (expr-fix new))
       ((unless (expr-pure-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (expr-pure-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       (type (expr-type old))
       ((unless (equal (expr-type new)
                       type))
        (raise "Internal error: ~
                the type ~x0 of the new expression ~x1 differs from ~
                the type ~x2 of the old expression ~x3."
               (expr-type new) new type old)
        (mv '(_) nil 1))
       ((unless (type-formalp type))
        (raise "Internal error: expression ~x0 has type ~x1." old type)
        (mv '(_) nil 1))
       ((mv & old-expr) (ldm-expr old)) ; ERP is NIL because FORMALP
       ((mv & new-expr) (ldm-expr new)) ; ERP is NIL because FORMALP
       ((mv & ctype) (ldm-type type)) ; ERP is NIL because FORMALP
       (vars-pre (gen-var-assertions vartys 'compst))
       (formula
        `(b* ((old-expr ',old-expr)
              (new-expr ',new-expr)
              (old-result (c::exec-expr-pure old-expr compst))
              (new-result (c::exec-expr-pure new-expr compst))
              (old-value (c::expr-value->value old-result))
              (new-value (c::expr-value->value new-result)))
           (implies (and ,@vars-pre
                         (not (c::errorp old-result)))
                    (and (not (c::errorp new-result))
                         (equal old-value new-value)
                         (equal (c::type-of-value old-value) ',ctype)))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event `(defrule ,thm-name
                     ,formula
                     :rule-classes nil
                     :hints ,hints)))
    (mv thm-event thm-name thm-index))
  ///
  (fty::deffixequiv gen-expr-pure-thm
    :args ((old exprp) (new exprp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-expr-pure-thm ((old exprp)
                            (new exprp)
                            (expr-pure-thm symbolp)
                            (vartys c::ident-type-mapp)
                            (const-new symbolp)
                            (thm-index posp))
  :guard (and (expr-unambp old)
              (expr-annop old)
              (expr-unambp new)
              (expr-annop new))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Lift a theorem for a pure expression
          from @(tsee c::exec-expr-pure) to @(tsee c::exec-expr)."
  :long
  (xdoc::topstring
   (xdoc::p
    "As noted in @(tsee gen-expr-pure-thm),
     we are transitioning from that function to @(tsee gen-expr-thm).
     When the transition is completed, and that function is eliminated,
     this function will be eliminated as well."))
  (b* ((old (expr-fix old))
       (new (expr-fix new))
       ((unless (expr-pure-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (expr-pure-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       (type (expr-type old))
       ((unless (equal (expr-type new)
                       type))
        (raise "Internal error: ~
                the type ~x0 of the new expression ~x1 differs from ~
                the type ~x2 of the old expression ~x3."
               (expr-type new) new type old)
        (mv '(_) nil 1))
       (vars-pre (gen-var-assertions vartys 'compst))
       ((unless (type-formalp type))
        (raise "Internal error: expression ~x0 has type ~x1." old type)
        (mv '(_) nil 1))
       ((mv & old-expr) (ldm-expr old)) ; ERP is NIL because FORMALP
       ((mv & new-expr) (ldm-expr new)) ; ERP is NIL because FORMALP
       ((mv & ctype) (ldm-type type)) ; ERP is NIL because FORMALP
       (formula
        `(b* ((old-expr ',old-expr)
              (new-expr ',new-expr)
              ((mv old-result old-compst)
               (c::exec-expr old-expr compst old-fenv limit))
              ((mv new-result new-compst)
               (c::exec-expr new-expr compst new-fenv limit))
              (old-value (c::expr-value->value old-result))
              (new-value (c::expr-value->value new-result)))
           (implies (and ,@vars-pre
                         (not (c::errorp old-result)))
                    (and (not (c::errorp new-result))
                         (iff old-result new-result)
                         (equal old-value new-value)
                         (equal old-compst new-compst)
                         old-value
                         (equal (c::type-of-value old-value) ',ctype)))))
       (hints `(("Goal"
                 :use (,expr-pure-thm
                       (:instance expr-pure-congruence
                                  (old ',old-expr)
                                  (new ',new-expr)))
                 :in-theory '(c::exec-expr
                              c::exec-expr-pure-when-const
                              c::errorp-of-error
                              (:e c::expr-purep)
                              (:e c::expr-kind)
                              (:e c::expr-binary->op)
                              (:e c::binop-kind)
                              (:e c::type-nonchar-integerp)
                              (:e c::expr-pure-limit)
                              (:t c::exec-expr-pure)
                              (:t c::expr-value->value)))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event
        `(defrule ,thm-name
           ,formula
           :rule-classes nil
           :hints ,hints)))
    (mv thm-event thm-name thm-index))
  ///
  (fty::deffixequiv lift-expr-pure-thm
    :args ((old exprp) (new exprp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-expr-thm ((old exprp)
                      (new exprp)
                      (vartys c::ident-type-mapp)
                      (const-new symbolp)
                      (thm-index posp)
                      (hints true-listp))
  :guard (and (expr-unambp old)
              (expr-annop old)
              (expr-unambp new)
              (expr-annop new))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem for the transformation of an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "As noted in @(tsee gen-expr-pure-thm),
     we are transitioning from that function to this function.
     During the transition, this function generates, as an additional conjunct,
     the same formula generated by @(tsee gen-expr-pure-thm),
     if the expression is pure,
     in order to facilitate the mixed use of this and that function.
     Once we have completed the transition,
     we will eliminate the additional conjunct."))
  (b* ((old (expr-fix old))
       (new (expr-fix new))
       ((unless (expr-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (expr-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       (type (expr-type old))
       ((unless (equal (expr-type new)
                       type))
        (raise "Internal error: ~
                the type ~x0 of the new expression ~x1 differs from ~
                the type ~x2 of the old expression ~x3."
               (expr-type new) new type old)
        (mv '(_) nil 1))
       ((unless (type-formalp type))
        (raise "Internal error: expression ~x0 has type ~x1." old type)
        (mv '(_) nil 1))
       ((mv & old-expr) (ldm-expr old)) ; ERP is NIL because FORMALP
       ((mv & new-expr) (ldm-expr new)) ; ERP is NIL because FORMALP
       ((mv & ctype) (ldm-type type)) ; ERP is NIL because FORMALP
       (vars-pre (gen-var-assertions vartys 'compst))
       (vars-post (gen-var-assertions vartys 'old-compst))
       (formula
        `(b* ((old-expr ',old-expr)
              (new-expr ',new-expr)
              ((mv old-result old-compst)
               (c::exec-expr old-expr compst old-fenv limit))
              ((mv new-result new-compst)
               (c::exec-expr new-expr compst new-fenv limit))
              (old-value (c::expr-value->value old-result))
              (new-value (c::expr-value->value new-result)))
           (implies (and ,@vars-pre
                         (not (c::errorp old-result)))
                    (and (not (c::errorp new-result))
                         (iff old-result new-result)
                         (equal old-value new-value)
                         (equal old-compst new-compst)
                         ,@(if (c::type-case ctype :void)
                               '((not old-result))
                             `(old-result
                               (equal (c::type-of-value old-value) ',ctype)))
                         ,@vars-post))))
       (formula2 ; additional conjunct (see doc above)
        `(b* ((old-expr ',old-expr)
              (new-expr ',new-expr)
              (old-result (c::exec-expr-pure old-expr compst))
              (new-result (c::exec-expr-pure new-expr compst))
              (old-value (c::expr-value->value old-result))
              (new-value (c::expr-value->value new-result)))
           (implies (and ,@vars-pre
                         (not (c::errorp old-result)))
                    (and (not (c::errorp new-result))
                         (equal old-value new-value)
                         (equal (c::type-of-value old-value) ',ctype)))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event `(defrule ,thm-name
                     ,(if (expr-purep old)
                          `(and ,formula ,formula2)
                        formula)
                     :rule-classes nil
                     :hints ,hints)))
    (mv thm-event thm-name thm-index))
  ///
  (fty::deffixequiv gen-expr-thm
    :args ((old exprp) (new exprp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-initer-single-thm ((old initerp)
                               (new initerp)
                               (vartys c::ident-type-mapp)
                               (const-new symbolp)
                               (thm-index posp)
                               (hints true-listp))
  :guard (and (initer-case old :single)
              (initer-case new :single)
              (initer-unambp old)
              (initer-annop old)
              (initer-unambp new)
              (initer-annop new))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem for the transformation of a single initializer."
  (b* ((old (initer-fix old))
       (new (initer-fix new))
       ((unless (initer-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (initer-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       (type (initer-type old))
       ((unless (equal (initer-type new)
                       type))
        (raise "Internal error: ~
                the type ~x0 of the new initializer ~x1 differs from ~
                the type ~x2 of the old initializer ~x3."
               (initer-type new) new type old)
        (mv '(_) nil 1))
       (vars-pre (gen-var-assertions vartys 'compst))
       (vars-post (gen-var-assertions vartys 'old-compst))
       ((unless (type-formalp type))
        (raise "Internal error: initializer ~x0 has type ~x1." old type)
        (mv '(_) nil 1))
       ((mv & old-initer) (ldm-initer old)) ; ERP is NIL because FORMALP
       ((mv & new-initer) (ldm-initer new)) ; ERP is NIL because FORMALP
       ((mv & ctype) (ldm-type type)) ; ERP is NIL because FORMALP
       (formula
        `(b* ((old-initer ',old-initer)
              (new-initer ',new-initer)
              ((mv old-result old-compst)
               (c::exec-initer old-initer compst old-fenv limit))
              ((mv new-result new-compst)
               (c::exec-initer new-initer compst new-fenv limit)))
           (implies (and (> (c::compustate-frames-number compst) 0)
                         ,@vars-pre
                         (not (c::errorp old-result)))
                    (and (not (c::errorp new-result))
                         (equal old-result new-result)
                         (equal old-compst new-compst)
                         (equal (c::init-type-of-init-value old-result)
                                (c::init-type-single ',ctype))
                         ,@vars-post))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event
        `(defrule ,thm-name
           ,formula
           :rule-classes nil
           :hints ,hints)))
    (mv thm-event thm-name thm-index))
  ///
  (fty::deffixequiv gen-initer-single-thm
    :args ((old initerp) (new initerp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-stmt-thm ((old stmtp)
                      (new stmtp)
                      (vartys c::ident-type-mapp)
                      (const-new symbolp)
                      (thm-index posp)
                      (hints true-listp))
  :guard (and (stmt-unambp old)
              (stmt-annop old)
              (stmt-unambp new)
              (stmt-annop new))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem for the transformation of a statement."
  (b* ((old (stmt-fix old))
       (new (stmt-fix new))
       ((unless (stmt-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (stmt-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       (types (stmt-types old))
       ((unless (equal (stmt-types new)
                       types))
        (raise "Internal error: ~
                the types ~x0 of the new statement ~x1 differ from ~
                the types ~x2 of the old statement ~x3."
               (stmt-types new) new types old)
        (mv '(_) nil 1))
       (vars-pre (gen-var-assertions vartys 'compst))
       (vars-post (gen-var-assertions vartys 'old-compst))
       ((mv & old-stmt) (ldm-stmt old)) ; ERP is NIL because FORMALP
       ((mv & new-stmt) (ldm-stmt new)) ; ERP is NIL because FORMALP
       ((mv & ctypes) (ldm-type-option-set types)) ; ERP must be NIL
       (formula
        `(b* ((old-stmt ',old-stmt)
              (new-stmt ',new-stmt)
              ((mv old-result old-compst)
               (c::exec-stmt old-stmt compst old-fenv limit))
              ((mv new-result new-compst)
               (c::exec-stmt new-stmt compst new-fenv limit)))
           (implies (and (> (c::compustate-frames-number compst) 0)
                         ,@vars-pre
                         (not (c::errorp old-result)))
                    (and (not (c::errorp new-result))
                         (equal old-result new-result)
                         (equal old-compst new-compst)
                         (set::in (c::type-option-of-stmt-value old-result)
                                  ',ctypes)
                         ,@vars-post))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event
        `(defrule ,thm-name
           ,formula
           :rule-classes nil
           :hints ,hints)))
    (mv thm-event thm-name thm-index))
  ///
  (fty::deffixequiv gen-stmt-thm
    :args ((old stmtp) (new stmtp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-decl-thm ((old declp)
                      (new declp)
                      (vartys-pre c::ident-type-mapp)
                      (vartys-post c::ident-type-mapp)
                      (const-new symbolp)
                      (thm-index posp)
                      (hints true-listp))
  :guard (and (decl-unambp old)
              (decl-annop old)
              (decl-unambp new)
              (decl-annop new))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem for the transformation of a declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declarations must be of objects in blocks."))
  (b* ((old (decl-fix old))
       (new (decl-fix new))
       ((unless (decl-block-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (decl-block-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       (vars-pre (gen-var-assertions vartys-pre 'compst))
       (vars-post (gen-var-assertions vartys-post 'old-compst))
       ((mv & old-decl) (ldm-decl-obj old)) ; ERP is NIL because FORMALP
       ((mv & new-decl) (ldm-decl-obj new)) ; ERP is NIL because FORMALP
       (formula
        `(b* ((old-decl ',old-decl)
              (new-decl ',new-decl)
              (old-compst
               (c::exec-obj-declon old-decl compst old-fenv limit))
              (new-compst
               (c::exec-obj-declon new-decl compst new-fenv limit)))
           (implies (and (> (c::compustate-frames-number compst) 0)
                         ,@vars-pre
                         (not (c::errorp old-compst)))
                    (and (not (c::errorp new-compst))
                         (equal old-compst new-compst)
                         ,@vars-post))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event
        `(defrule ,thm-name
           ,formula
           :rule-classes nil
           :hints ,hints)))
    (mv thm-event thm-name thm-index))
  ///
  (fty::deffixequiv gen-decl-thm
    :args ((old declp) (new declp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-block-item-thm ((old block-itemp)
                            (new block-itemp)
                            (vartys-pre c::ident-type-mapp)
                            (vartys-post c::ident-type-mapp)
                            (const-new symbolp)
                            (thm-index posp)
                            (hints true-listp))
  :guard (and (block-item-unambp old)
              (block-item-annop old)
              (block-item-unambp new)
              (block-item-annop new))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem for the transformation of a block item."
  (b* ((old (block-item-fix old))
       (new (block-item-fix new))
       ((unless (block-item-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (block-item-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       (types (block-item-types old))
       ((unless (equal (block-item-types new)
                       types))
        (raise "Internal error: ~
                the types ~x0 of the new block item ~x1 differ from ~
                the types ~x2 of the old block item ~x3."
               (block-item-types new) new types old)
        (mv '(_) nil 1))
       (vars-pre (gen-var-assertions vartys-pre 'compst))
       (vars-post (gen-var-assertions vartys-post 'old-compst))
       ((mv & old-item) (ldm-block-item old)) ; ERP is NIL because FORMALP
       ((mv & new-item) (ldm-block-item new)) ; ERP is NIL because FORMALP
       ((mv & ctypes) (ldm-type-option-set types)) ; ERP is NIL because FORMALP
       (formula
        `(b* ((old-item ',old-item)
              (new-item ',new-item)
              ((mv old-result old-compst)
               (c::exec-block-item old-item compst old-fenv limit))
              ((mv new-result new-compst)
               (c::exec-block-item new-item compst new-fenv limit)))
           (implies (and (> (c::compustate-frames-number compst) 0)
                         ,@vars-pre
                         (not (c::errorp old-result)))
                    (and (not (c::errorp new-result))
                         (equal old-result new-result)
                         (equal old-compst new-compst)
                         (set::in (c::type-option-of-stmt-value old-result)
                                  ',ctypes)
                         ,@vars-post))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event
        `(defrule ,thm-name
           ,formula
           :rule-classes nil
           :hints ,hints)))
    (mv thm-event thm-name thm-index))
  ///
  (fty::deffixequiv gen-block-item-thm
    :args ((old block-itemp) (new block-itemp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-block-item-list-thm ((old block-item-listp)
                                 (new block-item-listp)
                                 (vartys c::ident-type-mapp)
                                 (const-new symbolp)
                                 (thm-index posp)
                                 (hints true-listp))
  :guard (and (block-item-list-unambp old)
              (block-item-list-annop old)
              (block-item-list-unambp new)
              (block-item-list-annop new))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem for the transformation of a list of block items."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unlike @(tsee gen-block-item-thm),
     here we have a single @('vartys')
     instead of a @('vartys-pre') and a @('vartys-post').
     This is intentional, because we are only interested in
     variables that will survive the scope of the list of block items,
     which are the variables in scope at the start of the list."))
  (b* ((old (block-item-list-fix old))
       (new (block-item-list-fix new))
       ((unless (block-item-list-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (block-item-list-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       (types (block-item-list-types old))
       ((unless (equal (block-item-list-types new)
                       types))
        (raise "Internal error: ~
                the types ~x0 of the new block item list ~x1 differ from ~
                the types ~x2 of the old block item list ~x3."
               (block-item-list-types new) new types old)
        (mv '(_) nil 1))
       (vars-pre (gen-var-assertions vartys 'compst))
       ((mv & old-items) (ldm-block-item-list old)) ; ERP is NIL because FORMALP
       ((mv & new-items) (ldm-block-item-list new)) ; ERP is NIL because FORMALP
       ((mv & ctypes) (ldm-type-option-set types)) ; ERP is NIL because FORMALP
       (formula
        `(b* ((old-items ',old-items)
              (new-items ',new-items)
              ((mv old-result old-compst)
               (c::exec-block-item-list old-items compst old-fenv limit))
              ((mv new-result new-compst)
               (c::exec-block-item-list new-items compst new-fenv limit)))
           (implies (and (> (c::compustate-frames-number compst) 0)
                         ,@vars-pre
                         (not (c::errorp old-result)))
                    (and (not (c::errorp new-result))
                         (equal old-result new-result)
                         (equal old-compst new-compst)
                         (set::in (c::type-option-of-stmt-value old-result)
                                  ',ctypes)))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event
        `(defrule ,thm-name
           ,formula
           :rule-classes nil
           :hints ,hints)))
    (mv thm-event thm-name thm-index))
  ///
  (fty::deffixequiv gen-block-item-list-thm
    :args ((old block-item-listp) (new block-item-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tyspecseq-to-type ((tyspecseq c::tyspecseqp))
  :returns (mv (okp booleanp) (type c::typep))
  :short "Map a type specifier sequence from the language formalization
          to the corresponding type."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only allow certain types."))
  (c::tyspecseq-case
   tyspecseq
   :uchar (mv t (c::type-uchar))
   :schar (mv t (c::type-schar))
   :ushort (mv t (c::type-ushort))
   :sshort (mv t (c::type-sshort))
   :uint (mv t (c::type-uint))
   :sint (mv t (c::type-sint))
   :ulong (mv t (c::type-ulong))
   :slong (mv t (c::type-slong))
   :ullong (mv t (c::type-ullong))
   :sllong (mv t (c::type-sllong))
   :otherwise (mv nil (c::type-void)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-from-params ((params c::param-declon-listp) (gin ginp))
  :returns (mv (okp booleanp)
               (args symbol-listp)
               (parargs "A term.")
               (arg-types true-listp)
               (arg-types-compst true-listp)
               (vartys c::ident-type-mapp))
  :short "Generate certain pieces of information
          from the formal parameters of a function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The results of this function are used to generate
     theorems about function calls.")
   (xdoc::p
    "We generate the following:")
   (xdoc::ul
    (xdoc::li
     "A list @('args') of symbols used as ACL2 variables
      that denote the C values passed as arguments to the function.")
    (xdoc::li
     "A term @('parargs') that is a nest of @(tsee omap::update) calls
      that denotes the initial scope of the function.
      Each @(tsee omap::update) call adds
      the name of the parameter as key
      and the variable for the corresponding argument as value.")
    (xdoc::li
     "A list @('arg-types') of terms that assert that
      each variable in @('args') is a value of the appropriate type.")
    (xdoc::li
     "A list @('arg-types-compst') of terms that assert that
      each parameter in @('params') can be read from a computation state
      and its reading yields a value of the appropriate type.")
    (xdoc::li
     "A variable-type map corresponding to the parameters in the obvious way."))
   (xdoc::p
    "These results are generated only if
     all the parameters have certain types
     (see @(tsee tyspecseq-to-type)),
     which we check as we go through the parameters.
     The @('okp') result says whether this is the case;
     if it is @('nil'), the other results are @('nil') too."))
  (b* (((when (endp params)) (mv t nil nil nil nil nil))
       ((c::param-declon param) (car params))
       ((mv okp type) (tyspecseq-to-type param.tyspec))
       ((unless okp) (mv nil nil nil nil nil nil))
       ((unless (c::obj-declor-case param.declor :ident))
        (mv nil nil nil nil nil nil))
       (ident (c::obj-declor-ident->get param.declor))
       (par (c::ident->name ident))
       (arg (intern-in-package-of-symbol par (gin->const-new gin)))
       (arg-type `(and (c::valuep ,arg)
                       (equal (c::type-of-value ,arg) ',type)))
       (arg-type-compst
        `(c::compustate-has-var-with-type-p ',ident ',type compst))
       ((mv okp
            more-args
            parargs
            more-arg-types
            more-arg-types-compst
            more-vartys)
        (gen-from-params (cdr params) gin))
       ((unless okp) (mv nil nil nil nil nil nil))
       (parargs `(omap::update (c::ident ,par) ,arg ,parargs))
       (vartys (omap::update ident type more-vartys)))
    (mv t
        (cons arg more-args)
        parargs
        (cons arg-type more-arg-types)
        (cons arg-type-compst more-arg-types-compst)
        vartys))
  :verify-guards :after-returns

  ///

  (defret len-of-gen-from-params.arg-types
    (equal (len arg-types)
           (len args))
    :hints (("Goal" :induct t :in-theory (enable len))))

  (defret len-of-gen-from-params.arg-types-compst
    (equal (len arg-types-compst)
           (len args))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-init-scope-thm ((params c::param-declon-listp)
                            (args symbol-listp)
                            (parargs "A term.")
                            (arg-types true-listp)
                            (const-new symbolp)
                            (thm-index posp))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp
                                  :rule-classes (:rewrite :type-prescription)))
  :short "Generate a theorem about the initial scope of a function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('args'), @('parargs'), and @('arg-types') inputs
     are the corresponding outputs of @(tsee gen-from-params).")
   (xdoc::p
    "The theorem says that, given values of certain types for the arguments,
     @(tsee c::init-scope) applied to the list of parameter declarations
     and to the list of parameter values
     yields an omap (which we express as an @(tsee omap::update) nest)
     that associates parameter name and argument value."))
  (b* ((formula `(implies (and ,@arg-types)
                          (equal (c::init-scope ',params (list ,@args))
                                 ,parargs)))
       (hints
        '(("Goal" :in-theory '(omap::assoc-when-emptyp
                               (:e omap::emptyp)
                               omap::assoc-of-update
                               c::init-scope
                               c::not-flexible-array-member-p-when-ucharp
                               c::not-flexible-array-member-p-when-scharp
                               c::not-flexible-array-member-p-when-ushortp
                               c::not-flexible-array-member-p-when-sshortp
                               c::not-flexible-array-member-p-when-uintp
                               c::not-flexible-array-member-p-when-sintp
                               c::not-flexible-array-member-p-when-ulongp
                               c::not-flexible-array-member-p-when-slongp
                               c::not-flexible-array-member-p-when-ullongp
                               c::not-flexible-array-member-p-when-sllongp
                               c::remove-flexible-array-member-when-absent
                               c::ucharp-alt-def
                               c::scharp-alt-def
                               c::ushortp-alt-def
                               c::sshortp-alt-def
                               c::uintp-alt-def
                               c::sintp-alt-def
                               c::ulongp-alt-def
                               c::slongp-alt-def
                               c::ullongp-alt-def
                               c::sllongp-alt-def
                               c::type-of-value-when-ucharp
                               c::type-of-value-when-scharp
                               c::type-of-value-when-ushortp
                               c::type-of-value-when-sshortp
                               c::type-of-value-when-uintp
                               c::type-of-value-when-sintp
                               c::type-of-value-when-ulongp
                               c::type-of-value-when-slongp
                               c::type-of-value-when-ullongp
                               c::type-of-value-when-sllongp
                               c::value-fix-when-valuep
                               c::value-list-fix-of-cons
                               c::type-of-value
                               c::type-array
                               c::type-pointer
                               c::type-struct
                               (:e c::adjust-type)
                               (:e c::apconvert-type)
                               (:e c::ident)
                               (:e c::param-declon-list-fix$inline)
                               (:e c::param-declon-to-ident+tyname)
                               (:e c::tyname-to-type)
                               (:e c::type-uchar)
                               (:e c::type-schar)
                               (:e c::type-ushort)
                               (:e c::type-sshort)
                               (:e c::type-uint)
                               (:e c::type-sint)
                               (:e c::type-ulong)
                               (:e c::type-slong)
                               (:e c::type-ullong)
                               (:e c::type-sllong)
                               (:e c::value-list-fix$inline)
                               mv-nth
                               car-cons
                               cdr-cons
                               (:e <<)
                               lemma1
                               lemma2))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event `(defruled ,thm-name
                     ,formula
                     :hints ,hints
                     :prep-lemmas
                     ((defruled lemma1
                        (not (c::errorp nil)))
                      (defruled lemma2
                        (not (c::errorp (omap::update key val map)))
                        :enable (c::errorp omap::update))))))
    (mv thm-event thm-name thm-index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-param-thms ((arg-types-compst true-listp)
                        (all-arg-types true-listp)
                        (all-params c::param-declon-listp)
                        (all-args symbol-listp)
                        (init-scope-thm symbolp)
                        (const-new symbolp)
                        (thm-index posp))
  :returns (mv (thm-events pseudo-event-form-listp)
               (thm-names symbol-listp)
               (updated-thm-index posp
                                  :rule-classes (:rewrite :type-prescription)))
  :short "Generate theorems about the parameters of a function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('args') and @('arg-types-compst') inputs are
     the corresponding outputs of @(tsee gen-from-params);
     these are @(tsee cdr)ed in the recursion.
     The @('all-arg-types') input is
     the @('arg-types') output of @(tsee gen-from-params);
     it stays the same during the recursion.")
   (xdoc::p
    "We return the theorem events, along with the theorem names.")
   (xdoc::p
    "The theorem names are used locally in an enclosing theorem,
     so they do not need to be particularly unique.
     But we should check and disambiguate them more thoroughly.")
   (xdoc::p
    "For each parameter of the function,
     we generate a theorem saying that,
     in the computation state resulting from
     pushing the initial scope to the frame stack,
     if the value corresponding to the parameter has a certain type,
     then reading the parameter from the computation state
     succeeds and yields a value of that type."))
  (b* (((when (endp arg-types-compst)) (mv nil nil (pos-fix thm-index)))
       (formula
        `(b* ((compst
               (c::push-frame
                (c::frame fun
                          (list
                           (c::init-scope ',all-params (list ,@all-args))))
                compst0)))
           (implies (and ,@all-arg-types)
                    ,(car arg-types-compst))))
       (hints
        `(("Goal" :in-theory '(,init-scope-thm
                               (:e ident)
                               c::push-frame
                               c::compustate-has-var-with-type-p
                               c::objdesign-of-var
                               c::objdesign-of-var-aux
                               c::compustate-frames-number
                               c::top-frame
                               c::read-object
                               c::scopep-of-update
                               (:e c::scopep)
                               c::compustate->frames-of-compustate
                               c::frame->scopes-of-frame
                               c::frame-fix-when-framep
                               c::frame-list-fix-of-cons
                               c::mapp-when-scopep
                               c::framep-of-frame
                               c::objdesign-auto->frame-of-objdesign-auto
                               c::objdesign-auto->name-of-objdesign-auto
                               c::objdesign-auto->scope-of-objdesign-auto
                               c::return-type-of-objdesign-auto
                               c::scope-fix-when-scopep
                               c::scope-fix
                               c::scope-list-fix-of-cons
                               (:e c::ident)
                               (:e c::ident-fix$inline)
                               (:e c::identp)
                               (:t c::objdesign-auto)
                               omap::assoc-of-update
                               param-thm-list-lemma
                               nfix
                               fix
                               len
                               car-cons
                               cdr-cons
                               commutativity-of-+
                               acl2::fold-consts-in-+
                               acl2::len-of-append
                               acl2::len-of-rev
                               acl2::rev-of-cons
                               (:e acl2::fast-<<)
                               unicity-of-0
                               (:e rev)
                               (:t len)
                               (:e c::type-fix)))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event `(defruled ,thm-name
                     ,formula
                     :hints ,hints))
       ((mv more-thm-events more-thm-names thm-index)
        (gen-param-thms (cdr arg-types-compst)
                        all-arg-types
                        all-params
                        all-args
                        init-scope-thm
                        const-new
                        thm-index)))
    (mv (cons thm-event more-thm-events)
        (cons thm-name more-thm-names)
        thm-index))
  :guard-hints (("Goal" :in-theory (enable len)))

  ///

  (defret len-of-gen-param-thms.thm-names
    (equal (len thm-names)
           (len thm-events))
    :hints (("Goal" :induct t :in-theory (enable len))))

  (defruled param-thm-list-lemma
    (equal (nth (len l) (append (rev l) (list x)))
           x)
    :use (:instance lemma (l (rev l)))
    :prep-lemmas
    ((defruled lemma
       (equal (nth (len l) (append l (list x)))
              x)
       :induct t
       :enable len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-expr-ident ((ident identp) (info var-infop) (gin ginp))
  :returns (mv (expr exprp) (gout goutp))
  :short "Equality transformation of an identifier expression (i.e. variable)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since an identifier expression has no sub-constructs,
     this is a special case of lifting equalities
     (see discussion in @(see proof-generation)),
     where there is no equality of sub-constructs to lift,
     but we just generate a new expression
     that is identical to the old one,
     with an equality theorem about them;
     but, importantly, the theorem includes assertions
     about the type of the variable and the preservation of variables
     (see @(tsee gen-expr-thm)).")
   (xdoc::p
    "We generate a theorem
     if the variable has a type supported in our C formalization,
     and if the variable is known in scope."))
  (b* ((ident (ident-fix ident))
       ((var-info info) (var-info-fix info))
       ((gin gin) gin)
       (expr (make-expr-ident :ident ident :info info))
       (gout-no-thm (gout-no-thm gin))
       ((unless (and (ident-formalp ident)
                     (type-formalp info.type)
                     (not (type-case info.type :void))
                     (not (type-case info.type :char))))
        (mv expr gout-no-thm))
       ((mv & cvar) (ldm-ident ident)) ; ERP is NIL because FORMALP
       ((mv & ctype) (ldm-type info.type)) ; ERP is NIL because FORMALP
       ((unless (omap::assoc cvar gin.vartys)) (mv expr gout-no-thm))
       (hints `(("Goal"
                 :in-theory '((:e c::expr-ident)
                              (:e c::type-fix)
                              expr-compustate-vars)
                 :use ((:instance expr-ident-compustate-vars
                                  (var ',cvar)
                                  (type ',ctype))
                       (:instance expr-ident-congruence
                                  (var ',cvar)
                                  (type ',ctype))))))
       ((mv thm-event thm-name thm-index)
        (gen-expr-thm expr
                      expr
                      gin.vartys
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv expr
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))
  :hooks (:fix)

  ///

  (defret expr-unambp-of-expr-ident
    (expr-unambp expr))

  (defret expr-annop-of-expr-ident
    (expr-annop expr))

  (defret expr-aidentp-of-expr-ident
    (expr-aidentp expr gcc)
    :hyp (ident-aidentp ident gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-expr-const ((const constp) (info expr-const-infop) (gin ginp))
  :guard (const-annop const)
  :returns (mv (expr exprp) (gout goutp))
  :short "Equality transformation of a constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since a constant has no sub-constructs,
     this is a special case of lifting equalities
     (see discussion in @(see proof-generation)),
     where there is no equality of sub-constructs to lift,
     but we just generate a new expression
     that is identical to the old one,
     with an equality theorem about them;
     but, importantly, the theorem includes assertions
     about the type of the variable and the preservation of variables
     (see @(tsee gen-expr-thm)).")
   (xdoc::p
    "We generate a theorem
     if the constant is an integer one,
     and under the following additional conditions:")
   (xdoc::ul
    (xdoc::li
     "If the constant has type (@('signed') or @('unsigned')) @('int'),
      it fits in 32 bits.")
    (xdoc::li
     "If the constant has type (@('signed') or @('unsigned')) @('long'),
      it fits in 64 bits.")
    (xdoc::li
     "If the constant has type (@('signed') or @('unsigned')) @('long long'),
      it fits in 64 bits."))
   (xdoc::p
    "The reason for these additional conditions is that
     our current dynamic semantics assumes that
     those types have those sizes,
     while our validator is more general
     (@(tsee c$::valid-iconst) takes an implementation environment as input,
     which specifies the size of those types).
     Until we extend our dynamic semantics to be more general,
     we need this additional condition for proof generation."))
  (b* (((gin gin) gin)
       (info (expr-const-info-fix info))
       (expr (make-expr-const :const const :info info))
       (gout-no-thm (gout-no-thm gin))
       ((unless (const-case const :int)) (mv expr gout-no-thm))
       ((iconst iconst) (const-int->unwrap const))
       ((iconst-info info) iconst.info)
       ((unless (or (and (type-case info.type :sint)
                         (<= info.value (c::sint-max)))
                    (and (type-case info.type :uint)
                         (<= info.value (c::uint-max)))
                    (and (type-case info.type :slong)
                         (<= info.value (c::slong-max)))
                    (and (type-case info.type :ulong)
                         (<= info.value (c::ulong-max)))
                    (and (type-case info.type :sllong)
                         (<= info.value (c::sllong-max)))
                    (and (type-case info.type :ullong)
                         (<= info.value (c::ullong-max)))))
        (mv expr gout-no-thm))
       ((mv & cconst) (c$::ldm-const const)) ; ERP must be NIL
       (hints
        `(("Goal"
           :in-theory '((:e c::expr-const)
                        (:e c::const-kind)
                        (:e c::const-int->get)
                        (:e c::check-iconst)
                        (:e c::typep)
                        expr-compustate-vars)
           :use ((:instance expr-const-congruence-pure
                            (const ',cconst))
                 (:instance expr-const-congruence
                            (const ',cconst))))))
       ((mv thm-event thm-name thm-index)
        (gen-expr-thm expr
                      expr
                      gin.vartys
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv expr
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))
  :guard-hints (("Goal" :in-theory (disable (:e tau-system)))) ; for speed
  :hooks (:fix)

  ///

  (defret expr-unambp-of-xeq-expr-const
    (expr-unambp expr))

  (defret expr-annop-of-xeq-expr-const
    (expr-annop expr)
    :hyp (and (const-annop const)
              (expr-const-infop info)))

  (defret expr-aidentp-of-xeq-expr-const
    (expr-aidentp expr gcc)
    :hyp (const-aidentp const gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-expr-unary ((op unopp)
                        (arg exprp)
                        (arg-new exprp)
                        (arg-thm-name symbolp)
                        (info expr-unary-infop)
                        (gin ginp))
  :guard (and (expr-unambp arg)
              (expr-annop arg)
              (expr-unambp arg-new)
              (expr-annop arg-new))
  :returns (mv (expr exprp) (gout goutp))
  :short "Equality lifting transformation of a unary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     combining the unary operator with
     the possibly transformed argument expression.")
   (xdoc::p
    "We generate a theorem iff
     a theorem was generated for the argument expression
     and the unary operator is among @('+'), @('-'), @('~') and @('!').
     The argument expression may be pure or not."))
  (b* (((gin gin) gin)
       (expr (make-expr-unary :op op :arg arg :info info))
       (expr-new (make-expr-unary :op op :arg arg-new :info info))
       ((unless (and arg-thm-name
                     (member-eq (unop-kind op)
                                '(:plus :minus :bitnot :lognot))))
        (mv expr-new (gout-no-thm gin)))
       ((mv & old-arg) (ldm-expr arg)) ; ERP must be NIL
       ((mv & new-arg) (ldm-expr arg-new)) ; ERP must be NIL
       ((mv lifted-thm-name thm-index events)
        (if (and (expr-purep arg)
                 (not (expr-case arg :ident))
                 (not (expr-case arg :const))
                 (not (expr-case arg :unary)))
            (b* (((mv thm-event thm-name thm-index)
                  (lift-expr-pure-thm arg
                                      arg-new
                                      arg-thm-name
                                      gin.vartys
                                      gin.const-new
                                      gin.thm-index)))
              (mv thm-name thm-index (cons thm-event gin.events)))
          (mv nil gin.thm-index gin.events)))
       (hints `(("Goal"
                 :in-theory '((:e c::unop-nonpointerp)
                              (:e c::unop-kind)
                              (:e c::expr-unary)
                              (:e c::type-kind)
                              (:e c::promote-type)
                              (:e c::type-nonchar-integerp)
                              (:e c::type-sint)
                              (:e member-equal)
                              expr-compustate-vars)
                 :use ((:instance ,(or lifted-thm-name arg-thm-name)
                                  (limit (1- limit)))
                       ,@(and (expr-purep arg)
                              (list arg-thm-name))
                       (:instance expr-unary-congruence
                                  (op ',(unop-case
                                         op
                                         :plus (c::unop-plus)
                                         :minus (c::unop-minus)
                                         :bitnot (c::unop-bitnot)
                                         :lognot (c::unop-lognot)
                                         :otherwise (impossible)))
                                  (old-arg ',old-arg)
                                  (new-arg ',new-arg))
                       ,@(and (expr-purep arg)
                              `((:instance expr-unary-congruence-pure
                                           (op ',(unop-case
                                                  op
                                                  :plus (c::unop-plus)
                                                  :minus (c::unop-minus)
                                                  :bitnot (c::unop-bitnot)
                                                  :lognot (c::unop-lognot)
                                                  :otherwise (impossible)))
                                           (old-arg ',old-arg)
                                           (new-arg ',new-arg))))
                       (:instance expr-unary-errors
                                  (op ',(unop-case
                                         op
                                         :plus (c::unop-plus)
                                         :minus (c::unop-minus)
                                         :bitnot (c::unop-bitnot)
                                         :lognot (c::unop-lognot)
                                         :otherwise (impossible)))
                                  (arg ',old-arg)
                                  (fenv old-fenv))
                       ,@(and (expr-purep arg)
                              `((:instance expr-unary-errors-pure
                                           (op ',(unop-case
                                                  op
                                                  :plus (c::unop-plus)
                                                  :minus (c::unop-minus)
                                                  :bitnot (c::unop-bitnot)
                                                  :lognot (c::unop-lognot)
                                                  :otherwise (impossible)))
                                           (arg ',old-arg))))))))
       ((mv thm-event thm-name thm-index)
        (gen-expr-thm expr
                      expr-new
                      gin.vartys
                      gin.const-new
                      thm-index
                      hints)))
    (mv expr-new
        (make-gout :events (cons thm-event events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))

  ///

  (defret expr-unambp-of-xeq-expr-unary
    (expr-unambp expr)
    :hyp (expr-unambp arg-new))

  (defret expr-annop-of-xeq-expr-unary
    (expr-annop expr)
    :hyp (and (expr-annop arg-new)
              (expr-unary-infop info)))

  (defret expr-aidentp-of-xeq-expr-unary
    (expr-aidentp expr gcc)
    :hyp (expr-aidentp arg-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-expr-cast ((type tynamep)
                       (type-new tynamep)
                       (type-thm-name symbolp)
                       (arg exprp)
                       (arg-new exprp)
                       (arg-thm-name symbolp)
                       (info tyname-infop)
                       (gin ginp))
  :guard (and (tyname-unambp type)
              (tyname-annop type)
              (tyname-unambp type-new)
              (tyname-annop type-new)
              (expr-unambp arg)
              (expr-annop arg)
              (expr-unambp arg-new)
              (expr-annop arg-new))
  :returns (mv (expr exprp) (gout goutp))
  :short "Equality lifting transformation of a cast expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     combining the possibly transformed type name with
     the possibly transformed argument expression.")
   (xdoc::p
    "For now, we generate no theorem for the transformation of the type name,
     but we double-check that here.
     We generate a theorem only if we generated one for the argument expression,
     the argument expression is pure,
     and the old and new type names are the same (i.e. no transformation)."))
  (b* (((gin gin) gin)
       (expr (make-expr-cast :type type :arg arg))
       (expr-new (make-expr-cast :type type-new :arg arg-new))
       ((when type-thm-name)
        (raise "Internal error: ~
                unexpected type name transformation theorem ~x0."
               type-thm-name)
        (mv expr-new (irr-gout)))
       ((tyname-info info) info)
       ((unless (and arg-thm-name
                     (expr-purep arg)
                     (type-formalp info.type)
                     (not (type-case info.type :void))
                     (not (type-case info.type :char))))
        (mv expr-new (gout-no-thm gin)))
       ((unless (equal type type-new))
        (raise "Internal error: ~
                type names ~x0 and ~x1 differ."
               type type-new)
        (mv expr-new (irr-gout)))
       ((mv & ctyname) (ldm-tyname type)) ; ERP must be NIL
       ((mv & old-arg) (ldm-expr arg)) ; ERP must be NIL
       ((mv & new-arg) (ldm-expr arg-new)) ; ERP must be NIL
       (hints `(("Goal"
                 :in-theory '((:e c::expr-cast)
                              (:e c::tyname-to-type)
                              (:e c::type-nonchar-integerp))
                 :use (,arg-thm-name
                       (:instance
                        expr-cast-congruence
                        (tyname ',ctyname)
                        (old-arg ',old-arg)
                        (new-arg ',new-arg))
                       (:instance
                        expr-cast-errors
                        (tyname ',ctyname)
                        (arg ',old-arg))))))
       ((mv thm-event thm-name thm-index)
        (gen-expr-pure-thm expr
                           expr-new
                           gin.vartys
                           gin.const-new
                           gin.thm-index
                           hints)))
    (mv expr-new
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))

  ///

  (defret expr-unambp-of-xeq-expr-cast
    (expr-unambp expr)
    :hyp (and (tyname-unambp type-new)
              (expr-unambp arg-new)))

  (defret expr-annop-of-xeq-expr-cast
    (expr-annop expr)
    :hyp (and (tyname-annop type-new)
              (expr-annop arg-new)))

  (defret expr-aidentp-of-xeq-expr-cast
    (expr-aidentp expr gcc)
    :hyp (and (tyname-aidentp type-new gcc)
              (expr-aidentp arg-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-expr-binary ((op binopp)
                         (arg1 exprp)
                         (arg1-new exprp)
                         (arg1-thm-name symbolp)
                         (arg2 exprp)
                         (arg2-new exprp)
                         (arg2-thm-name symbolp)
                         (info expr-binary-infop)
                         (gin ginp))
  :guard (and (expr-unambp arg1)
              (expr-annop arg1)
              (expr-unambp arg1-new)
              (expr-annop arg1-new)
              (expr-unambp arg2)
              (expr-annop arg2)
              (expr-unambp arg2-new)
              (expr-annop arg2-new))
  :returns (mv (expr exprp) (gout goutp))
  :short "Equality lifting transformation of a binary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a theorem only if
     theorems were generated for both argument expressions.")
   (xdoc::p
    "For pure strict binary operators,
     we generate a theorem if additionally
     both argument expressions are pure,
     since the order of evaluation is unspecified in C.")
   (xdoc::p
    "For pure non-strict binary operators,
     for now we also require both argument expressions to be pure
     in order to generate a theorem.
     But this could be relaxed, since in this case
     the order of evaluation is prescribed.")
   (xdoc::p
    "For the non-pure strict simple assignment operator,
     for theorem generation we require the left expression to be a variable.
     The right expression does not have to be pure,
     because when the left expression is a variable,
     the order of evaluation does not matter,
     because the (previous) value of the assigned variable does not matter.
     Note that this supports multiple assignments @('x = y = z = ...').
     If the right expression is pure (which always is, currently),
     we lift the theorem about @(tsee c::exec-expr-pure)
     to a theorem about @(tsee c::exec-expr):
     this uniformly provides a theorem about @(tsee c::exec-expr)
     to use in the proof for the assignment expression.")
   (xdoc::p
    "For the remaining (non-pure strict) operators,
     namely compound assignments,
     we do not generate any theorems for now."))
  (b* (((gin gin) gin)
       (expr (make-expr-binary :op op :arg1 arg1 :arg2 arg2 :info info))
       (expr-new
        (make-expr-binary :op op :arg1 arg1-new :arg2 arg2-new :info info))
       (gout-no-thm (gout-no-thm gin))
       ((unless (and arg1-thm-name
                     arg2-thm-name))
        (mv expr-new gout-no-thm)))
    (cond
     ((member-eq (binop-kind op)
                 '(:mul :div :rem :add :sub :shl :shr
                   :lt :gt :le :ge :eq :ne
                   :bitand :bitxor :bitior))
      (b* (((unless (and (expr-purep arg1)
                         (expr-purep arg2)))
            (mv expr-new gout-no-thm))
           (cop (ldm-binop op)) ; ERP must be NIL
           ((mv & old-arg1) (ldm-expr arg1)) ; ERP must be NIL
           ((mv & old-arg2) (ldm-expr arg2)) ; ERP must be NIL
           ((mv & new-arg1) (ldm-expr arg1-new)) ; ERP must be NIL
           ((mv & new-arg2) (ldm-expr arg2-new)) ; ERP must be NIL
           (hints `(("Goal"
                     :in-theory '((:e c::binop-kind)
                                  (:e c::binop-purep)
                                  (:e c::binop-strictp)
                                  (:e c::expr-binary)
                                  (:e c::type-nonchar-integerp)
                                  (:e c::promote-type)
                                  (:e c::uaconvert-types)
                                  (:e c::type-sint)
                                  (:e member-equal))
                     :use (,arg1-thm-name
                           ,arg2-thm-name
                           (:instance
                            expr-binary-pure-strict-congruence
                            (op ',cop)
                            (old-arg1 ',old-arg1)
                            (old-arg2 ',old-arg2)
                            (new-arg1 ',new-arg1)
                            (new-arg2 ',new-arg2))
                           (:instance
                            expr-binary-pure-strict-errors
                            (op ',cop)
                            (arg1 ',old-arg1)
                            (arg2 ',old-arg2))))))
           ((mv thm-event thm-name thm-index)
            (gen-expr-pure-thm expr
                               expr-new
                               gin.vartys
                               gin.const-new
                               gin.thm-index
                               hints)))
        (mv expr-new
            (make-gout :events (cons thm-event gin.events)
                       :thm-index thm-index
                       :thm-name thm-name
                       :vartys gin.vartys))))
     ((member-eq (binop-kind op) '(:logand :logor))
      (b* (((unless (and (expr-purep arg1)
                         (expr-purep arg2)))
            (mv expr-new gout-no-thm))
           ((mv & old-arg1) (ldm-expr arg1)) ; ERP must be NIL
           ((mv & old-arg2) (ldm-expr arg2)) ; ERP must be NIL
           ((mv & new-arg1) (ldm-expr arg1-new)) ; ERP must be NIL
           ((mv & new-arg2) (ldm-expr arg2-new)) ; ERP must be NIL
           (hints
            `(("Goal"
               :in-theory '((:e c::expr-binary)
                            (:e c::binop-logand)
                            (:e c::binop-logor)
                            (:e c::type-sint)
                            (:e c::type-nonchar-integerp))
               :use
               (,arg1-thm-name
                ,arg2-thm-name
                (:instance
                 ,(case (binop-kind op)
                    (:logand 'expr-binary-logand-first-congruence)
                    (:logor 'expr-binary-logor-first-congruence))
                 (old-arg1 ',old-arg1)
                 (old-arg2 ',old-arg2)
                 (new-arg1 ',new-arg1)
                 (new-arg2 ',new-arg2))
                (:instance
                 ,(case (binop-kind op)
                    (:logand 'expr-binary-logand-second-congruence)
                    (:logor 'expr-binary-logor-second-congruence))
                 (old-arg1 ',old-arg1)
                 (old-arg2 ',old-arg2)
                 (new-arg1 ',new-arg1)
                 (new-arg2 ',new-arg2))
                (:instance
                 ,(case (binop-kind op)
                    (:logand 'expr-binary-logand-first-errors)
                    (:logor 'expr-binary-logor-first-errors))
                 (arg1 ',old-arg1)
                 (arg2 ',old-arg2))
                (:instance
                 ,(case (binop-kind op)
                    (:logand 'expr-binary-logand-second-errors)
                    (:logor 'expr-binary-logor-second-errors))
                 (arg1 ',old-arg1)
                 (arg2 ',old-arg2))))))
           ((mv thm-event thm-name thm-index)
            (gen-expr-pure-thm expr
                               expr-new
                               gin.vartys
                               gin.const-new
                               gin.thm-index
                               hints)))
        (mv expr-new
            (make-gout :events (cons thm-event gin.events)
                       :thm-index thm-index
                       :thm-name thm-name
                       :vartys gin.vartys))))
     ((eq (binop-kind op) :asg)
      (b* (((unless (and (expr-case arg1 :ident)
                         (equal (expr-type arg1)
                                (expr-type arg2))
                         (type-integerp (expr-type arg1))))
            (mv expr-new gout-no-thm))
           ((mv & cvar) (ldm-ident (expr-ident->ident arg1))) ; ERP must be NIL
           ((mv & old-arg2) (ldm-expr arg2)) ; ERP must be NIL
           ((mv & new-arg2) (ldm-expr arg2-new)) ; ERP must be NIL
           ((mv lifted-thm-name thm-index events)
            (if (and (expr-purep arg2)
                     (not (expr-case arg2 :ident))
                     (not (expr-case arg2 :const))
                     (not (expr-case arg2 :unary)))
                (b* (((mv thm-event thm-name thm-index)
                      (lift-expr-pure-thm arg2
                                          arg2-new
                                          arg2-thm-name
                                          gin.vartys
                                          gin.const-new
                                          gin.thm-index)))
                  (mv thm-name thm-index (cons thm-event gin.events)))
              (mv nil gin.thm-index gin.events)))
           (hints
            `(("Goal"
               :in-theory
               '((:e c::expr-kind)
                 (:e c::expr-ident)
                 (:e c::expr-ident->get)
                 (:e c::expr-binary->op)
                 (:e c::expr-binary->arg1)
                 (:e c::expr-binary->arg2)
                 (:e c::expr-binary)
                 (:e c::binop-kind)
                 (:e c::binop-asg)
                 (:e c::ident)
                 (:e c::type-nonchar-integerp)
                 c::not-errorp-when-compustate-has-var-with-type-p
                 expr-compustate-vars)
               :use (,arg1-thm-name
                     (:instance
                      ,(or lifted-thm-name
                           arg2-thm-name)
                      (limit (1- limit)))
                     (:instance
                      expr-binary-asg-congruence
                      (var ',cvar)
                      (old-arg ',old-arg2)
                      (new-arg ',new-arg2))
                     (:instance
                      expr-binary-asg-errors
                      (var ',cvar)
                      (expr ',old-arg2)
                      (fenv old-fenv))))))
           ((mv thm-event thm-name thm-index)
            (gen-expr-thm expr
                          expr-new
                          gin.vartys
                          gin.const-new
                          thm-index
                          hints)))
        (mv expr-new
            (make-gout :events (cons thm-event events)
                       :thm-index thm-index
                       :thm-name thm-name
                       :vartys gin.vartys))))
     (t (mv expr-new gout-no-thm))))

  ///

  (defret expr-unambp-of-xeq-expr-binary
    (expr-unambp expr)
    :hyp (and (expr-unambp arg1-new)
              (expr-unambp arg2-new)))

  (defret expr-annop-of-xeq-expr-binary
    (expr-annop expr)
    :hyp (and (expr-annop arg1-new)
              (expr-annop arg2-new)
              (expr-binary-infop info)))

  (defret expr-aidentp-of-xeq-expr-binary
    (expr-aidentp expr gcc)
    :hyp (and (expr-aidentp arg1-new gcc)
              (expr-aidentp arg2-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-expr-cond ((test exprp)
                       (test-new exprp)
                       (test-thm-name symbolp)
                       (then expr-optionp)
                       (then-new expr-optionp)
                       (then-thm-name symbolp)
                       (else exprp)
                       (else-new exprp)
                       (else-thm-name symbolp)
                       (gin ginp))
  :guard (and (expr-unambp test)
              (expr-annop test)
              (expr-unambp test-new)
              (expr-annop test-new)
              (expr-option-unambp then)
              (expr-option-annop then)
              (expr-option-unambp then-new)
              (expr-option-annop then-new)
              (expr-unambp else)
              (expr-annop else)
              (expr-unambp else-new)
              (expr-annop else-new))
  :returns (mv (expr exprp) (gou goutp))
  :short "Equality lifting transformation of a conditional expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     combining the possibly transformed argument expression.")
   (xdoc::p
    "We generate a theorem iff
     a theorem was generated for the argument expressions,
     and the argument expressions are pure.
     The theorem is proved via a few general ones that we prove below.
     These are a bit more complicated than for strict expressions,
     because conditional expressions are non-strict:
     the branch not taken could return an error
     while the conditional expression does not."))
  (b* (((gin gin) gin)
       (expr (make-expr-cond :test test :then then :else else))
       (expr-new (make-expr-cond :test test-new :then then-new :else else-new))
       ((unless (and test-thm-name
                     then-thm-name
                     else-thm-name
                     (expr-purep test)
                     (expr-option-purep then)
                     (expr-purep else)))
        (mv expr-new (gout-no-thm gin)))
       ((mv & old-test) (ldm-expr test)) ; ERP must be NIL
       ((mv & old-then) (ldm-expr-option then)) ; ERP must be NIL
       ((mv & old-else) (ldm-expr else)) ; ERP must be NIL
       ((mv & new-test) (ldm-expr test-new)) ; ERP must be NIL
       ((mv & new-then) (ldm-expr-option then-new)) ; ERP must be NIL
       ((mv & new-else) (ldm-expr else-new)) ; ERP must be NIL
       (hints `(("Goal"
                 :in-theory '((:e c::expr-cond)
                              (:e c::type-nonchar-integerp))
                 :use (,test-thm-name
                       ,then-thm-name
                       ,else-thm-name
                       (:instance
                        expr-cond-true-congruence
                        (old-test ',old-test)
                        (old-then ',old-then)
                        (old-else ',old-else)
                        (new-test ',new-test)
                        (new-then ',new-then)
                        (new-else ',new-else))
                       (:instance
                        expr-cond-false-congruence
                        (old-test ',old-test)
                        (old-then ',old-then)
                        (old-else ',old-else)
                        (new-test ',new-test)
                        (new-then ',new-then)
                        (new-else ',new-else))
                       (:instance
                        expr-cond-test-errors
                        (test ',old-test)
                        (then ',old-then)
                        (else ',old-else))
                       (:instance
                        expr-cond-then-errors
                        (test ',old-test)
                        (then ',old-then)
                        (else ',old-else))
                       (:instance
                        expr-cond-else-errors
                        (test ',old-test)
                        (then ',old-then)
                        (else ',old-else))))))
       ((mv thm-event thm-name thm-index)
        (gen-expr-pure-thm expr
                           expr-new
                           gin.vartys
                           gin.const-new
                           gin.thm-index
                           hints)))
    (mv expr-new
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))

  ///

  (defret expr-unambp-of-xeq-expr-cond
    (expr-unambp expr)
    :hyp (and (expr-unambp test-new)
              (expr-option-unambp then-new)
              (expr-unambp else-new)))

  (defret expr-annop-of-xeq-expr-cond
    (expr-annop expr)
    :hyp (and (expr-annop test-new)
              (expr-option-annop then-new)
              (expr-annop else-new)))

  (defret expr-aidentp-of-xeq-expr-cond
    (expr-aidentp expr gcc)
    :hyp (and (expr-aidentp test-new gcc)
              (expr-option-aidentp then-new gcc)
              (expr-aidentp else-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-initer-single ((expr exprp)
                           (expr-new exprp)
                           (expr-thm-name symbolp)
                           (gin ginp))
  :guard (and (expr-unambp expr)
              (expr-annop expr)
              (expr-unambp expr-new)
              (expr-annop expr-new))
  :returns (mv (initer initerp) (gout goutp))
  :short "Equality lifting transformation of
          an initializer consisting of a single expression."
  (b* (((gin gin) gin)
       (initer (initer-single expr))
       (initer-new (initer-single expr-new))
       ((unless (and expr-thm-name
                     (expr-purep expr)))
        (mv initer-new (gout-no-thm gin)))
       ((mv & old-expr) (ldm-expr expr)) ; ERP must be NIL
       ((mv & new-expr) (ldm-expr expr-new)) ; ERP must be NIL
       (hints
        `(("Goal"
           :in-theory '((:e c::initer-kind)
                        (:e c::initer-single)
                        (:e c::initer-single->get)
                        (:e c::expr-purep)
                        (:e c::expr-kind)
                        (:e c::expr-binary->op)
                        (:e c::binop-kind)
                        (:e c::type-nonchar-integerp)
                        (:e c::expr-pure-limit)
                        initer-compustate-vars)
           :use ((:instance ,expr-thm-name)
                 (:instance initer-single-pure-congruence
                            (old-expr ',old-expr)
                            (new-expr ',new-expr))
                 (:instance initer-single-pure-errors
                            (expr ',old-expr)
                            (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-initer-single-thm initer
                               initer-new
                               gin.vartys
                               gin.const-new
                               gin.thm-index
                               hints)))
    (mv initer-new
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))

  ///

  (defret initer-unambp-of-xeq-initer-single
    (initer-unambp initer)
    :hyp (expr-unambp expr-new))

  (defret initer-annop-of-xeq-initer-single
    (initer-annop initer)
    :hyp (expr-annop expr-new))

  (defret initer-aidentp-of-xeq-initer-single
    (initer-aidentp initer gcc)
    :hyp (expr-aidentp expr-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-stmt-expr ((expr? expr-optionp)
                       (expr?-new expr-optionp)
                       (expr?-thm-name symbolp)
                       info
                       (gin ginp))
  :guard (and (expr-option-unambp expr?)
              (expr-option-annop expr?)
              (expr-option-unambp expr?-new)
              (expr-option-annop expr?-new)
              (iff expr? expr?-new))
  :returns (mv (stmt stmtp) (gout goutp))
  :short "Equality lifting transformation of an expression statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put the optional expression into an expression statement.")
   (xdoc::p
    "We generate a theorem
     if there is no expression (i.e. the null statement),
     or if we have a theorem for a supported expression.
     If the expression is pure, its theorem refers to @(tsee c::exec-expr-pure),
     and so we lift that to a theorem that refers to @(tsee c::exec-expr).
     An expression statement does not change the variables in scope,
     so we use the variable-type map from the validation table in the AST
     for both before and after the statement, in the generated theorem."))
  (b* (((gin gin) gin)
       (stmt (make-stmt-expr :expr? expr? :info info))
       (stmt-new (make-stmt-expr :expr? expr?-new :info info))
       ((unless (iff expr? expr?-new))
        (raise "Internal error: ~
                return statement with optional expression ~x0 ~
                is transformed into ~
                return statement with optional expression ~x1."
               expr? expr?-new)
        (mv stmt-new (irr-gout)))
       ((unless (or (not expr?)
                    expr?-thm-name))
        (mv stmt-new (gout-no-thm gin)))
       ((mv lifted-thm-name thm-index events)
        (if (and expr?
                 (expr-purep expr?)
                 (not (expr-case expr? :ident))
                 (not (expr-case expr? :const))
                 (not (expr-case expr? :unary)))
            (b* (((mv thm-event thm-name thm-index)
                  (lift-expr-pure-thm expr?
                                      expr?-new
                                      expr?-thm-name
                                      gin.vartys
                                      gin.const-new
                                      gin.thm-index)))
              (mv thm-name thm-index (cons thm-event gin.events)))
          (mv nil gin.thm-index gin.events)))
       ((mv & old-expr?) (ldm-expr-option expr?)) ; ERP must be NIL
       ((mv & new-expr?) (ldm-expr-option expr?-new)) ; ERP must be NIL
       (hints
        (if expr?
            `(("Goal"
               :in-theory '((:e c::stmt-kind)
                            (:e c::stmt-expr->get)
                            (:e c::stmt-expr)
                            (:e set::insert)
                            expr-compustate-vars
                            stmt-compustate-vars)
               :use ((:instance
                      ,(or lifted-thm-name
                           expr?-thm-name)
                      (limit (1- limit)))
                     (:instance
                      stmt-expr-congruence
                      (old-expr ',old-expr?)
                      (new-expr ',new-expr?))
                     (:instance
                      stmt-expr-errors
                      (expr ',old-expr?)
                      (fenv old-fenv)))))
          `(("Goal"
             :in-theory '((:e c::stmt-kind)
                          (:e c::stmt-null)
                          c::type-option-of-stmt-value
                          (:e set::in)
                          (:e set::insert)
                          stmt-compustate-vars)
             :use (stmt-null-congruence)))))
       ((mv thm-event thm-name thm-index)
        (gen-stmt-thm stmt
                      stmt-new
                      gin.vartys
                      gin.const-new
                      thm-index
                      hints)))
    (mv stmt-new
        (make-gout :events (cons thm-event events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))
  :guard-hints (("Goal" :in-theory (enable ldm-expr-option)))

  ///

  (defret stmt-unambp-of-xeq-stmt-expr
    (stmt-unambp stmt)
    :hyp (expr-option-unambp expr?-new))

  (defret stmt-annop-of-xeq-stmt-expr
    (stmt-annop stmt)
    :hyp (expr-option-annop expr?-new))

  (defret stmt-aidentp-of-xeq-stmt-expr
    (stmt-aidentp stmt gcc)
    :hyp (expr-option-aidentp expr?-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-stmt-return ((expr? expr-optionp)
                         (expr?-new expr-optionp)
                         (expr?-thm-name symbolp)
                         info
                         (gin ginp))
  :guard (and (expr-option-unambp expr?)
              (expr-option-annop expr?)
              (expr-option-unambp expr?-new)
              (expr-option-annop expr?-new)
              (iff expr? expr?-new))
  :returns (mv (stmt stmtp) (gout goutp))
  :short "Equality lifting transformation of a return statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put the new optional expression into a return statement.")
   (xdoc::p
    "We generate a theorem iff
     the expression is absent
     or a theorem was generated for the expression.
     Note that the expression is present in the old statement
     iff it is present in the new statement;
     also note that, if there is no expression,
     old and new statements are syntactically equal."))
  (b* (((gin gin) gin)
       (stmt (make-stmt-return :expr? expr? :info info))
       (stmt-new (make-stmt-return :expr? expr?-new :info info))
       ((unless (iff expr? expr?-new))
        (raise "Internal error: ~
                return statement with optional expression ~x0 ~
                is transformed into ~
                return statement with optional expression ~x1."
               expr? expr?-new)
        (mv stmt-new (irr-gout)))
       ((unless (or (not expr?)
                    expr?-thm-name))
        (mv stmt-new (gout-no-thm gin)))
       ((mv & old-expr?) (ldm-expr-option expr?)) ; ERP must be NIL
       ((mv & new-expr?) (ldm-expr-option expr?-new)) ; ERP must be NIL
       ((mv lifted-thm-name thm-index events)
        (if (and expr?
                 (expr-purep expr?)
                 (not (expr-case expr? :ident))
                 (not (expr-case expr? :const))
                 (not (expr-case expr? :unary)))
            (b* (((mv thm-event thm-name thm-index)
                  (lift-expr-pure-thm expr?
                                      expr?-new
                                      expr?-thm-name
                                      gin.vartys
                                      gin.const-new
                                      gin.thm-index)))
              (mv thm-name thm-index (cons thm-event gin.events)))
          (mv nil gin.thm-index gin.events)))
       (hints (if expr?
                  `(("Goal"
                     :in-theory '((:e set::insert)
                                  (:e c::stmt-kind)
                                  (:e c::stmt-return)
                                  (:e c::stmt-return->value)
                                  (:e c::type-nonchar-integerp)
                                  stmt-compustate-vars)
                     :use ((:instance ,(or lifted-thm-name expr?-thm-name)
                                      (limit (1- limit)))
                           (:instance stmt-return-value-congruence
                                      (old-expr ',old-expr?)
                                      (new-expr ',new-expr?))
                           (:instance stmt-return-errors
                                      (expr ',old-expr?)
                                      (fenv old-fenv)))))
                `(("Goal"
                   :in-theory '((:e c::stmt-return)
                                (:e c::type-void)
                                (:e set::insert)
                                stmt-compustate-vars)
                   :use (stmt-return-novalue-congruence)))))
       ((mv thm-event thm-name thm-index)
        (gen-stmt-thm stmt
                      stmt-new
                      gin.vartys
                      gin.const-new
                      thm-index
                      hints)))
    (mv stmt-new
        (make-gout :events (cons thm-event events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))

  ///

  (defret stmt-unambp-of-xeq-stmt-return
    (stmt-unambp stmt)
    :hyp (expr-option-unambp expr?-new))

  (defret stmt-annop-of-xeq-stmt-return
    (stmt-annop stmt)
    :hyp (expr-option-annop expr?-new))

  (defret stmt-aidentp-of-xeq-stmt-return
    (stmt-aidentp stmt gcc)
    :hyp (expr-option-aidentp expr?-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-stmt-if ((test exprp)
                     (test-new exprp)
                     (test-thm-name symbolp)
                     (then stmtp)
                     (then-new stmtp)
                     (then-thm-name symbolp)
                     (gin ginp))
  :guard (and (expr-unambp test)
              (expr-annop test)
              (expr-unambp test-new)
              (expr-annop test-new)
              (stmt-unambp then)
              (stmt-annop then)
              (stmt-unambp then-new)
              (stmt-annop then-new))
  :returns (mv (stmt stmtp) (gout goutp))
  :short "Equality lifting transformation of
          an @('if') statement (without @('else'))."
  (b* (((gin gin) gin)
       (stmt (make-stmt-if :test test :then then))
       (stmt-new (make-stmt-if :test test-new :then then-new))
       ((unless (and test-thm-name
                     then-thm-name
                     (expr-purep test)))
        (mv stmt-new (gout-no-thm gin)))
       (then-types (stmt-types then))
       ((mv & old-test) (ldm-expr test)) ; ERP must be NIL
       ((mv & new-test) (ldm-expr test-new)) ; ERP must be NIL
       ((mv & old-then) (ldm-stmt then)) ; ERP must be NIL
       ((mv & new-then) (ldm-stmt then-new)) ; ERP must be NIL
       ((mv & then-ctypes) (ldm-type-option-set then-types)) ; ERP must be NIL
       (hints `(("Goal"
                 :in-theory
                 '((:e c::stmt-kind)
                   (:e c::stmt-if->test)
                   (:e c::stmt-if->then)
                   (:e c::stmt-if)
                   (:e c::type-nonchar-integerp)
                   (:e set::insert)
                   (:e set::subset)
                   set::subset-in
                   c::compustate-frames-number-of-exec-stmt
                   c::compustatep-when-compustate-resultp-and-not-errorp
                   stmt-compustate-vars)
                 :use (,test-thm-name
                       (:instance ,then-thm-name (limit (1- limit)))
                       (:instance
                        stmt-if-true-congruence
                        (old-test ',old-test)
                        (old-then ',old-then)
                        (new-test ',new-test)
                        (new-then ',new-then)
                        (types ',then-ctypes))
                       (:instance
                        stmt-if-false-congruence
                        (old-test ',old-test)
                        (old-then ',old-then)
                        (new-test ',new-test)
                        (new-then ',new-then))
                       (:instance
                        stmt-if-test-errors
                        (test ',old-test)
                        (then ',old-then)
                        (fenv old-fenv))
                       (:instance
                        stmt-if-then-errors
                        (test ',old-test)
                        (then ',old-then)
                        (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-stmt-thm stmt
                      stmt-new
                      gin.vartys
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv stmt-new
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))

  ///

  (defret stmt-unambp-of-xeq-stmt-if
    (stmt-unambp stmt)
    :hyp (and (expr-unambp test-new)
              (stmt-unambp then-new)))

  (defret stmt-annop-of-xeq-stmt-if
    (stmt-annop stmt)
    :hyp (and (expr-annop test-new)
              (stmt-annop then-new)))

  (defret stmt-aidentp-of-xeq-stmt-if
    (stmt-aidentp stmt gcc)
    :hyp (and (expr-aidentp test-new gcc)
              (stmt-aidentp then-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-stmt-ifelse ((test exprp)
                         (test-new exprp)
                         (test-thm-name symbolp)
                         (then stmtp)
                         (then-new stmtp)
                         (then-thm-name symbolp)
                         (else stmtp)
                         (else-new stmtp)
                         (else-thm-name symbolp)
                         (gin ginp))
  :guard (and (expr-unambp test)
              (expr-annop test)
              (expr-unambp test-new)
              (expr-annop test-new)
              (stmt-unambp then)
              (stmt-annop then)
              (stmt-unambp then-new)
              (stmt-annop then-new)
              (stmt-unambp else)
              (stmt-annop else)
              (stmt-unambp else-new)
              (stmt-annop else-new))
  :returns (mv (stmt stmtp) (gout goutp))
  :short "Equality lifting transformation of an @('if')-@('else') statement."
  (b* (((gin gin) gin)
       (stmt (make-stmt-ifelse :test test :then then :else else))
       (stmt-new
        (make-stmt-ifelse :test test-new :then then-new :else else-new))
       ((unless (and test-thm-name
                     then-thm-name
                     else-thm-name
                     (expr-purep test)))
        (mv stmt-new (gout-no-thm gin)))
       (then-types (stmt-types then))
       (else-types (stmt-types else))
       ((mv & old-test) (ldm-expr test)) ; ERP must be NIL
       ((mv & new-test) (ldm-expr test-new)) ; ERP must be NIL
       ((mv & old-then) (ldm-stmt then)) ; ERP must be NIL
       ((mv & new-then) (ldm-stmt then-new)) ; ERP must be NIL
       ((mv & old-else) (ldm-stmt else)) ; ERP must be NIL
       ((mv & new-else) (ldm-stmt else-new)) ; ERP must be NIL
       ((mv & then-ctypes) (ldm-type-option-set then-types)) ; ERP must be NIL
       ((mv & else-ctypes) (ldm-type-option-set else-types)) ; ERP must be NIL
       (hints `(("Goal"
                 :in-theory
                 '((:e c::stmt-kind)
                   (:e c::stmt-ifelse->test)
                   (:e c::stmt-ifelse->then)
                   (:e c::stmt-ifelse->else)
                   (:e c::stmt-ifelse)
                   (:e c::type-nonchar-integerp)
                   (:e set::insert)
                   (:e set::subset)
                   set::subset-in
                   c::compustate-frames-number-of-exec-stmt
                   c::compustatep-when-compustate-resultp-and-not-errorp
                   stmt-compustate-vars)
                 :use (,test-thm-name
                       (:instance ,then-thm-name (limit (1- limit)))
                       (:instance ,else-thm-name (limit (1- limit)))
                       (:instance
                        stmt-ifelse-true-congruence
                        (old-test ',old-test)
                        (old-then ',old-then)
                        (old-else ',old-else)
                        (new-test ',new-test)
                        (new-then ',new-then)
                        (new-else ',new-else)
                        (types ',then-ctypes))
                       (:instance
                        stmt-ifelse-false-congruence
                        (old-test ',old-test)
                        (old-then ',old-then)
                        (old-else ',old-else)
                        (new-test ',new-test)
                        (new-then ',new-then)
                        (new-else ',new-else)
                        (types ',else-ctypes))
                       (:instance
                        stmt-ifelse-test-errors
                        (test ',old-test)
                        (then ',old-then)
                        (else ',old-else)
                        (fenv old-fenv))
                       (:instance
                        stmt-ifelse-then-errors
                        (test ',old-test)
                        (then ',old-then)
                        (else ',old-else)
                        (fenv old-fenv))
                       (:instance
                        stmt-ifelse-else-errors
                        (test ',old-test)
                        (then ',old-then)
                        (else ',old-else)
                        (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-stmt-thm stmt
                      stmt-new
                      gin.vartys
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv stmt-new
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))

  ///

  (defret stmt-unambp-of-xeq-stmt-ifelse
    (stmt-unambp stmt)
    :hyp (and (expr-unambp test-new)
              (stmt-unambp then-new)
              (stmt-unambp else-new)))

  (defret stmt-annop-of-xeq-stmt-ifelse
    (stmt-annop stmt)
    :hyp (and (expr-annop test-new)
              (stmt-annop then-new)
              (stmt-annop else-new)))

  (defret stmt-aidentp-of-xeq-stmt-ifelse
    (stmt-aidentp stmt gcc)
    :hyp (and (expr-aidentp test-new gcc)
              (stmt-aidentp then-new gcc)
              (stmt-aidentp else-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-stmt-compound ((cstmt comp-stmtp)
                           (cstmt-new comp-stmtp)
                           (cstmt-thm-name symbolp)
                           (gin ginp))
  :guard (and (comp-stmt-unambp cstmt)
              (comp-stmt-annop cstmt)
              (comp-stmt-unambp cstmt-new)
              (comp-stmt-annop cstmt-new))
  :returns (mv (stmt stmtp) (gout goutp))
  :short "Equality lifting transformation of a compound statement."
  (b* (((gin gin) gin)
       (stmt (stmt-compound cstmt))
       (stmt-new (stmt-compound cstmt-new))
       ((unless cstmt-thm-name)
        (mv stmt-new (gout-no-thm gin)))
       (types (comp-stmt-types cstmt))
       ((mv & old-items) (ldm-comp-stmt cstmt)) ; ERP must be NIL
       ((mv & new-items) (ldm-comp-stmt cstmt-new)) ; ERP must be NIL
       ((mv & ctypes) (ldm-type-option-set types)) ; ERP must be NIL
       (hints
        `(("Goal"
           :in-theory '((:e c::stmt-compound)
                        (:e c::stmt-kind)
                        c::compustate-frames-number-of-enter-scope
                        c::compustate-has-var-with-type-p-of-enter-scope
                        stmt-compustate-vars)
           :use ((:instance ,cstmt-thm-name
                            (compst (c::enter-scope compst))
                            (limit (1- limit)))
                 (:instance stmt-compound-congruence
                            (old-items ',old-items)
                            (new-items ',new-items)
                            (types ',ctypes))
                 (:instance stmt-compound-errors
                            (items ',old-items)
                            (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-stmt-thm stmt
                      stmt-new
                      gin.vartys
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv stmt-new
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))

  ///

  (defret stmt-unambp-of-xeq-stmt-compound
    (stmt-unambp stmt)
    :hyp (comp-stmt-unambp cstmt-new))

  (defret stmt-annop-of-xeq-stmt-compound
    (stmt-annop stmt)
    :hyp (comp-stmt-annop cstmt-new))

  (defret stmt-aidentp-of-xeq-stmt-compound
    (stmt-aidentp stmt gcc)
    :hyp (comp-stmt-aidentp cstmt-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-stmt-while ((test exprp)
                        (test-new exprp)
                        (test-thm-name symbolp)
                        (body stmtp)
                        (body-new stmtp)
                        (body-thm-name symbolp)
                        (gin ginp))
  :guard (and (expr-unambp test)
              (expr-annop test)
              (expr-unambp test-new)
              (expr-annop test-new)
              (stmt-unambp body)
              (stmt-annop body)
              (stmt-unambp body-new)
              (stmt-annop body-new))
  :returns (mv (stmt stmtp) (gout goutp))
  :short "Equality lifting transformation of a @('while') loop."
  (b* (((gin gin) gin)
       (stmt (make-stmt-while :test test
                              :body body))
       (stmt-new (make-stmt-while :test test-new
                                  :body body-new))
       ((unless (and test-thm-name
                     body-thm-name))
        (mv stmt-new (gout-no-thm gin)))
       (types (stmt-types body))
       ((mv & old-test) (ldm-expr test)) ; ERP must be NIL
       ((mv & new-test) (ldm-expr test-new)) ; ERP must be NIL
       ((mv & old-body) (ldm-stmt body)) ; ERP must be NIL
       ((mv & new-body) (ldm-stmt body-new)) ; ERP must be NIL
       (hints
        `(("Goal"
           :in-theory '((:e c::stmt-while)
                        (:e c::ident-type-map-fix)
                        (:e omap::emptyp)
                        (:e omap::head)
                        (:e omap::tail)
                        (:e set::insert)
                        (:e c::type-nonchar-integerp)
                        while-test-hyp
                        while-body-hyp
                        c::compustate-has-vars-with-types-p
                        stmt-compustate-vars)
           :use ((:instance
                  ,test-thm-name
                  (compst (while-test-hyp-witness ',old-test
                                                  ',new-test
                                                  ',gin.vartys)))
                 (:instance
                  ,body-thm-name
                  (compst (mv-nth 0 (while-body-hyp-witness ',old-body
                                                            ',new-body
                                                            old-fenv
                                                            new-fenv
                                                            ',types
                                                            ',gin.vartys)))
                  (limit (mv-nth 1 (while-body-hyp-witness ',old-body
                                                           ',new-body
                                                           old-fenv
                                                           new-fenv
                                                           ',types
                                                           ',gin.vartys))))
                 (:instance
                  stmt-while-theorem
                  (old-test ',old-test)
                  (new-test ',new-test)
                  (old-body ',old-body)
                  (new-body ',new-body)
                  (types ',types)
                  (vartys ',gin.vartys))))))
       ((mv thm-event thm-name thm-index)
        (gen-stmt-thm stmt
                      stmt-new
                      gin.vartys
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv stmt-new
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))

  ///

  (defret stmt-unambp-of-xeq-stmt-while
    (stmt-unambp stmt)
    :hyp (and (expr-unambp test-new)
              (stmt-unambp body-new)))

  (defret stmt-annop-of-xeq-stmt-while
    (stmt-annop stmt)
    :hyp (and (expr-annop test-new)
              (stmt-annop body-new)))

  (defret stmt-aidentp-of-xeq-stmt-while
    (stmt-aidentp stmt gcc)
    :hyp (and (expr-aidentp test-new gcc)
              (stmt-aidentp body-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-stmt-dowhile ((body stmtp)
                          (body-new stmtp)
                          (body-thm-name symbolp)
                          (test exprp)
                          (test-new exprp)
                          (test-thm-name symbolp)
                          (gin ginp))
  :guard (and (stmt-unambp body)
              (stmt-annop body)
              (stmt-unambp body-new)
              (stmt-annop body-new)
              (expr-unambp test)
              (expr-annop test)
              (expr-unambp test-new)
              (expr-annop test-new))
  :returns (mv (stmt stmtp) (gout goutp))
  :short "Equality lifting transformation of a @('do-while') loop."
  (b* (((gin gin) gin)
       (stmt (make-stmt-dowhile :body body
                                :test test))
       (stmt-new (make-stmt-dowhile :body body-new
                                    :test test-new))
       ((unless (and body-thm-name
                     test-thm-name))
        (mv stmt-new (gout-no-thm gin)))
       (types (stmt-types body))
       ((mv & old-body) (ldm-stmt body)) ; ERP must be NIL
       ((mv & new-body) (ldm-stmt body-new)) ; ERP must be NIL
       ((mv & old-test) (ldm-expr test)) ; ERP must be NIL
       ((mv & new-test) (ldm-expr test-new)) ; ERP must be NIL
       (hints
        `(("Goal"
           :in-theory '((:e c::stmt-dowhile)
                        (:e c::ident-type-map-fix)
                        (:e omap::emptyp)
                        (:e omap::head)
                        (:e omap::tail)
                        (:e set::insert)
                        (:e c::type-nonchar-integerp)
                        dowhile-test-hyp
                        dowhile-body-hyp
                        c::compustate-has-vars-with-types-p
                        stmt-compustate-vars)
           :use ((:instance
                  ,body-thm-name
                  (compst (mv-nth 0 (dowhile-body-hyp-witness ',old-body
                                                              ',new-body
                                                              old-fenv
                                                              new-fenv
                                                              ',types
                                                              ',gin.vartys)))
                  (limit (mv-nth 1 (dowhile-body-hyp-witness ',old-body
                                                             ',new-body
                                                             old-fenv
                                                             new-fenv
                                                             ',types
                                                             ',gin.vartys))))
                 (:instance
                  ,test-thm-name
                  (compst (dowhile-test-hyp-witness ',old-test
                                                    ',new-test
                                                    ',gin.vartys)))
                 (:instance
                  stmt-dowhile-theorem
                  (old-body ',old-body)
                  (new-body ',new-body)
                  (old-test ',old-test)
                  (new-test ',new-test)
                  (types ',types)
                  (vartys ',gin.vartys))))))
       ((mv thm-event thm-name thm-index)
        (gen-stmt-thm stmt
                      stmt-new
                      gin.vartys
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv stmt-new
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))

  ///

  (defret stmt-unambp-of-xeq-stmt-dowhile
    (stmt-unambp stmt)
    :hyp (and (stmt-unambp body-new)
              (expr-unambp test-new)))

  (defret stmt-annop-of-xeq-stmt-dowhile
    (stmt-annop stmt)
    :hyp (and (stmt-annop body-new)
              (expr-annop test-new)))

  (defret stmt-aidentp-of-xeq-stmt-dowhile
    (stmt-aidentp stmt gcc)
    :hyp (and (stmt-aidentp body-new gcc)
              (expr-aidentp test-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-decl-decl ((extension booleanp)
                       (specs decl-spec-listp)
                       (specs-new decl-spec-listp)
                       (specs-thm-name symbolp)
                       (init initdeclor-listp)
                       (init-new initdeclor-listp)
                       (init-thm-name symbolp)
                       (vartys-post c::ident-type-mapp)
                       (gin ginp))
  :guard (and (decl-spec-list-unambp specs)
              (decl-spec-list-annop specs)
              (decl-spec-list-unambp specs-new)
              (decl-spec-list-annop specs-new)
              (initdeclor-list-unambp init)
              (initdeclor-list-annop init)
              (initdeclor-list-unambp init-new)
              (initdeclor-list-annop init-new))
  :returns (mv (decl declp) (gout goutp))
  :short "Equality lifting transformation of a non-static-assert declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We combine the (untransformed) extension flag
     with the possibly transformed
     declaration specifiers and initializer declarators.")
   (xdoc::p
    "Currently we do not generate theorems for lists of declaration specifiers.
     We double-check that here."))
  (b* (((gin gin) gin)
       (decl (make-decl-decl :extension extension
                             :specs specs
                             :init init))
       (decl-new (make-decl-decl :extension extension
                                 :specs specs-new
                                 :init init-new))
       (gout-no-thm (change-gout (gout-no-thm gin)
                                 :vartys vartys-post))
       ((when specs-thm-name)
        (raise "Internal error: ~
                new list of initializer declarators ~x0 ~
                is not in the formalized subset."
               init)
        (mv decl-new (irr-gout)))
       ((unless (and init-thm-name
                     (decl-block-formalp decl)))
        (mv decl-new gout-no-thm))
       ((unless (decl-block-formalp decl-new))
        (raise "Internal error: ~
                new declaration ~x0 is not in the formalized subset ~
                while old declaration ~x1 is."
               decl-new decl)
        (mv decl-new (irr-gout)))
       (initdeclor (car init))
       (var (dirdeclor-ident->ident
             (declor->direct
              (initdeclor->declor initdeclor))))
       (initer (initdeclor->init? initdeclor))
       (initdeclor-new (car init-new))
       ((unless (equal var (dirdeclor-ident->ident
                            (declor->direct
                             (initdeclor->declor initdeclor-new)))))
        (raise "Internal error: ~
                new variable ~x0 differs from old variable ~x1."
               (dirdeclor-ident->ident
                (declor->direct
                 (initdeclor->declor initdeclor-new)))
               var)
        (mv decl-new (irr-gout)))
       (initer-new (initdeclor->init? initdeclor-new))
       ((unless (equal specs specs-new))
        (raise "Internal error: ~
                new declaration specifiers ~x0 differ from ~
                old declaration specifiers ~x1."
               specs-new specs)
        (mv decl-new (irr-gout)))
       ((mv & tyspecs) (check-decl-spec-list-all-typespec specs))
       ((mv & ctyspecs) (ldm-type-spec-list tyspecs))
       (ctype (c::tyspecseq-to-type ctyspecs))
       ((unless (c::type-nonchar-integerp ctype))
        (mv decl-new gout-no-thm))
       ((mv & cvar) (ldm-ident var))
       ((mv & old-initer) (ldm-initer initer))
       ((mv & new-initer) (ldm-initer initer-new))
       (hints `(("Goal"
                 :in-theory
                 '((:e c::obj-declon->scspec)
                   (:e c::obj-declon->tyspec)
                   (:e c::obj-declon->declor)
                   (:e c::obj-declon->init?)
                   (:e c::obj-declon)
                   (:e c::obj-declor-kind)
                   (:e c::obj-declor-ident->get)
                   (:e c::obj-declor-ident)
                   (:e c::scspecseq-none)
                   (:e c::tyspecseq-to-type)
                   (:e c::identp)
                   c::compustate-frames-number-of-exec-initer
                   c::compustatep-when-compustate-resultp-and-not-errorp
                   decl-decl-compustate-vars-old
                   decl-decl-compustate-vars-new)
                 :use ((:instance ,init-thm-name (limit (1- limit)))
                       (:instance
                        decl-decl-congruence
                        (var ',cvar)
                        (tyspecs ',ctyspecs)
                        (old-initer ',old-initer)
                        (new-initer ',new-initer))
                       (:instance
                        decl-decl-errors
                        (var ',cvar)
                        (tyspecs ',ctyspecs)
                        (initer ',old-initer)
                        (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-decl-thm decl
                      decl-new
                      gin.vartys
                      vartys-post
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv decl-new
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys vartys-post)))
  :guard-hints (("Goal" :in-theory (enable decl-block-formalp
                                           initdeclor-block-formalp
                                           declor-block-formalp
                                           dirdeclor-block-formalp)))

  ///

  (defret decl-unambp-of-xeq-decl-decl
    (decl-unambp decl)
    :hyp (and (decl-spec-list-unambp specs-new)
              (initdeclor-list-unambp init-new)))

  (defret decl-annop-of-xeq-decl-decl
    (decl-annop decl)
    :hyp (and (decl-spec-list-annop specs-new)
              (initdeclor-list-annop init-new)))

  (defret decl-aidentp-of-xeq-decl-decl
    (decl-aidentp decl gcc)
    :hyp (and (decl-spec-list-aidentp specs-new gcc)
              (initdeclor-list-aidentp init-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-block-item-stmt ((stmt stmtp)
                             (stmt-new stmtp)
                             (stmt-thm-name symbolp)
                             info
                             (gin ginp))
  :guard (and (stmt-unambp stmt)
              (stmt-annop stmt)
              (stmt-unambp stmt-new)
              (stmt-annop stmt-new))
  :returns (mv (item block-itemp) (gout goutp))
  :short "Equality lifting transformation of
          a block items that consists of a statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put the new statement into a block item."))
  (b* (((gin gin) gin)
       (item (make-block-item-stmt :stmt stmt :info info))
       (item-new (make-block-item-stmt :stmt stmt-new :info info))
       ((unless stmt-thm-name)
        (mv item-new (gout-no-thm gin)))
       (types (stmt-types stmt))
       ((mv & old-stmt) (ldm-stmt stmt)) ; ERP must be NIL
       ((mv & new-stmt) (ldm-stmt stmt-new)) ; ERP must be NIL
       ((mv & ctypes) (ldm-type-option-set types)) ; ERP must be NIL
       (hints `(("Goal"
                 :in-theory
                 '((:e c::block-item-stmt)
                   (:e c::block-item-kind)
                   (:e c::block-item-stmt->get)
                   c::compustate-frames-number-of-exec-stmt
                   c::compustatep-when-compustate-resultp-and-not-errorp
                   block-item-stmt-compustate-vars)
                 :use ((:instance ,stmt-thm-name (limit (1- limit)))
                       (:instance
                        block-item-stmt-congruence
                        (old-stmt ',old-stmt)
                        (new-stmt ',new-stmt)
                        (types ',ctypes))
                       (:instance
                        block-item-stmt-errors
                        (stmt ',old-stmt)
                        (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-block-item-thm item
                            item-new
                            gin.vartys
                            gin.vartys
                            gin.const-new
                            gin.thm-index
                            hints)))
    (mv item-new
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))

  ///

  (defret block-item-unambp-of-xeq-block-item-stmt
    (block-item-unambp item)
    :hyp (stmt-unambp stmt-new))

  (defret block-item-annop-of-xeq-block-item-stmt
    (block-item-annop item)
    :hyp (stmt-annop stmt-new))

  (defret block-item-aidentp-of-xeq-block-item-stmt
    (block-item-aidentp item gcc)
    :hyp (stmt-aidentp stmt-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-block-item-decl ((decl declp)
                             (decl-new declp)
                             (decl-thm-name symbolp)
                             info
                             (vartys-post c::ident-type-mapp)
                             (gin ginp))
  :guard (and (decl-unambp decl)
              (decl-annop decl)
              (decl-unambp decl-new)
              (decl-annop decl-new))
  :returns (mv (item block-itemp) (gout goutp))
  :short "Equality lifting transformation of
          a block item that consists of a declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put the new declaration into a block item."))
  (b* (((gin gin) gin)
       (item (make-block-item-decl :decl decl :info info))
       (item-new (make-block-item-decl :decl decl-new :info info))
       (gout-no-thm (change-gout (gout-no-thm gin)
                                 :vartys vartys-post))
       ((unless decl-thm-name) (mv item-new gout-no-thm))
       ((mv & old-declon) (ldm-decl-obj decl)) ; ERP must be NIL
       ((mv & new-declon) (ldm-decl-obj decl-new)) ; ERP must be NIL
       (hints `(("Goal"
                 :in-theory
                 '((:e c::block-item-declon)
                   (:e c::block-item-kind)
                   (:e c::block-item-declon->get)
                   (:e set::insert)
                   c::compustate-frames-number-of-exec-obj-declon
                   c::compustatep-when-compustate-resultp-and-not-errorp
                   block-item-decl-compustate-vars)
                 :use ((:instance ,decl-thm-name (limit (1- limit)))
                       (:instance
                        block-item-decl-congruence
                        (old-declon ',old-declon)
                        (new-declon ',new-declon))
                       (:instance
                        block-item-decl-errors
                        (declon ',old-declon)
                        (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-block-item-thm item
                            item-new
                            gin.vartys
                            vartys-post
                            gin.const-new
                            gin.thm-index
                            hints)))
    (mv item-new
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys vartys-post)))
  :guard-hints (("Goal" :in-theory (enable decl-block-formalp
                                           initdeclor-block-formalp
                                           declor-block-formalp
                                           dirdeclor-block-formalp)))

  ///

  (defret block-item-unambp-of-xeq-block-item-decl
    (block-item-unambp item)
    :hyp (decl-unambp decl-new))

  (defret block-item-annop-of-xeq-block-item-decl
    (block-item-annop item)
    :hyp (decl-annop decl-new))

  (defret block-item-aidentp-of-xeq-block-item-decl
    (block-item-aidentp item gcc)
    :hyp (decl-aidentp decl-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-block-item-list-empty ((gin ginp))
  :returns (gout goutp)
  :short "Equality lifting transformation of the empty list of block items."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is introduced mainly for uniformity.
     It actually takes and returns no block item list,
     because there is only one empty block item list."))
  (b* (((gin gin) gin)
       (items nil)
       (hints `(("Goal"
                 :in-theory '((:e set::insert)
                              block-item-list-empty-compustate-vars)
                 :use (block-item-list-empty-congruence))))
       ((mv thm-event thm-name thm-index)
        (gen-block-item-list-thm items
                                 items
                                 gin.vartys
                                 gin.const-new
                                 gin.thm-index
                                 hints)))
    (make-gout :events (cons thm-event gin.events)
               :thm-index thm-index
               :thm-name thm-name
               :vartys gin.vartys))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-block-item-list-cons ((item block-itemp)
                                  (item-new block-itemp)
                                  (item-thm-name symbolp)
                                  (items block-item-listp)
                                  (items-new block-item-listp)
                                  (items-thm-name symbolp)
                                  (gin ginp))
  :guard (and (block-item-unambp item)
              (block-item-annop item)
              (block-item-unambp item-new)
              (block-item-annop item-new)
              (block-item-list-unambp items)
              (block-item-list-annop items)
              (block-item-list-unambp items-new)
              (block-item-list-annop items-new))
  :returns (mv (item+items block-item-listp) (gout goutp))
  :short "Equality lifting transformation of a non-empty list of block items."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting list of block items is obtained by
     @(tsee cons)ing the possibly transformed first item
     and the possibly transformed rest of the items.")
   (xdoc::p
    "We generate a theorem iff theorems were generated for
     both the first item and (the list of) the rest of the items."))
  (b* (((gin gin) gin)
       (item (block-item-fix item))
       (items (block-item-list-fix items))
       (item-new (block-item-fix item-new))
       (items-new (block-item-list-fix items-new))
       (item+items (cons item items))
       (item+items-new (cons item-new items-new))
       (gout-no-thm (gout-no-thm gin))
       ((unless (and item-thm-name
                     items-thm-name))
        (mv item+items-new gout-no-thm))
       (first-types (block-item-types item))
       (rest-types (block-item-list-types items))
       ((mv & old-item) (ldm-block-item item)) ; ERP must be NIL
       ((mv & new-item) (ldm-block-item item-new)) ; ERP must be NIL
       ((mv & old-items) (ldm-block-item-list items)) ; ERP must be NIL
       ((mv & new-items) (ldm-block-item-list items-new)) ; ERP must be NIL
       ((mv & first-ctypes) (ldm-type-option-set first-types)) ; ERP must be NIL
       ((mv & rest-ctypes) (ldm-type-option-set rest-types)) ; ERP must be NIL
       (hints
        `(("Goal"
           :in-theory
           '(c::stmt-value-kind-possibilities
             (:e set::delete)
             (:e set::union)
             c::compustate-frames-number-of-exec-block-item
             c::compustatep-when-compustate-resultp-and-not-errorp
             block-item-list-cons-compustate-vars)
           :use ((:instance
                  ,item-thm-name
                  (limit (1- limit)))
                 (:instance
                  ,items-thm-name
                  (compst
                   (mv-nth 1 (c::exec-block-item
                              ',old-item compst old-fenv (1- limit))))
                  (limit (1- limit)))
                 (:instance
                  block-item-list-cons-first-congruence
                  (old-item ',old-item)
                  (old-items ',old-items)
                  (new-item ',new-item)
                  (new-items ',new-items)
                  (first-types ',first-ctypes)
                  (rest-types ',rest-ctypes))
                 (:instance
                  block-item-list-cons-rest-congruence
                  (old-item ',old-item)
                  (old-items ',old-items)
                  (new-item ',new-item)
                  (new-items ',new-items)
                  (first-types ',first-ctypes)
                  (rest-types ',rest-ctypes))
                 (:instance
                  block-item-list-cons-first-errors
                  (item ',old-item)
                  (items ',old-items)
                  (fenv old-fenv))
                 (:instance
                  block-item-list-cons-rest-errors
                  (item ',old-item)
                  (items ',old-items)
                  (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-block-item-list-thm item+items
                                 item+items-new
                                 gin.vartys
                                 gin.const-new
                                 gin.thm-index
                                 hints)))
    (mv item+items-new
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))

  ///

  (fty::deffixequiv xeq-block-item-list-cons
    :args ((item block-itemp)
           (item-new block-itemp)
           (items block-item-listp)
           (items-new block-item-listp)))

  (defret block-item-list-unambp-of-xeq-block-item-list-cons
    (block-item-list-unambp item+items)
    :hyp (and (block-item-unambp item-new)
              (block-item-list-unambp items-new)))

  (defret block-item-list-annop-of-xeq-block-item-list-cons
    (block-item-list-annop item+items)
    :hyp (and (block-item-annop item-new)
              (block-item-list-annop items-new)))

  (defret block-item-list-aidentp-of-xeq-block-item-list-cons
    (block-item-list-aidentp item+items gcc)
    :hyp (and (block-item-aidentp item-new gcc)
              (block-item-list-aidentp items-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-fundef ((extension booleanp)
                    (spec decl-spec-listp)
                    (spec-new decl-spec-listp)
                    (declor declorp)
                    (declor-new declorp)
                    (asm? asm-name-spec-optionp)
                    (attribs attrib-spec-listp)
                    (decls decl-listp)
                    (decls-new decl-listp)
                    (body comp-stmtp)
                    (body-new comp-stmtp)
                    (body-thm-name symbolp)
                    (info fundef-infop)
                    (gin ginp))
  :guard (and (decl-spec-list-unambp spec)
              (decl-spec-list-annop spec)
              (decl-spec-list-unambp spec-new)
              (decl-spec-list-annop spec-new)
              (declor-unambp declor)
              (declor-annop declor)
              (declor-unambp declor-new)
              (declor-annop declor-new)
              (decl-list-unambp decls)
              (decl-list-annop decls)
              (decl-list-unambp decls-new)
              (decl-list-annop decls-new)
              (comp-stmt-unambp body)
              (comp-stmt-annop body)
              (comp-stmt-unambp body-new)
              (comp-stmt-annop body-new))
  :returns (mv (fundef fundefp) (gout goutp))
  :short "Equality lifting transformation of a function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a theorem for the function
     only under certain conditions,
     including the fact that a theorem for the body gets generated.")
   (xdoc::p
    "We generate the following theorems:")
   (xdoc::ul
    (xdoc::li
     "A theorem about the initial scope of the function body.
      See @(tsee gen-init-scope-thm).")
    (xdoc::li
     "For each function parameter, a theorem saying that,
      after pushing a frame with the initial scope above,
      the computation state has a variable for the parameter
      with the associated type.")
    (xdoc::li
     "The main theorem for the function definition,
      saying that, if the execution of the old function does not yield an error,
      neither does the execition of the new function,
      and they return the same results and computation states."))
   (xdoc::p
    "We use @(tsee gen-from-params) to obtain
     certain information from the parameters,
     which is used to generate the theorems.
     This information includes the variable-type map
     corresponding to the function parameters:
     we ensure that it is the same as
     the variable-type map from the validation table
     that annotates the start of the function body.
     In general the former is a sub-map of the latter,
     because the validation table could include global variables;
     but for now proof generation does not handle global variables,
     so we generate proofs for the body only if
     the theorems about the initial scope and the parameters
     suffice to establish the variable-type hypotheses of the body.")
   (xdoc::p
    "The function may use global variables not hidden by parameters.
     No assertions about global variables
     are returned by @(tsee gen-from-params).
     We generate them directly from @('gin.vartys'),
     after removing from that map
     any keys that are also function parameters,
     which hide the corresponding global variables."))
  (b* (((gin gin) gin)
       (fundef (make-fundef :extension extension
                            :spec spec
                            :declor declor
                            :asm? asm?
                            :attribs attribs
                            :decls decls
                            :body body
                            :info info))
       (new-fundef (make-fundef :extension extension
                                :spec spec-new
                                :declor declor-new
                                :asm? asm?
                                :attribs attribs
                                :decls decls-new
                                :body body-new
                                :info info))
       (type (fundef-info->type info))
       (ident (declor->ident declor))
       (vartys-after-fundef (if (and (ident-formalp ident)
                                     (type-formalp type)
                                     (not (type-case type :void))
                                     (not (type-case type :char)))
                                (b* (((mv & cvar) (ldm-ident ident))
                                     ((mv & ctype) (ldm-type type)))
                                  (omap::update cvar ctype gin.vartys))
                              gin.vartys))
       (gout-no-thm (change-gout (gout-no-thm gin) :vartys vartys-after-fundef))
       ((unless body-thm-name) (mv new-fundef gout-no-thm))
       ((unless (fundef-formalp fundef)) (mv new-fundef gout-no-thm))
       ((declor declor) declor)
       ((when (consp declor.pointers)) (mv new-fundef gout-no-thm))
       ((mv okp params dirdeclor)
        (dirdeclor-case
         declor.direct
         :function-params (mv t declor.direct.params declor.direct.declor)
         :function-names (mv (endp declor.direct.names)
                             nil
                             declor.direct.declor)
         :otherwise (mv nil nil (irr-dirdeclor))))
       ((unless okp) (mv new-fundef gout-no-thm))
       ((unless (dirdeclor-case dirdeclor :ident))
        (raise "Internal error: ~x0 is not just the function name."
               dirdeclor)
        (mv new-fundef (irr-gout)))
       (fun (ident->unwrap (dirdeclor-ident->ident dirdeclor)))
       ((unless (stringp fun))
        (raise "Internal error: non-string identifier ~x0." fun)
        (mv new-fundef (irr-gout)))
       ((mv erp ldm-params) (ldm-param-declon-list params))
       ((when erp) (mv new-fundef gout-no-thm))
       (types (fundef-types fundef))
       ((mv okp args parargs arg-types arg-types-compst param-vartys)
        (gen-from-params ldm-params gin))
       ((unless okp) (mv new-fundef gout-no-thm))
       ((mv init-scope-thm-event init-scope-thm-name thm-index)
        (gen-init-scope-thm ldm-params
                            args
                            parargs
                            arg-types
                            gin.const-new
                            gin.thm-index))
       (events (cons init-scope-thm-event gin.events))
       ((mv param-thm-events param-thm-names thm-index)
        (gen-param-thms arg-types-compst
                        arg-types
                        ldm-params
                        args
                        init-scope-thm-name
                        gin.const-new
                        thm-index))
       (events (append (rev param-thm-events) events))
       ((mv thm-name thm-index) (gen-thm-name gin.const-new thm-index))
       (global-vartys (omap::delete* (omap::keys param-vartys) gin.vartys))
       (global-vars-pre
        (gen-var-assertions global-vartys
                            `(c::push-frame
                              (c::frame ',(c::ident fun)
                                        (list
                                         (c::init-scope ',ldm-params
                                                        (list ,@args))))
                              compst)))
       (formula
        `(b* ((old ',(fundef-fix fundef))
              (new ',new-fundef)
              (fun (mv-nth 1 (ldm-ident (ident ,fun))))
              ((mv old-result old-compst)
               (c::exec-fun fun (list ,@args) compst old-fenv limit))
              ((mv new-result new-compst)
               (c::exec-fun fun (list ,@args) compst new-fenv limit)))
           (implies (and ,@global-vars-pre
                         ,@arg-types
                         (equal (c::fun-env-lookup fun old-fenv)
                                (c::fun-info-from-fundef
                                 (mv-nth 1 (ldm-fundef old))))
                         (equal (c::fun-env-lookup fun new-fenv)
                                (c::fun-info-from-fundef
                                 (mv-nth 1 (ldm-fundef new))))
                         (not (c::errorp old-result)))
                    (and (not (c::errorp new-result))
                         (equal old-result new-result)
                         (equal old-compst new-compst)
                         (set::in (c::type-of-value-option old-result)
                                  (mv-nth 1 (ldm-type-set ',types)))))))
       (hints
        `(("Goal"
           :expand ((c::exec-fun
                     ',(c::ident fun) (list ,@args) compst old-fenv limit)
                    (c::exec-fun
                     ',(c::ident fun) (list ,@args) compst new-fenv limit))
           :use (,init-scope-thm-name
                 ,@(xeq-fundef-loop param-thm-names fun)
                 (:instance ,body-thm-name
                            (compst
                             (c::push-frame
                              (c::frame (mv-nth 1 (ldm-ident
                                                   (ident ,fun)))
                                        (list
                                         (c::init-scope
                                          ',ldm-params
                                          (list ,@args))))
                              compst))
                            (limit (1- limit))))
           :in-theory '((:e c::fun-info->body$inline)
                        (:e c::fun-info->params$inline)
                        (:e c::fun-info->result$inline)
                        (:e c::fun-info-from-fundef)
                        (:e ident)
                        (:e ldm-fundef)
                        (:e ldm-ident)
                        (:e ldm-type)
                        (:e ldm-type-set)
                        (:e ldm-comp-stmt)
                        (:e c::tyname-to-type)
                        (:e c::block-item-list-nocallsp)
                        (:e set::in)
                        c::errorp-of-error
                        c::compustate-frames-number-of-push-frame
                        (:t c::compustate-frames-number)))))
       (thm-event `(defrule ,thm-name
                     ,formula
                     :rule-classes nil
                     :hints ,hints)))
    (mv new-fundef
        (make-gout :events (cons thm-event events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys vartys-after-fundef)))

  :prepwork
  ((local (in-theory (disable (:e tau-system)))) ; for speed
   (define xeq-fundef-loop ((thms symbol-listp) (fun stringp))
     :returns (lemma-instances true-listp)
     :parents nil
     (b* (((when (endp thms)) nil)
          (thm (car thms))
          (lemma-instance
           `(:instance ,thm
                       (fun (mv-nth 1 (ldm-ident (ident ,fun))))
                       (compst0 compst)))
          (more-lemma-instances
           (xeq-fundef-loop (cdr thms) fun)))
       (cons lemma-instance more-lemma-instances))))

  ///

  (defret fundef-unambp-of-xeq-fundef
    (fundef-unambp fundef)
    :hyp (and (decl-spec-list-unambp spec-new)
              (declor-unambp declor-new)
              (decl-list-unambp decls-new)
              (comp-stmt-unambp body-new)))

  (defret fundef-annop-of-xeq-fundef
    (fundef-annop fundef)
    :hyp (and (decl-spec-list-annop spec-new)
              (declor-annop declor-new)
              (decl-list-annop decls-new)
              (comp-stmt-annop body-new)
              (fundef-infop info)))

  (defret fundef-aidentp-of-xeq-fundef
    (fundef-aidentp fundef gcc)
    :hyp (and (decl-spec-list-unambp spec-new)
              (decl-spec-list-aidentp spec-new gcc)
              (declor-unambp declor-new)
              (declor-aidentp declor-new gcc)
              (attrib-spec-list-aidentp attribs gcc)
              (decl-list-unambp decls-new)
              (decl-list-aidentp decls-new gcc)
              (comp-stmt-unambp body-new)
              (comp-stmt-aidentp body-new gcc))))
