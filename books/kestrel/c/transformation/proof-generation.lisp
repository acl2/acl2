; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "variables-in-computation-states")

(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/code-ensembles")
(include-book "../syntax/validation-information")
(include-book "../syntax/ascii-identifiers")
(include-book "../syntax/purity")

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

(define gen-var-assertions ((vartys c::ident-type-mapp) (compst symbolp))
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
    "The symbol @('compst') is the ACL2 variable name
     to use for the computation state."))
  (b* (((when (omap::emptyp (c::ident-type-map-fix vartys))) nil)
       ((mv var type) (omap::head vartys))
       (asrt `(c::compustate-has-var-with-type-p ',var ',type ,compst))
       (asrts (gen-var-assertions (omap::tail vartys) compst)))
    (cons asrt asrts))
  ///
  (fty::deffixequiv gen-var-assertions
    :args ((vartys c::ident-type-mapp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vartys-from-valid-table ((table c$::valid-tablep))
  :returns (vatys c::ident-type-mapp)
  :short "Generate, from a validation table,
          a map from identifiers to types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The validation table is from validation annotations.
     The resulting map contains all the variables in scope
     whose names satisfy @(tsee ident-formalp)
     and whose types satisfy @(tsee type-formalp);
     variables not satisfying these requirements are skipped.
     Given that later scopes may contain variables that shadow earlier scopes,
     we process the scopes in the validation table
     from oldest to newest, overriding map entries as applicable."))
  (vartys-from-valid-scope-list (c$::valid-table->scopes table))

  :prepwork
  ((define vartys-from-valid-scope-list ((scopes
                                          c$::valid-scope-listp))
     :returns (vartys c::ident-type-mapp :hyp :guard)
     :parents nil
     (cond ((endp scopes) nil)
           (t (omap::update*
               (vartys-from-valid-scope-list (cdr scopes))
               (vartys-from-valid-scope (car scopes)))))
     :verify-guards :after-returns

     :prepwork
     ((define vartys-from-valid-scope ((scope c$::valid-scopep))
        :returns (vartys c::ident-type-mapp)
        :parents nil
        (vartys-from-valid-ord-scope (c$::valid-scope->ord scope))

        :prepwork
        ((define vartys-from-valid-ord-scope ((oscope
                                               c$::valid-ord-scopep))
           :returns (vartys c::ident-type-mapp :hyp :guard)
           :parents nil
           (b* (((when (endp oscope)) nil)
                ((cons ident info) (car oscope))
                (vartys (vartys-from-valid-ord-scope (cdr oscope)))
                ((unless (ident-formalp ident)) vartys)
                ((unless (c$::valid-ord-info-case info :objfun)) vartys)
                (type (c$::valid-ord-info-objfun->type info))
                ((unless (type-formalp type)) vartys)
                ((mv & cvar) (ldm-ident ident)) ; ERP is NIL because of FORMALP
                ((mv & ctype) (ldm-type type))) ; ERP is NIL because of FORMALP
             (omap::update cvar ctype vartys))
           :verify-guards :after-returns)))))))

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
       (thm-event
        `(defrule ,thm-name
           ,formula
           :rule-classes nil
           :hints ,hints)))
    (mv thm-event thm-name thm-index))
  ///
  (fty::deffixequiv gen-expr-pure-thm
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

(define gen-expr-asg-thm ((old exprp)
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
  :short "Generate a theorem for the transformation
          of an assignment expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The expressions must be simple assignments
     whose left side is a variable expression @('var')
     (which is not changed by the transformation)
     and whose old and new right sides are pure expressions."))
  (b* ((old (expr-fix old))
       (new (expr-fix new))
       ((unless (expr-asg-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (expr-asg-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       ((unless (and (expr-case old :binary)
                     (binop-case (expr-binary->op old) :asg)))
        (raise "Internal error: ~x0 is not an assignment expression." old)
        (mv '(_) nil 1))
       (old-left (expr-binary->arg1 old))
       ((unless (expr-case old-left :ident))
        (raise "Internal error: ~x0 is not a variable." old-left)
        (mv '(_) nil 1))
       ((unless (and (expr-case new :binary)
                     (binop-case (expr-binary->op new) :asg)))
        (raise "Internal error: ~x0 is not an assignment expression." new)
        (mv '(_) nil 1))
       (new-left (expr-binary->arg1 new))
       ((unless (equal new-left old-left))
        (raise "Internal error: ~x0 and ~x1 differ." old-left new-left)
        (mv '(_) nil 1))
       (vars-pre (gen-var-assertions vartys 'compst))
       (vars-post (gen-var-assertions vartys 'old-compst))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       ((mv & old-expr) (ldm-expr old)) ; ERP is NIL because FORMALP
       ((mv & new-expr) (ldm-expr new)) ; ERP is NIL because FORMALP
       (formula
        `(b* ((old-expr ',old-expr)
              (new-expr ',new-expr)
              ((mv old-result old-compst)
               (c::exec-expr old-expr compst old-fenv limit))
              ((mv new-result new-compst)
               (c::exec-expr new-expr compst new-fenv limit)))
           (implies (and ,@vars-pre
                         (not (c::errorp old-result)))
                    (and (not (c::errorp new-result))
                         (equal old-result new-result)
                         (equal old-compst new-compst)
                         ,@vars-post))))
       (thm-event `(defrule ,thm-name
                     ,formula
                     :rule-classes nil
                     :hints ,hints)))
    (mv thm-event thm-name thm-index))
  ///
  (fty::deffixequiv gen-expr-asg-thm
    :args ((old exprp) (new exprp))))

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
       ((mv & ctypes) (ldm-type-option-set types)) ; ERP is NIL because FORMALP
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
  :short "Equality transformation of identifier expressions (i.e. variables)."
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
     but, importantly, the theorem includes an assertion
     about the type of the variable
     (see @(tsee gen-expr-pure-thm)).")
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
                              (:e c::type-fix))
                 :use (:instance expr-ident-compustate-vars
                                 (var ',cvar)
                                 (type ',ctype)))))
       ((mv thm-event thm-name thm-index)
        (gen-expr-pure-thm expr
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

(define xeq-expr-const ((const constp) (gin ginp))
  :guard (const-annop const)
  :returns (mv (expr exprp) (gout goutp))
  :short "Equality transformation of constants."
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
     but, importantly, the theorem includes an assertion
     about the type of the variable
     (see @(tsee gen-expr-pure-thm)).")
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
       (expr (expr-const const))
       (no-thm-gout (gout-no-thm gin))
       ((unless (const-case const :int)) (mv expr no-thm-gout))
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
        (mv expr no-thm-gout))
       (hints `(("Goal" :in-theory '(c::exec-expr-pure
                                     (:e c::expr-const)
                                     (:e c::expr-fix)
                                     (:e c::expr-kind)
                                     (:e c::expr-const->get)
                                     (:e c::exec-const)
                                     (:e c::expr-value->value)
                                     (:e c::type-of-value)))))
       ((mv thm-event thm-name thm-index)
        (gen-expr-pure-thm expr
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
    :hyp (const-annop const))

  (defret expr-aidentp-of-xeq-expr-const
    (expr-aidentp expr gcc)
    :hyp (const-aidentp const gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xeq-expr-paren ((inner exprp)
                        (inner-new exprp)
                        (inner-thm-name symbolp)
                        (gin ginp))
  :guard (and (expr-unambp inner)
              (expr-annop inner)
              (expr-unambp inner-new)
              (expr-annop inner-new))
  :returns (mv (expr exprp) (gout goutp))
  :short "Equality lifting transformation of parenthesized expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     parenthesizing the possibly transformed inner expression.
     We generate a theorem iff
     a theorem was generated for the inner expression,
     and the inner expression is pure.
     The function @(tsee ldm-expr) maps
     a parenthesized expression to the same as the inner expression.
     Thus, the theorem for the parenthesized expression
     follows directly from the one for the inner expression."))
  (b* ((expr (expr-paren inner))
       (expr-new (expr-paren inner-new))
       ((gin gin) gin)
       ((unless (and inner-thm-name
                     (expr-purep inner)))
        (mv expr-new (gout-no-thm gin)))
       (hints `(("Goal"
                 :in-theory '((:e ldm-expr))
                 :use ,inner-thm-name)))
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

  (defret expr-unambp-of-xeq-expr-paren
    (expr-unambp expr)
    :hyp (expr-unambp inner-new))

  (defret expr-annop-of-xeq-expr-paren
    (expr-annop expr)
    :hyp (expr-annop inner-new))

  (defret expr-aidentp-of-xeq-expr-paren
    (expr-aidentp expr gcc)
    :hyp (expr-aidentp inner-new gcc)))

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
  :short "Equality lifting transformation of unary expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     combining the unary operator with
     the possibly transformed argument expression.")
   (xdoc::p
    "We generate a theorem iff
     a theorem was generated for the argument expression,
     the argument expression is pure,
     and the unary operator is among @('+'), @('-'), @('~') and @('!').
     The theorem is proved via two general ones that we prove below."))
  (b* (((gin gin) gin)
       (expr (make-expr-unary :op op :arg arg :info info))
       (expr-new (make-expr-unary :op op :arg arg-new :info info))
       ((unless (and arg-thm-name
                     (expr-purep arg)
                     (member-eq (unop-kind op)
                                '(:plus :minus :bitnot :lognot))))
        (mv expr-new (gout-no-thm gin)))
       ((mv & old-arg) (ldm-expr arg)) ; ERP must be NIL
       ((mv & new-arg) (ldm-expr arg-new)) ; ERP must be NIL
       (hints `(("Goal"
                 :in-theory '((:e c::unop-nonpointerp)
                              (:e c::unop-kind)
                              (:e c::expr-unary)
                              (:e c::type-kind)
                              (:e c::promote-type)
                              (:e c::type-nonchar-integerp)
                              (:e c::type-sint)
                              (:e member-equal))
                 :use (,arg-thm-name
                       (:instance
                        expr-unary-congruence
                        (op ',(unop-case
                               op
                               :plus (c::unop-plus)
                               :minus (c::unop-minus)
                               :bitnot (c::unop-bitnot)
                               :lognot (c::unop-lognot)
                               :otherwise (impossible)))
                        (old-arg ',old-arg)
                        (new-arg ',new-arg))
                       (:instance
                        expr-unary-errors
                        (op ',(unop-case
                               op
                               :plus (c::unop-plus)
                               :minus (c::unop-minus)
                               :bitnot (c::unop-bitnot)
                               :lognot (c::unop-lognot)
                               :otherwise (impossible)))
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
  :short "Equality lifting transformation of cast expressions."
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
