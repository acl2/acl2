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
(include-book "../atc/symbolic-execution-rules/top")

(local (include-book "std/typed-lists/atom-listp" :dir :system))

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
    "The functions to generate theorems for expression, statements, etc.
     take the old and new constructs as inputs,
     which must be in the formalized subset,
     and in some cases must satisfy additional restrictions.
     The callers check these conditions,
     but they are double-checked here,
     throwing hard errors if not satisfied, which should never happen.")
   (xdoc::p
    "The theorems for the various constructs say that:")
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
      (e.g. for declarations).")))
  :order-subtopics t
  :default-parent t)

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
           (implies (and ,@vars-pre
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
              (old-compst (c::exec-expr-asg old-expr compst old-fenv limit))
              (new-compst (c::exec-expr-asg new-expr compst new-fenv limit)))
           (implies (and ,@vars-pre
                         (not (c::errorp old-compst)))
                    (and (not (c::errorp new-compst))
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
           (implies (and ,@vars-pre
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
           (implies (and ,@vars-pre
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
           (implies (and ,@vars-pre
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
       (vars-post (gen-var-assertions vartys 'old-compst))
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
           (implies (and ,@vars-pre
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
  (fty::deffixequiv gen-block-item-list-thm
    :args ((old block-item-listp) (new block-item-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-tyspecseq-to-type ((tyspecseq c::tyspecseqp))
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
