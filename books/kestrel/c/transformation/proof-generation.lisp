; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

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
     that should be of general use."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define c::compustate-has-var-with-type-p ((var c::identp)
                                           (type c::typep)
                                           (compst c::compustatep))
  :returns (yes/no booleanp)
  :short "Check if a computation state includes
          a variable with a given name
          containing a value of the given type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is essentially an abbreviation,
     which we use in generated theorems.
     In a way this predicate belongs to a more general place,
     perhaps in the language formalization;
     this is why we put it into the @('\"C\"') package."))
  (b* ((objdes (c::objdesign-of-var var compst)))
    (and objdes
         (b* ((val (c::read-object objdes compst)))
           (equal (c::type-of-value val) type))))
  :guard-hints
  (("Goal" :in-theory (enable c::valuep-of-read-object-of-objdesign-of-var)))

  ///

  (defruled c::not-errorp-when-compustate-has-var-with-type-p
    (implies (c::compustate-has-var-with-type-p var type compst)
             (not (c::errorp
                   (c::read-object (c::objdesign-of-var var compst)
                                   compst))))
    :enable (c::valuep-of-read-object-of-objdesign-of-var
             c::not-errorp-when-valuep))

  (defruled c::type-of-value-when-compustate-has-var-with-type-p
    (implies (c::compustate-has-var-with-type-p var type compst)
             (equal (c::type-of-value
                     (c::read-object (c::objdesign-of-var var compst)
                                     compst))
                    type)))

  (defruled c::compustate-has-var-with-type-p-of-create-other-var
    (b* ((compst1 (c::create-var var1 val compst)))
      (implies (and (not (c::errorp compst1))
                    (c::identp var)
                    (c::identp var1)
                    (not (equal var var1))
                    (c::compustate-has-var-with-type-p var type compst))
               (c::compustate-has-var-with-type-p var type compst1)))
    :enable (c::objdesign-of-var-of-create-var
             c::read-object-of-create-var-when-auto-or-static
             c::objdesign-static->name-of-objdesign-of-var
             c::objdesign-auto->name-of-objdesign-of-var))

  (defruled c::compustate-has-var-with-type-p-of-create-same-var
    (b* ((compst1 (c::create-var var val compst)))
      (implies (and (not (c::errorp compst1))
                    (c::identp var)
                    (equal type (c::type-of-value val)))
               (c::compustate-has-var-with-type-p var type compst1)))
    :enable (c::objdesign-of-var-of-create-var
             c::read-object-of-create-var-when-auto-or-static
             nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-var-assertions ((vartys ident-type-mapp) (compst symbolp))
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
  (b* (((when (omap::emptyp (ident-type-map-fix vartys))) nil)
       ((mv var type) (omap::head vartys))
       ((unless (ident-formalp var))
        (raise "Internal error: variable ~x0 cannot be mapped to formal model."
               var))
       ((unless (type-formalp type))
        (raise "Internal error: variable ~x0 has type ~x1, ~
                which cannot be mapped to formal model."
               var type))
       ((mv & cvar) (ldm-ident var)) ; ERP is NIL because IDENT-FORMALP holds
       ((mv & ctype) (ldm-type type)) ; ERP is NIL because TYPE-FORMALP holds
       (asrt `(c::compustate-has-var-with-type-p ',cvar ',ctype ,compst))
       (asrts (gen-var-assertions (omap::tail vartys) compst)))
    (cons asrt asrts))
  ///
  (fty::deffixequiv gen-var-assertions
    :args ((vartys ident-type-mapp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vartys-from-valid-table ((table c$::valid-tablep))
  :returns (vatys ident-type-mapp)
  :short "Generate, from a validation table,
          a map from identifiers to types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The validation table is from validation annotations.
     The resulting map contains all the variables in scope
     whose types satisfy @(tsee type-formalp);
     variables of other types are skipped.
     Given that later scopes may contain variables that shadow earlier scopes,
     we process the scopes in the validation table
     from oldest to newest, overriding map entries as applicable."))
  (vartys-from-valid-scope-list (c$::valid-table->scopes table))

  :prepwork
  ((define vartys-from-valid-scope-list ((scopes
                                          c$::valid-scope-listp))
     :returns (vartys ident-type-mapp :hyp :guard)
     :parents nil
     (cond ((endp scopes) nil)
           (t (omap::update*
               (vartys-from-valid-scope-list (cdr scopes))
               (vartys-from-valid-scope (car scopes)))))
     :verify-guards :after-returns

     :prepwork
     ((define vartys-from-valid-scope ((scope c$::valid-scopep))
        :returns (vartys ident-type-mapp)
        :parents nil
        (vartys-from-valid-ord-scope (c$::valid-scope->ord scope))

        :prepwork
        ((define vartys-from-valid-ord-scope ((oscope
                                               c$::valid-ord-scopep))
           :returns (vartys ident-type-mapp :hyp :guard)
           :parents nil
           (b* (((when (endp oscope)) nil)
                ((cons ident info) (car oscope))
                (vartys (vartys-from-valid-ord-scope (cdr oscope)))
                ((unless (c$::valid-ord-info-case info :objfun)) vartys)
                (type (c$::valid-ord-info-objfun->type info))
                ((unless (type-formalp type)) vartys))
             (omap::update ident type vartys))
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
                           (vartys ident-type-mapp)
                           (const-new symbolp)
                           (thm-index posp)
                           (hints true-listp))
  :guard (and (expr-unambp old)
              (expr-unambp new))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem for the transformation of a pure expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function takes the old and new expressions as inputs,
     which must satisfy @(tsee expr-pure-formalp).")
   (xdoc::p
    "The theorem says that
     if the execution of the old expression does not yield an error,
     neither does the execution of the new expression,
     and that the two executions give the same result;
     the theorem also says that the result has the type of the expressions.")
   (xdoc::p
    "Note that the calls of @(tsee ldm-expr) in the theorem
     are known to succeed (i.e. not return any error),
     given that @(tsee expr-pure-formalp) is checked to hold.")
   (xdoc::p
    "This function also takes as input a map from identifiers to types,
     which are the variables in scope with their types.
     The theorem includes a hypothesis for each of these variables,
     saying that they are in the computation state
     and that they contain values of the appropriate types.")
   (xdoc::p
    "The hints to prove the theorem are passed as input too,
     since the proof varies depending on the kind of expression."))
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
       ((mv & ctype) (ldm-type type)) ; ERP is NIL because TYPE-FORMALP holds
       (formula
        `(b* ((old-expr (mv-nth 1 (ldm-expr ',old)))
              (new-expr (mv-nth 1 (ldm-expr ',new)))
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
                               (vartys ident-type-mapp)
                               (const-new symbolp)
                               (thm-index posp)
                               (hints true-listp))
  :guard (and (initer-unambp old)
              (initer-unambp new)
              (initer-case old :single)
              (initer-case new :single))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem for the transformation of a single initializer."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem says that
     if the execution of the old initializer does not yield an error,
     neither does the execution of the new initializer,
     and that the two executions give the same result;
     the theorem also says that the result has the type of the initializer."))
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
       ((mv & ctype) (ldm-type type)) ; ERP is NIL because TYPE-FORMALP holds
       (formula
        `(b* ((old-initer (mv-nth 1 (ldm-initer ',old)))
              (new-initer (mv-nth 1 (ldm-initer ',new)))
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
                          (vartys ident-type-mapp)
                          (const-new symbolp)
                          (thm-index posp)
                          (hints true-listp))
  :guard (and (expr-unambp old)
              (expr-unambp new))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem for the transformation
          of an assignment expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This only applies to simple assignments
     whose left side is a variable expression @('var')
     (which is not changed by the transformation)
     and whose old and new right sides are pure expressions.
     The caller of this function checks that that is the case;
     here we double-check these conditions,
     and throw a hard error if they are not satisfied,
     because that should never happen.")
   (xdoc::p
    "The theorem says that
     if the execution of the old expression does not yield an error,
     neither does the execution of the new expression,
     and that the two executions give the same results;
     it also says that
     the variables in the computation state (passed as the @('vartys') input)
     are preserved."))
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
       (formula
        `(b* ((old-expr (mv-nth 1 (ldm-expr ',old)))
              (new-expr (mv-nth 1 (ldm-expr ',new)))
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
                      (vartys ident-type-mapp)
                      (const-new symbolp)
                      (thm-index posp)
                      (hints true-listp))
  :guard (and (stmt-unambp old)
              (stmt-unambp new))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem for the transformation of a statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem says that
     if the execution of the old statement does not yield an error,
     neither does the execution of the new statement,
     and that the two executions give the same results.
     The theorem says whether the statement value is a return or not;
     if it is a return with a value,
     the theorem also says what the type of the value is.
     The theorem also says
     which variables in the comuptation state are present after the statement,
     which are the same present before the statement,
     indicated by the @('vartys') input."))
  (b* ((old (stmt-fix old))
       (new (stmt-fix new))
       ((unless (stmt-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (stmt-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       (types (stmt-types old))
       ((unless (= (set::cardinality types) 1))
        (raise "Internal error: non-singleton type set ~x0." types)
        (mv '(_) nil 1))
       ((unless (equal (stmt-types new)
                       types))
        (raise "Internal error: ~
                the types ~x0 of the new statement ~x1 differ from ~
                the types ~x2 of the old statement ~x3."
               (stmt-types new) new types old)
        (mv '(_) nil 1))
       (type (set::head types))
       ((unless (or (not type)
                    (type-formalp type)))
        (raise "Internal error: statement ~x0 has type ~x1." old type)
        (mv '(_) nil 1))
       (ctype (if type
                  (b* (((mv & ctype) ; ERP is NIL because TYPE-FORMALP holds
                        (ldm-type type)))
                    ctype)
                nil))
       (vars-pre (gen-var-assertions vartys 'compst))
       (vars-post (gen-var-assertions vartys 'old-compst))
       (formula
        `(b* ((old-stmt (mv-nth 1 (ldm-stmt ',old)))
              (new-stmt (mv-nth 1 (ldm-stmt ',new)))
              ((mv old-result old-compst)
               (c::exec-stmt old-stmt compst old-fenv limit))
              ((mv new-result new-compst)
               (c::exec-stmt new-stmt compst new-fenv limit)))
           (implies (and ,@vars-pre
                         (not (c::errorp old-result)))
                    (and (not (c::errorp new-result))
                         (equal old-result new-result)
                         (equal old-compst new-compst)
                         ,@(cond
                            ((not type)
                             '((equal (c::stmt-value-kind old-result)
                                      :none)))
                            ((type-case type :void)
                             '((equal (c::stmt-value-kind old-result)
                                      :return)
                               (not (c::stmt-value-return->value?
                                     old-result))))
                            (t
                             `((equal (c::stmt-value-kind old-result)
                                      :return)
                               (c::stmt-value-return->value? old-result)
                               (equal (c::type-of-value
                                       (c::stmt-value-return->value?
                                        old-result))
                                      ',ctype))))
                         ,@vars-post))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event
        `(defrule ,thm-name
           ,formula
           :rule-classes nil
           :hints ,hints)))
    (mv thm-event thm-name thm-index))
  :guard-hints (("Goal" :in-theory (enable set::cardinality)))
  ///
  (fty::deffixequiv gen-stmt-thm
    :args ((old stmtp) (new stmtp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-decl-thm ((old declp)
                      (new declp)
                      (vartys-pre ident-type-mapp)
                      (vartys-post ident-type-mapp)
                      (const-new symbolp)
                      (thm-index posp)
                      (hints true-listp))
  :guard (and (decl-unambp old)
              (decl-unambp new))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem for the transformation of a declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is currently only for declarations of objects in blocks,
     satisfying @(tsee decl-block-formalp).
     The theorem is in terms of @(tsee c::exec-obj-declon)."))
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
       (formula
        `(b* ((old-decl (mv-nth 1 (ldm-decl-obj ',old)))
              (new-decl (mv-nth 1 (ldm-decl-obj ',new)))
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
                            (vartys-pre ident-type-mapp)
                            (vartys-post ident-type-mapp)
                            (const-new symbolp)
                            (thm-index posp)
                            (hints true-listp))
  :guard (and (block-item-unambp old)
              (block-item-unambp new))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem for the transformation of a block item."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee gen-stmt-thm),
     but for block items instead of statements."))
  (b* ((old (block-item-fix old))
       (new (block-item-fix new))
       ((unless (block-item-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (block-item-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       (types (block-item-types old))
       ((unless (= (set::cardinality types) 1))
        (raise "Internal error: non-singleton type set ~x0." types)
        (mv '(_) nil 1))
       ((unless (equal (block-item-types new)
                       types))
        (raise "Internal error: ~
                the types ~x0 of the new block item ~x1 differ from ~
                the types ~x2 of the old block item ~x3."
               (block-item-types new) new types old)
        (mv '(_) nil 1))
       (type (set::head types))
       ((unless (or (not type)
                    (type-formalp type)))
        (raise "Internal error: statement ~x0 has type ~x1." old type)
        (mv '(_) nil 1))
       (ctype (if type
                  (b* (((mv & ctype) ; ERP is NIL because TYPE-FORMALP holds
                        (ldm-type type)))
                    ctype)
                nil))
       (vars-pre (gen-var-assertions vartys-pre 'compst))
       (vars-post (gen-var-assertions vartys-post 'old-compst))
       (formula
        `(b* ((old-item (mv-nth 1 (ldm-block-item ',old)))
              (new-item (mv-nth 1 (ldm-block-item ',new)))
              ((mv old-result old-compst)
               (c::exec-block-item old-item compst old-fenv limit))
              ((mv new-result new-compst)
               (c::exec-block-item new-item compst new-fenv limit)))
           (implies (and ,@vars-pre
                         (not (c::errorp old-result)))
                    (and (not (c::errorp new-result))
                         (equal old-result new-result)
                         (equal old-compst new-compst)
                         ,@(cond
                            ((not type)
                             '((equal (c::stmt-value-kind old-result)
                                      :none)))
                            ((type-case type :void)
                             '((equal (c::stmt-value-kind old-result)
                                      :return)
                               (not (c::stmt-value-return->value?
                                     old-result))))
                            (t
                             `((equal (c::stmt-value-kind old-result)
                                      :return)
                               (c::stmt-value-return->value? old-result)
                               (equal (c::type-of-value
                                       (c::stmt-value-return->value?
                                        old-result))
                                      ',ctype))))
                         ,@vars-post))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event
        `(defrule ,thm-name
           ,formula
           :rule-classes nil
           :hints ,hints)))
    (mv thm-event thm-name thm-index))
  :guard-hints (("Goal" :in-theory (enable set::cardinality)))
  ///
  (fty::deffixequiv gen-block-item-thm
    :args ((old block-itemp) (new block-itemp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gen-block-item-list-thm ((old block-item-listp)
                                 (new block-item-listp)
                                 (vartys-pre ident-type-mapp)
                                 (vartys-post ident-type-mapp)
                                 (const-new symbolp)
                                 (thm-index posp)
                                 (hints true-listp))
  :guard (and (block-item-list-unambp old)
              (block-item-list-unambp new))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp))
  :short "Generate a theorem for the transformation of a list of block items."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee gen-block-item-thm),
     but for lists of block items instead of single block items."))
  (b* ((old (block-item-list-fix old))
       (new (block-item-list-fix new))
       ((unless (block-item-list-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (block-item-list-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       (types (block-item-list-types old))
       ((unless (= (set::cardinality types) 1))
        (raise "Internal error: non-singleton type set ~x0." types)
        (mv '(_) nil 1))
       ((unless (equal (block-item-list-types new)
                       types))
        (raise "Internal error: ~
                the types ~x0 of the new block item list ~x1 differ from ~
                the types ~x2 of the old block item list ~x3."
               (block-item-list-types new) new types old)
        (mv '(_) nil 1))
       (type (set::head types))
       ((unless (or (not type)
                    (type-formalp type)))
        (raise "Internal error: statement ~x0 has type ~x1." old type)
        (mv '(_) nil 1))
       (ctype (if type
                  (b* (((mv & ctype) ; ERP is NIL because TYPE-FORMALP holds
                        (ldm-type type)))
                    ctype)
                nil))
       (vars-pre (gen-var-assertions vartys-pre 'compst))
       (vars-post (gen-var-assertions vartys-post 'old-compst))
       (formula
        `(b* ((old-items (mv-nth 1 (ldm-block-item-list ',old)))
              (new-items (mv-nth 1 (ldm-block-item-list ',new)))
              ((mv old-result old-compst)
               (c::exec-block-item-list old-items compst old-fenv limit))
              ((mv new-result new-compst)
               (c::exec-block-item-list new-items compst new-fenv limit)))
           (implies (and ,@vars-pre
                         (not (c::errorp old-result)))
                    (and (not (c::errorp new-result))
                         (equal old-result new-result)
                         (equal old-compst new-compst)
                         ,@(cond
                            ((not type)
                             '((equal (c::stmt-value-kind old-result)
                                      :none)))
                            ((type-case type :void)
                             '((equal (c::stmt-value-kind old-result)
                                      :return)
                               (not (c::stmt-value-return->value?
                                     old-result))))
                            (t
                             `((equal (c::stmt-value-kind old-result)
                                      :return)
                               (c::stmt-value-return->value? old-result)
                               (equal (c::type-of-value
                                       (c::stmt-value-return->value?
                                        old-result))
                                      ',ctype))))
                         ,@vars-post))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event
        `(defrule ,thm-name
           ,formula
           :rule-classes nil
           :hints ,hints)))
    (mv thm-event thm-name thm-index))
  :guard-hints (("Goal" :in-theory (enable set::cardinality)))
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
