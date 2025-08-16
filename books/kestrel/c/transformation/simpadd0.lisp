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
(include-book "../syntax/unambiguity")
(include-book "../syntax/ascii-identifiers")
(include-book "../syntax/purity")
(include-book "../syntax/validation-information")
(include-book "../syntax/langdef-mapping")
(include-book "../atc/symbolic-execution-rules/top")
(include-book "../representation/shallow-deep-relation")

(include-book "kestrel/fty/pseudo-event-form-list" :dir :system)
(include-book "std/lists/index-of" :dir :system)
(include-book "std/system/constant-value" :dir :system)
(include-book "std/system/pseudo-event-form-listp" :dir :system)

(local (include-book "std/system/w" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (in-theory (enable* c$::abstract-syntax-aidentp-rules)))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 simpadd0

 :items

 ((xdoc::evmac-topic-implementation-item-input "const-old")

  (xdoc::evmac-topic-implementation-item-input "const-new")

  (xdoc::evmac-topic-implementation-item-input "proofs"))

 :additional

 ("This transformation is implemented as a collection of ACL2 functions
   that operate on the abstract syntax,
   following the recursive structure of the abstract syntax.
   This is a typical pattern for C-to-C transformations,
   which we may want to partially automate,
   via things like generalized `folds' over the abstract syntax."

  "These functions also return correctness theorems in a bottom-up fashion,
   for a growing subset of constructs currently supported.
   This is one of a few different or slightly different approaches
   to proof generation, which we are exploring."

  "For a growing number of constructs,
   we have ACL2 functions that do most of the transformation of the construct,
   including theorem generation when applicable,
   and these ACL2 function are outside the large mutual recursion.
   The recursive functions recursively transform the sub-constructs,
   and then call the separate non-recursive functions
   with the results from transforming the sub-constructs.
   A simple example is @(tsee simpadd0-expr-paren),
   which is called by @(tsee simpadd0-expr):
   the caller recursively transforms the inner expression,
   and passes the possibly transformed expression to the callee,
   along with some of the @(tsee simpadd0-gout) components
   resulting from that transformation;
   it also passes a @(tsee simpadd0-gin)
   whose components have been updated
   from the aforementioned @(tsee simpadd0-gout)."

  "The generated theorems involve hypotheses about
   variables in scope having values of appropriate types,
   captured as ACL2 values of type @(tsee ident-type-map).
   Our initial approach has been to take the variables from the constructs,
   joining the ones for sub-constructs via @(tsee simpadd0-join-vartys)
   to obtain the ones for super-constructs.
   This is adequate for some of the constructs,
   but we need to generalize this approach for other constructs.
   Specifically, we are moving towards having
   information about the variables in scope in the AST validation annotations,
   and using that instead of calculating the information from the constructs.
   As we move towards the new approach,
   we may have a mix of the new and old appraoches."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing simpadd0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-process-inputs (const-old const-new (wrld plist-worldp))
  :returns (mv erp
               (code-old code-ensemblep)
               (const-new$ symbolp))
  :short "Process all the inputs."
  (b* (((reterr) (irr-code-ensemble) nil)
       ((unless (symbolp const-old))
        (reterr (msg "The first input must be a symbol, ~
                      but it is ~x0 instead."
                     const-old)))
       ((unless (symbolp const-new))
        (reterr (msg "The second input must be a symbol, ~
                      but it is ~x0 instead."
                     const-new)))
       ((unless (constant-symbolp const-old wrld))
        (reterr (msg "The first input, ~x0, must be a named constant, ~
                      but it is not."
                     const-old)))
       (code-old (constant-value const-old wrld))
       ((unless (code-ensemblep code-old))
        (reterr (msg "The value of the constant ~x0 ~
                      must be a code ensemble, ~
                      but it is ~x1 instead."
                     const-old code-old)))
       ((unless (code-ensemble-unambp code-old))
        (reterr (msg "The code ensemble ~x0 ~
                      that is the value of the constant ~x1 ~
                      must be unambiguous, ~
                      but it is not."
                     code-old const-old)))
       ((unless (code-ensemble-annop code-old))
        (reterr (msg "The code ensemble ~x0 ~
                      that is the value of the constant ~x1 ~
                      must contains validation information, ~
                      but it does not."
                     code-old const-old))))
    (retok code-old const-new))

  ///

  (defret code-ensemble-unambp-of-simpadd0-process-inputs
    (implies (not erp)
             (code-ensemble-unambp code-old)))

  (defret code-ensemble-annop-of-simpadd0-process-inputs
    (implies (not erp)
             (code-ensemble-annop code-old))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation simpadd0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod simpadd0-gin
  :short "General inputs for transformation functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The transformation functions take as input the construct to transform,
     which has a different type for each transformation function.
     But each function also takes certain common inputs,
     which we put into this data structure
     for modularity and to facilitate extension.
     Additionally, the transformation functions take the ACL2 state as input,
     but this is not part of this structure for obvious reasons."))
  ((const-new symbolp
              "The @(':const-new') input of the transformation.")
   (thm-index pos
              "Index used to generate unique theorem names
               that include increasing numeric indices.")
   (names-to-avoid symbol-list
                   "List of event names to avoid,
                    for the generated theorems."))
  :pred simpadd0-ginp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod simpadd0-gout
  :short "General outputs for transformation functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The transformation functions return as output the transformed construct,
     which has a different type for each transformation function.
     But each function also returns certain common outputs,
     which we put into this data structure
     for modularity and to facility extension."))
  ((events pseudo-event-form-list
           "Cumulative list of generated theorems.")
   (thm-name symbol
             "Name of the theorem generated by the transformation function.
              The theorem concerns the transformation of the C construct
              that the transformation function operates on.
              This is @('nil') if no theorem is generated.")
   (thm-index pos
              "Updated numeric index to generate unique theorem names;
               this is updated from
               the homonymous component of @(tsee simpadd0-gin).")
   (names-to-avoid symbol-list
                   "Updated list of event names to avoid;
                    this is updated from
                    the homonymous component of @(tsee simpadd0-gin).")
   (vartys ident-type-map
           "Variables for which the generated theorem (if any)
            has hypotheses about the variables being in the computation state
            and having values of the appropriate types."))
  :pred simpadd0-goutp)

;;;;;;;;;;

(defirrelevant irr-simpadd0-gout
  :short "Irrelevant general outputs for transformation functions."
  :type simpadd0-goutp
  :body (make-simpadd0-gout :events nil
                            :thm-name nil
                            :thm-index 1
                            :names-to-avoid nil
                            :vartys nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gin-update ((gin simpadd0-ginp) (gout simpadd0-goutp))
  :returns (new-gin simpadd0-ginp)
  :short "Update a @(tsee simpadd0-gin) with a @(tsee simpadd0-gout)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Those two data structures include common components,
     whose values are threaded through the transformation functions."))
  (b* (((simpadd0-gout gout) gout))
    (change-simpadd0-gin gin
                         :thm-index gout.thm-index
                         :names-to-avoid gout.names-to-avoid))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
                    type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-var-assertions ((vartys ident-type-mapp) (compst symbolp))
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
       (asrts (simpadd0-gen-var-assertions (omap::tail vartys) compst)))
    (cons asrt asrts))
  ///
  (fty::deffixequiv simpadd0-gen-var-assertions
    :args ((vartys ident-type-mapp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-join-vartys ((vartys1 ident-type-mapp)
                              (vartys2 ident-type-mapp))
  :returns (vartys ident-type-mapp)
  :short "Join two maps from identifiers to types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used on maps that must be compatible,
     so we throw a hard error if that is not the case."))
  (b* ((vartys1 (ident-type-map-fix vartys1))
       (vartys2 (ident-type-map-fix vartys2)))
    (if (omap::compatiblep vartys1 vartys2)
        (omap::update* vartys1 vartys2)
      (raise "Internal error: ~
              incompatible variable-type maps ~x0 and ~x1"
             vartys1 vartys2)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-vartys-from-valid-table ((table c$::valid-tablep))
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
  (simpadd0-vartys-from-valid-scope-list (c$::valid-table->scopes table))

  :prepwork
  ((define simpadd0-vartys-from-valid-scope-list ((scopes
                                                   c$::valid-scope-listp))
     :returns (vartys ident-type-mapp :hyp :guard)
     :parents nil
     (cond ((endp scopes) nil)
           (t (omap::update*
               (simpadd0-vartys-from-valid-scope-list (cdr scopes))
               (simpadd0-vartys-from-valid-scope (car scopes)))))
     :verify-guards :after-returns

     :prepwork
     ((define simpadd0-vartys-from-valid-scope ((scope c$::valid-scopep))
        :returns (vartys ident-type-mapp)
        :parents nil
        (simpadd0-vartys-from-valid-ord-scope (c$::valid-scope->ord scope))

        :prepwork
        ((define simpadd0-vartys-from-valid-ord-scope ((oscope
                                                        c$::valid-ord-scopep))
           :returns (vartys ident-type-mapp :hyp :guard)
           :parents nil
           (b* (((when (endp oscope)) nil)
                ((cons ident info) (car oscope))
                (vartys (simpadd0-vartys-from-valid-ord-scope (cdr oscope)))
                ((unless (c$::valid-ord-info-case info :objfun)) vartys)
                (type (c$::valid-ord-info-objfun->type info))
                ((unless (type-formalp type)) vartys))
             (omap::update ident type vartys))
           :verify-guards :after-returns)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-expr-pure-thm ((old exprp)
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
       (vars-pre (simpadd0-gen-var-assertions vartys 'compst))
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
       (thm-name
        (packn-pos (list const-new '-thm- thm-index) const-new))
       (thm-index (1+ (pos-fix thm-index)))
       (thm-event
        `(defrule ,thm-name
           ,formula
           :rule-classes nil
           :hints ,hints)))
    (mv thm-event thm-name thm-index))
  ///
  (fty::deffixequiv simpadd0-gen-expr-pure-thm
    :args ((old exprp) (new exprp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-expr-asg-thm ((old exprp)
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
       (old-right (expr-binary->arg2 old))
       ((unless (expr-case old-left :ident))
        (raise "Internal error: ~x0 is not a variable." old-left)
        (mv '(_) nil 1))
       ((unless (expr-purep old-right))
        (raise "Internal error: ~x0 is not a pure expression." old-right)
        (mv '(_) nil 1))
       ((unless (and (expr-case new :binary)
                     (binop-case (expr-binary->op new) :asg)))
        (raise "Internal error: ~x0 is not an assignment expression." new)
        (mv '(_) nil 1))
       (new-left (expr-binary->arg1 new))
       (new-right (expr-binary->arg2 new))
       ((unless (equal new-left old-left))
        (raise "Internal error: ~x0 and ~x1 differ." old-left new-left)
        (mv '(_) nil 1))
       ((unless (expr-purep new-right))
        (raise "Internal error: ~x0 is not a pure expression." new-right)
        (mv '(_) nil 1))
       (vars-pre (simpadd0-gen-var-assertions vartys 'compst))
       (vars-post (simpadd0-gen-var-assertions vartys 'old-compst))
       (thm-name
        (packn-pos (list const-new '-thm- thm-index) const-new))
       (thm-index (1+ (pos-fix thm-index)))
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
  (fty::deffixequiv simpadd0-gen-expr-asg-thm
    :args ((old exprp) (new exprp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-stmt-thm ((old stmtp)
                               (new stmtp)
                               (vartys-pre ident-type-mapp)
                               (vartys-post ident-type-mapp)
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
     which are passed as the @('vartys-post') input;
     the @('vartys-pre') input indicates the variables before the statement."))
  (b* ((old (stmt-fix old))
       (new (stmt-fix new))
       ((unless (stmt-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (stmt-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       (type (stmt-type old))
       ((unless (equal (stmt-type new)
                       type))
        (raise "Internal error: ~
                the type ~x0 of the new statement ~x1 differs from ~
                the type ~x2 of the old statement ~x3."
               (stmt-type new) new type old)
        (mv '(_) nil 1))
       ((unless (or (not type)
                    (type-formalp type)))
        (raise "Internal error: statement ~x0 has type ~x1." old type)
        (mv '(_) nil 1))
       (ctype (if type
                  (b* (((mv & ctype) ; ERP is NIL because TYPE-FORMALP holds
                        (ldm-type type)))
                    ctype)
                nil))
       (vars-pre (simpadd0-gen-var-assertions vartys-pre 'compst))
       (vars-post (simpadd0-gen-var-assertions vartys-post 'compst))
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
       (thm-name
        (packn-pos (list const-new '-thm- thm-index) const-new))
       (thm-index (1+ (pos-fix thm-index)))
       (thm-event
        `(defrule ,thm-name
           ,formula
           :rule-classes nil
           :hints ,hints)))
    (mv thm-event thm-name thm-index))
  ///
  (fty::deffixequiv simpadd0-gen-stmt-thm
    :args ((old stmtp) (new stmtp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-block-item-thm ((old block-itemp)
                                     (new block-itemp)
                                     (vartys ident-type-mapp)
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
    "This is analogous to @(tsee simpadd0-gen-stmt-thm),
     but for block items instead of statements."))
  (b* ((old (block-item-fix old))
       (new (block-item-fix new))
       ((unless (block-item-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (block-item-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       (type (block-item-type old))
       ((unless (equal (block-item-type new)
                       type))
        (raise "Internal error: ~
                the type ~x0 of the new block item ~x1 differs from ~
                the type ~x2 of the old block item ~x3."
               (block-item-type new) new type old)
        (mv '(_) nil 1))
       ((unless (or (not type)
                    (type-formalp type)))
        (raise "Internal error: statement ~x0 has type ~x1." old type)
        (mv '(_) nil 1))
       (ctype (if type
                  (b* (((mv & ctype) ; ERP is NIL because TYPE-FORMALP holds
                        (ldm-type type)))
                    ctype)
                nil))
       (vars-pre (simpadd0-gen-var-assertions vartys 'compst))
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
                                      ',ctype))))))))
       (thm-name
        (packn-pos (list const-new '-thm- thm-index) const-new))
       (thm-index (1+ (pos-fix thm-index)))
       (thm-event
        `(defrule ,thm-name
           ,formula
           :rule-classes nil
           :hints ,hints)))
    (mv thm-event thm-name thm-index))
  ///
  (fty::deffixequiv simpadd0-gen-block-item-thm
    :args ((old block-itemp) (new block-itemp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-block-item-list-thm ((old block-item-listp)
                                          (new block-item-listp)
                                          (vartys ident-type-mapp)
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
    "This is analogous to @(tsee simpadd0-gen-block-item-thm),
     but for lists of block items instead of single block items."))
  (b* ((old (block-item-list-fix old))
       (new (block-item-list-fix new))
       ((unless (block-item-list-formalp old))
        (raise "Internal error: ~x0 is not in the formalized subset." old)
        (mv '(_) nil 1))
       ((unless (block-item-list-formalp new))
        (raise "Internal error: ~x0 is not in the formalized subset." new)
        (mv '(_) nil 1))
       (type (block-item-list-type old))
       ((unless (equal (block-item-list-type new)
                       type))
        (raise "Internal error: ~
                the type ~x0 of the new block item list ~x1 differs from ~
                the type ~x2 of the old block item list ~x3."
               (block-item-list-type new) new type old)
        (mv '(_) nil 1))
       ((unless (or (not type)
                    (type-formalp type)))
        (raise "Internal error: statement ~x0 has type ~x1." old type)
        (mv '(_) nil 1))
       (ctype (if type
                  (b* (((mv & ctype) ; ERP is NIL because TYPE-FORMALP holds
                        (ldm-type type)))
                    ctype)
                nil))
       (vars-pre (simpadd0-gen-var-assertions vartys 'compst))
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
                                      ',ctype))))))))
       (thm-name
        (packn-pos (list const-new '-thm- thm-index) const-new))
       (thm-index (1+ (pos-fix thm-index)))
       (thm-event
        `(defrule ,thm-name
           ,formula
           :rule-classes nil
           :hints ,hints)))
    (mv thm-event thm-name thm-index))
  ///
  (fty::deffixequiv simpadd0-gen-block-item-list-thm
    :args ((old block-item-listp) (new block-item-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-from-params ((params c::param-declon-listp)
                                  (gin simpadd0-ginp))
  :returns (mv (okp booleanp)
               (args symbol-listp)
               (parargs "A term.")
               (arg-types true-listp)
               (arg-types-compst true-listp))
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
      and its reading yields a value of the appropriate type."))
   (xdoc::p
    "These results are generated only if
     all the parameters have certain types
     (see @(tsee simpadd0-tyspecseq-to-type)),
     which we check as we go through the parameters.
     The @('okp') result says whether this is the case;
     if it is @('nil'), the other results are @('nil') too."))
  (b* (((when (endp params)) (mv t nil nil nil nil))
       ((c::param-declon param) (car params))
       ((mv okp type) (simpadd0-tyspecseq-to-type param.tyspec))
       ((unless okp) (mv nil nil nil nil nil))
       ((unless (c::obj-declor-case param.declor :ident))
        (mv nil nil nil nil nil))
       (ident (c::obj-declor-ident->get param.declor))
       (par (c::ident->name ident))
       (arg (intern-in-package-of-symbol par (simpadd0-gin->const-new gin)))
       (arg-type `(and (c::valuep ,arg)
                       (equal (c::type-of-value ,arg) ',type)))
       (arg-type-compst
        `(b* ((var (mv-nth 1 (ldm-ident (ident ,par)))))
           (c::compustate-has-var-with-type-p var ',type compst)))
       ((mv okp
            more-args
            parargs
            more-arg-types
            more-arg-types-compst)
        (simpadd0-gen-from-params (cdr params) gin))
       ((unless okp) (mv nil nil nil nil nil))
       (parargs `(omap::update (c::ident ,par) ,arg ,parargs)))
    (mv t
        (cons arg more-args)
        parargs
        (cons arg-type more-arg-types)
        (cons arg-type-compst more-arg-types-compst)))

  ///

  (defret len-of-simpadd0-gen-from-params.arg-types
    (equal (len arg-types)
           (len args))
    :hints (("Goal" :induct t :in-theory (enable len))))

  (defret len-of-simpadd0-gen-from-params.arg-types-compst
    (equal (len arg-types-compst)
           (len args))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-init-scope-thm ((params c::param-declon-listp)
                                     (args symbol-listp)
                                     (parargs "A term.")
                                     (arg-types true-listp))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp))
  :short "Generate a theorem about the initial scope of a function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('args'), @('parargs'), and @('arg-types') inputs
     are the corresponding outputs of @(tsee simpadd0-gen-from-params).")
   (xdoc::p
    "The theorem says that, given values of certain types for the arguments,
     @(tsee c::init-scope) applied to the list of parameter declarations
     and to the list of parameter values
     yields an omap (which we express as an @(tsee omap::update) nest)
     that associates parameter name and argument value.")
   (xdoc::p
    "The name of the theorem is used locally to another theorem,
     so it does not have to be particularly distinguished.
     But we should check and disambiguate this more thoroughly."))
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
       (thm-name 'init-scope-thm)
       (thm-event `(defruled ,thm-name
                     ,formula
                     :hints ,hints
                     :prep-lemmas
                     ((defruled lemma1
                        (not (c::errorp nil)))
                      (defruled lemma2
                        (not (c::errorp (omap::update key val map)))
                        :enable (c::errorp omap::update))))))
    (mv thm-event thm-name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-param-thms ((args symbol-listp)
                                 (arg-types-compst true-listp)
                                 (all-arg-types true-listp)
                                 (all-params c::param-declon-listp)
                                 (all-args symbol-listp))
  :guard (equal (len arg-types-compst) (len args))
  :returns (mv (thm-events pseudo-event-form-listp)
               (thm-names symbol-listp))
  :short "Generate theorems about the parameters of a function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('args') and @('arg-types-compst') inputs are
     the corresponding outputs of @(tsee simpadd0-gen-from-params);
     these are @(tsee cdr)ed in the recursion.
     The @('all-arg-types') input is
     the @('arg-types') output of @(tsee simpadd0-gen-from-params);
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
  (b* (((when (endp args)) (mv nil nil))
       (arg (car args))
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
        '(("Goal" :in-theory '(init-scope-thm
                               (:e ident)
                               (:e ldm-ident)
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
                               simpadd0-param-thm-list-lemma
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
                               (:t len)))))
       (thm-name (packn-pos (list arg '-param-thm) arg))
       (thm-event `(defruled ,thm-name
                     ,formula
                     :hints ,hints))
       ((mv more-thm-events more-thm-names)
        (simpadd0-gen-param-thms (cdr args)
                                 (cdr arg-types-compst)
                                 all-arg-types
                                 all-params
                                 all-args)))
    (mv (cons thm-event more-thm-events)
        (cons thm-name more-thm-names)))
  :guard-hints (("Goal" :in-theory (enable len)))

  ///

  (defret len-of-simpadd-gen-param-thms.thm-names
    (equal (len thm-names)
           (len thm-events))
    :hints (("Goal" :induct t :in-theory (enable len))))

  (defruled simpadd0-param-thm-list-lemma
    (equal (nth (len l) (append (rev l) (list x)))
           x)
    :use (:instance lemma (l (rev l)))
    :prep-lemmas
    ((defruled lemma
       (equal (nth (len l) (append l (list x)))
              x)
       :induct t
       :enable len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-ident ((ident identp)
                             (info var-infop)
                             (gin simpadd0-ginp))
  :returns (mv (expr exprp) (gout simpadd0-goutp))
  :short "Transform an identifier expression (i.e. a variable)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This undergoes no actual transformation,
     but we introduce it for uniformity,
     also because we may eventually evolve the @(tsee simpadd0) implementation
     into a much more general transformation.
     Thus, the output expression consists of
     the identifier and validation information passed as inputs.")
   (xdoc::p
    "If the variable has a type supported in our C formalization,
     which we check in the validation information,
     then we generate a theorem saying that the expression,
     when executed, yields a value of the appropriate type.
     The generated theorem is proved via a general supporting lemma,
     which is proved below."))
  (b* ((ident (ident-fix ident))
       ((var-info info) (var-info-fix info))
       ((simpadd0-gin gin) gin)
       (expr (make-expr-ident :ident ident :info info))
       ((unless (and (type-formalp info.type)
                     (not (type-case info.type :void))
                     (not (type-case info.type :char))))
        (mv expr
            (make-simpadd0-gout :events nil
                                :thm-name nil
                                :thm-index gin.thm-index
                                :names-to-avoid gin.names-to-avoid
                                :vartys nil)))
       (vartys (omap::update ident info.type nil))
       ((unless (type-formalp info.type))
        (raise "Internal error: variable ~x0 has type ~x1." ident info.type)
        (mv (irr-expr) (irr-simpadd0-gout)))
       ((mv & ctype) ; ERP is NIL because TYPE-FORMALP holds
        (ldm-type info.type))
       (hints `(("Goal"
                 :in-theory '((:e expr-ident)
                              (:e expr-pure-formalp)
                              (:e ldm-ident))
                 :use (:instance simpadd0-expr-ident-support-lemma
                                 (ident ',ident)
                                 (info ',info)
                                 (type ',ctype)))))
       ((mv thm-event thm-name thm-index)
        (simpadd0-gen-expr-pure-thm expr
                                    expr
                                    vartys
                                    gin.const-new
                                    gin.thm-index
                                    hints)))
    (mv expr
        (make-simpadd0-gout :events (list thm-event)
                            :thm-name thm-name
                            :thm-index thm-index
                            :names-to-avoid (cons thm-name gin.names-to-avoid)
                            :vartys vartys)))
  :hooks (:fix)

  ///

  (defret expr-unambp-of-simpadd0-expr-ident
    (expr-unambp expr))

  (defret expr-aidentp-of-simpadd0-expr-ident
    (c$::expr-aidentp expr gcc)
    :hyp (c$::ident-aidentp ident gcc))

  (defruled simpadd0-expr-ident-support-lemma
    (b* ((expr (mv-nth 1 (ldm-expr (expr-ident ident info))))
         (result (c::exec-expr-pure expr compst))
         (value (c::expr-value->value result)))
      (implies (and (expr-pure-formalp (expr-ident ident info))
                    (b* ((var (mv-nth 1 (ldm-ident ident))))
                      (c::compustate-has-var-with-type-p var type compst)))
               (equal (c::type-of-value value) type)))
    :enable (c::exec-expr-pure
             c::exec-ident
             ldm-expr
             expr-pure-formalp
             c::compustate-has-var-with-type-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-const ((const constp) (gin simpadd0-ginp))
  :returns (mv (expr exprp) (gout simpadd0-goutp))
  :short "Transform a constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This undergoes no actual transformation,
     but we introduce it for uniformity,
     also because we may eventually evolve the @(tsee simpadd0) implementation
     into a much more general transformation.
     Thus, the output expression consists of the constant passed as input.")
   (xdoc::p
    "If the constant is an integer one,
     and under the additional conditions described shortly,
     we generate a theorem saying that the exprssion,
     when executed, yields a value of the appropriate integer type.
     The additional conditions are that:")
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
    "The reason is that
     our current dynamic semantics assumes that
     those types have those sizes,
     while our validator is more general
     (@(tsee c$::valid-iconst) takes an implementation environment as input,
     which specifies, among other things, the size of those types).
     Until we extend our dynamic semantics to be more general,
     we need this additional condition for proof generation."))
  (b* (((simpadd0-gin gin) gin)
       (expr (expr-const const))
       (no-thm-gout (make-simpadd0-gout :events nil
                                        :thm-name nil
                                        :thm-index gin.thm-index
                                        :names-to-avoid gin.names-to-avoid
                                        :vartys nil))
       ((unless (const-case const :int)) (mv expr no-thm-gout))
       ((iconst iconst) (const-int->unwrap const))
       ((iconst-info info) (coerce-iconst-info iconst.info))
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
       (expr (expr-const const))
       (hints `(("Goal" :in-theory '(c::exec-expr-pure
                                     (:e ldm-expr)
                                     (:e c::expr-const)
                                     (:e c::expr-fix)
                                     (:e c::expr-kind)
                                     (:e c::expr-const->get)
                                     (:e c::exec-const)
                                     (:e c::expr-value->value)
                                     (:e c::type-of-value)))))
       (vartys nil)
       ((mv thm-event thm-name thm-index)
        (simpadd0-gen-expr-pure-thm expr
                                    expr
                                    vartys
                                    gin.const-new
                                    gin.thm-index
                                    hints)))
    (mv expr
        (make-simpadd0-gout :events (list thm-event)
                            :thm-name thm-name
                            :thm-index thm-index
                            :names-to-avoid (cons thm-name gin.names-to-avoid)
                            :vartys vartys)))
  :hooks (:fix)

  ///

  (defret expr-unambp-of-simpadd0-expr-const
    (expr-unambp expr))

  (defret expr-aidentp-of-simpadd0-expr-const
    (c$::expr-aidentp expr gcc)
    :hyp (c$::const-aidentp const gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-paren ((inner exprp)
                             (inner-new exprp)
                             (inner-events pseudo-event-form-listp)
                             (inner-thm-name symbolp)
                             (inner-vartys ident-type-mapp)
                             (gin simpadd0-ginp))
  :guard (and (expr-unambp inner)
              (expr-unambp inner-new))
  :returns (mv (expr exprp) (gout simpadd0-goutp))
  :short "Transform a parenthesized expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     parenthesizing the possibly transformed inner expression.
     We generate a theorem iff
     a theorem was generated for the inner expression,
     which we see from whether the theorem name is @('nil') or not.
     The function @(tsee ldm-expr) maps
     a parenthesized expression to the same as the inner expression.
     Thus, the theorem for the parenthesized expression
     follows directly from the one for the inner expression."))
  (b* ((expr (expr-paren inner))
       (expr-new (expr-paren inner-new))
       ((simpadd0-gin gin) gin)
       ((unless inner-thm-name)
        (mv expr-new
            (make-simpadd0-gout :events inner-events
                                :thm-name nil
                                :thm-index gin.thm-index
                                :names-to-avoid gin.names-to-avoid
                                :vartys inner-vartys)))
       (hints `(("Goal"
                 :in-theory '((:e ldm-expr))
                 :use ,inner-thm-name)))
       ((mv thm-event thm-name thm-index)
        (simpadd0-gen-expr-pure-thm expr
                                    expr-new
                                    inner-vartys
                                    gin.const-new
                                    gin.thm-index
                                    hints)))
    (mv expr-new
        (make-simpadd0-gout :events (append inner-events
                                            (list thm-event))
                            :thm-name thm-name
                            :thm-index thm-index
                            :names-to-avoid (cons thm-name gin.names-to-avoid)
                            :vartys inner-vartys)))

  ///

  (defret expr-unambp-of-simpadd0-expr-paren
    (expr-unambp expr)
    :hyp (expr-unambp inner-new)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-unary ((op unopp)
                             (arg exprp)
                             (arg-new exprp)
                             (arg-events pseudo-event-form-listp)
                             (arg-thm-name symbolp)
                             (arg-vartys ident-type-mapp)
                             (info unary-infop)
                             (gin simpadd0-ginp))
  :guard (and (expr-unambp arg)
              (expr-unambp arg-new))
  :returns (mv (expr exprp) (gout simpadd0-goutp))
  :short "Transform a unary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     combining the unary operator with
     the possibly transformed argument expression.")
   (xdoc::p
    "We generate a theorem iff
     a theorem was generated for the argument expression,
     and the unary operator is among @('+'), @('-'), @('~') and @('!').
     The theorem is proved via two general ones that we prove below."))
  (b* (((simpadd0-gin gin) gin)
       (expr (make-expr-unary :op op :arg arg :info info))
       (expr-new (make-expr-unary :op op :arg arg-new :info info))
       ((unless (and arg-thm-name
                     (member-eq (unop-kind op)
                                '(:plus :minus :bitnot :lognot))))
        (mv expr-new
            (make-simpadd0-gout :events arg-events
                                :thm-name nil
                                :thm-index gin.thm-index
                                :names-to-avoid gin.names-to-avoid
                                :vartys arg-vartys)))
       (hints `(("Goal"
                 :in-theory '((:e ldm-expr)
                              (:e c::unop-nonpointerp)
                              (:e c::unop-kind)
                              (:e c::expr-unary)
                              (:e c::type-kind)
                              (:e c::promote-type)
                              (:e c::type-nonchar-integerp)
                              (:e c::type-sint)
                              (:e member-equal))
                 :use (,arg-thm-name
                       (:instance
                        simpadd0-expr-unary-support-lemma
                        (op ',(unop-case
                               op
                               :plus (c::unop-plus)
                               :minus (c::unop-minus)
                               :bitnot (c::unop-bitnot)
                               :lognot (c::unop-lognot)
                               :otherwise (impossible)))
                        (old-arg (mv-nth 1 (ldm-expr ',arg)))
                        (new-arg (mv-nth 1 (ldm-expr ',arg-new))))
                       (:instance
                        simpadd0-expr-unary-error-support-lemma
                        (op ',(unop-case
                               op
                               :plus (c::unop-plus)
                               :minus (c::unop-minus)
                               :bitnot (c::unop-bitnot)
                               :lognot (c::unop-lognot)
                               :otherwise (impossible)))
                        (arg (mv-nth 1 (ldm-expr ',arg))))))))
       ((mv thm-event thm-name thm-index)
        (simpadd0-gen-expr-pure-thm expr
                                    expr-new
                                    arg-vartys
                                    gin.const-new
                                    gin.thm-index
                                    hints)))
    (mv expr-new
        (make-simpadd0-gout :events (append arg-events
                                            (list thm-event))
                            :thm-name thm-name
                            :thm-index thm-index
                            :names-to-avoid (cons thm-name gin.names-to-avoid)
                            :vartys arg-vartys)))

  ///

  (defret expr-unambp-of-simpadd0-expr-unary
    (expr-unambp expr)
    :hyp (expr-unambp arg-new))

  (defruledl c::lognot-value-lemma
    (implies (and (c::valuep val)
                  (member-equal (c::value-kind val)
                                '(:uchar :schar
                                  :ushort :sshort
                                  :uint :sint
                                  :ulong :slong
                                  :ullong :sllong)))
             (equal (c::value-kind (c::lognot-value val)) :sint))
    :enable (c::lognot-value
             c::lognot-scalar-value
             c::lognot-integer-value
             c::value-scalarp
             c::value-arithmeticp
             c::value-realp
             c::value-integerp
             c::value-signed-integerp
             c::value-unsigned-integerp))

  (defruled simpadd0-expr-unary-support-lemma
    (b* ((old (c::expr-unary op old-arg))
         (new (c::expr-unary op new-arg))
         (old-arg-result (c::exec-expr-pure old-arg compst))
         (new-arg-result (c::exec-expr-pure new-arg compst))
         (old-arg-value (c::expr-value->value old-arg-result))
         (new-arg-value (c::expr-value->value new-arg-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type (c::type-of-value old-arg-value)))
      (implies (and (c::unop-nonpointerp op)
                    (not (c::errorp old-result))
                    (not (c::errorp new-arg-result))
                    (equal old-arg-value new-arg-value)
                    (c::type-nonchar-integerp type))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value)
                           (if (equal (c::unop-kind op) :lognot)
                               (c::type-sint)
                             (c::promote-type type))))))
    :expand ((c::exec-expr-pure (c::expr-unary op old-arg) compst)
             (c::exec-expr-pure (c::expr-unary op new-arg) compst))
    :disable ((:e c::type-sint))
    :enable (c::unop-nonpointerp
             c::exec-unary
             c::eval-unary
             c::apconvert-expr-value-when-not-array
             c::value-arithmeticp
             c::value-realp
             c::value-integerp
             c::value-signed-integerp
             c::value-unsigned-integerp
             c::lognot-value-lemma
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-unary-error-support-lemma
    (implies (c::errorp (c::exec-expr-pure arg compst))
             (c::errorp (c::exec-expr-pure (c::expr-unary op arg) compst)))
    :expand (c::exec-expr-pure (c::expr-unary op arg) compst)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-cast ((type tynamep)
                            (type-new tynamep)
                            (type-events pseudo-event-form-listp)
                            (type-thm-name symbolp)
                            (type-vartys ident-type-mapp)
                            (arg exprp)
                            (arg-new exprp)
                            (arg-events pseudo-event-form-listp)
                            (arg-thm-name symbolp)
                            (arg-vartys ident-type-mapp)
                            (info tyname-infop)
                            (gin simpadd0-ginp))
  :guard (and (tyname-unambp type)
              (tyname-unambp type-new)
              (expr-unambp arg)
              (expr-unambp arg-new))
  :returns (mv (expr exprp) (gout simpadd0-goutp))
  :short "Transform a cast expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     combining the possibly transformed type name with
     the possibly transformed argument expression.")
   (xdoc::p
    "For now, we generate no theorem for the transformation of the type name,
     but we double-check that here.
     We generate a theorem only if we generated one for the argument expression
     and the old and new type names are the same (i.e. no transformation)."))
  (b* (((simpadd0-gin gin) gin)
       (expr (make-expr-cast :type type :arg arg))
       (expr-new (make-expr-cast :type type-new :arg arg-new))
       (type-vartys (ident-type-map-fix type-vartys))
       (arg-vartys (ident-type-map-fix arg-vartys))
       (vartys (simpadd0-join-vartys type-vartys arg-vartys))
       ((when type-thm-name)
        (raise "Internal error: ~
                unexpected type name transformation theorem ~x0."
               type-thm-name)
        (mv (irr-expr) (irr-simpadd0-gout)))
       ((c$::tyname-info info) info)
       ((unless (and arg-thm-name
                     (type-formalp info.type)
                     (not (type-case info.type :void))
                     (not (type-case info.type :char))))
        (mv expr-new
            (make-simpadd0-gout
             :events (append type-events arg-events)
             :thm-name nil
             :thm-index gin.thm-index
             :names-to-avoid gin.names-to-avoid
             :vartys vartys)))
       ((unless (equal type type-new))
        (raise "Internal error: ~
                type names ~x0 and ~x1 differ."
               type type-new)
        (mv (irr-expr) (irr-simpadd0-gout)))
       (hints `(("Goal"
                 :in-theory '((:e ldm-expr)
                              (:e ldm-tyname)
                              (:e c::expr-cast)
                              (:e c::tyname-to-type)
                              (:e c::type-nonchar-integerp))
                 :use (,arg-thm-name
                       (:instance
                        simpadd0-expr-cast-support-lemma
                        (tyname (mv-nth 1 (ldm-tyname ',type)))
                        (old-arg (mv-nth 1 (ldm-expr ',arg)))
                        (new-arg (mv-nth 1 (ldm-expr ',arg-new))))
                       (:instance
                        simpadd0-expr-cast-error-support-lemma
                        (tyname (mv-nth 1 (ldm-tyname ',type)))
                        (arg (mv-nth 1 (ldm-expr ',arg))))))))
       ((mv thm-event thm-name thm-index)
        (simpadd0-gen-expr-pure-thm expr
                                    expr-new
                                    arg-vartys
                                    gin.const-new
                                    gin.thm-index
                                    hints)))
    (mv expr-new
        (make-simpadd0-gout :events (append type-events
                                            arg-events
                                            (list thm-event))
                            :thm-name thm-name
                            :thm-index thm-index
                            :names-to-avoid (cons thm-name gin.names-to-avoid)
                            :vartys vartys)))

  ///

  (defret expr-unambp-of-simpadd0-expr-cast
    (expr-unambp expr)
    :hyp (and (tyname-unambp type-new)
              (expr-unambp arg-new))
    :hints (("Goal" :in-theory (enable irr-expr))))

  (defruled simpadd0-expr-cast-support-lemma
    (b* ((old (c::expr-cast tyname old-arg))
         (new (c::expr-cast tyname new-arg))
         (old-arg-result (c::exec-expr-pure old-arg compst))
         (new-arg-result (c::exec-expr-pure new-arg compst))
         (old-arg-value (c::expr-value->value old-arg-result))
         (new-arg-value (c::expr-value->value new-arg-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type (c::type-of-value old-arg-value))
         (type1 (c::tyname-to-type tyname)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-arg-result))
                    (equal old-arg-value new-arg-value)
                    (c::type-nonchar-integerp type)
                    (c::type-nonchar-integerp type1))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value)
                           type1))))
    :expand ((c::exec-expr-pure (c::expr-cast tyname old-arg) compst)
             (c::exec-expr-pure (c::expr-cast tyname new-arg) compst))
    :enable (c::exec-cast
             c::eval-cast
             c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-cast-error-support-lemma
    (implies (c::errorp (c::exec-expr-pure arg compst))
             (c::errorp (c::exec-expr-pure (c::expr-cast tyname arg) compst)))
    :expand ((c::exec-expr-pure (c::expr-cast tyname arg) compst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-binary ((op binopp)
                              (arg1 exprp)
                              (arg1-new exprp)
                              (arg1-events pseudo-event-form-listp)
                              (arg1-thm-name symbolp)
                              (arg1-vartys ident-type-mapp)
                              (arg2 exprp)
                              (arg2-new exprp)
                              (arg2-events pseudo-event-form-listp)
                              (arg2-thm-name symbolp)
                              (arg2-vartys ident-type-mapp)
                              (info binary-infop)
                              (gin simpadd0-ginp))
  :guard (and (expr-unambp arg1)
              (expr-unambp arg1-new)
              (expr-unambp arg2)
              (expr-unambp arg2-new))
  :returns (mv (expr exprp) (gout simpadd0-goutp))
  :short "Transform a binary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     combining the binary operator with
     the possibly transformed argument expressions,
     unless the binary operator is @('+')
     and the possibly transformed left argument is an @('int') expression
     and the possibly transformed right argument is
     an @('int') octal 0 without leading zeros,
     in which case the resulting expression is just that expression.
     This is the core of this simple transformation.")
   (xdoc::p
    "We generate a theorem only if
     theorems were generated for both argument expressions.
     We generate a theorem for pure strict and non-strict operators.
     We generate a theorem for simple assignment expressions
     whose left side is a variable of integer type
     and whose right side is a pure expression of the same integer type.")
   (xdoc::p
    "For pure (strict and non-strict) operators,
     we use and join the variable-type maps for the two argument expressions.
     For assignment expressions,
     instead we take the map from
     the validation table that annotates the expression.
     This is in general a supermap of the two maps
     (which we double-check here, throwing a hard error if not).
     In upcoming extensions, we will extend the generated theorem
     to say that all the variables in the map are preserved
     by the execution of the assignment expression,
     which is needed to compose proofs for sequential statements."))
  (b* (((simpadd0-gin gin) gin)
       (expr (make-expr-binary :op op :arg1 arg1 :arg2 arg2 :info info))
       (simpp (and (binop-case op :add)
                   (type-case (expr-type arg1-new) :sint)
                   (expr-zerop arg2-new)))
       (expr-new (if simpp
                     (expr-fix arg1-new)
                   (make-expr-binary
                    :op op :arg1 arg1-new :arg2 arg2-new :info info)))
       (arg1-vartys (ident-type-map-fix arg1-vartys))
       (arg2-vartys (ident-type-map-fix arg2-vartys))
       (vartys (simpadd0-join-vartys arg1-vartys arg2-vartys))
       (gout-no-thm
        (make-simpadd0-gout :events (append arg1-events arg2-events)
                            :thm-name nil
                            :thm-index gin.thm-index
                            :names-to-avoid gin.names-to-avoid
                            :vartys vartys))
       ((unless (and arg1-thm-name
                     arg2-thm-name))
        (mv expr-new gout-no-thm)))
    (cond
     ((member-eq (binop-kind op)
                 '(:mul :div :rem :add :sub :shl :shr
                   :lt :gt :le :ge :eq :ne
                   :bitand :bitxor :bitior))
      (b* ((hints `(("Goal"
                     :in-theory '((:e ldm-expr)
                                  (:e c::iconst-length-none)
                                  (:e c::iconst-base-oct)
                                  (:e c::iconst)
                                  (:e c::const-int)
                                  (:e c::expr-const)
                                  (:e c::binop-kind)
                                  (:e c::binop-add)
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
                            simpadd0-expr-binary-pure-strict-support-lemma
                            (op ',(ldm-binop op))
                            (old-arg1 (mv-nth 1 (ldm-expr ',arg1)))
                            (old-arg2 (mv-nth 1 (ldm-expr ',arg2)))
                            (new-arg1 (mv-nth 1 (ldm-expr ',arg1-new)))
                            (new-arg2 (mv-nth 1 (ldm-expr ',arg2-new))))
                           (:instance
                            simpadd0-expr-binary-pure-strict-error-support-lemma
                            (op ',(ldm-binop op))
                            (arg1 (mv-nth 1 (ldm-expr ',arg1)))
                            (arg2 (mv-nth 1 (ldm-expr ',arg2))))
                           ,@(and simpp
                                  `((:instance
                                     simpadd0-expr-binary-simp-support-lemma
                                     (expr (mv-nth 1 (ldm-expr
                                                      ',arg1-new))))))))))
           ((mv thm-event thm-name thm-index)
            (simpadd0-gen-expr-pure-thm expr
                                        expr-new
                                        vartys
                                        gin.const-new
                                        gin.thm-index
                                        hints)))
        (mv expr-new
            (make-simpadd0-gout :events (append arg1-events
                                                arg2-events
                                                (list thm-event))
                                :thm-name thm-name
                                :thm-index thm-index
                                :names-to-avoid (cons thm-name
                                                      gin.names-to-avoid)
                                :vartys vartys))))
     ((member-eq (binop-kind op) '(:logand :logor))
      (b* ((hints
            `(("Goal"
               :in-theory '((:e ldm-expr)
                            (:e ldm-ident)
                            (:e ident)
                            (:e c::expr-binary)
                            (:e c::binop-logand)
                            (:e c::binop-logor)
                            (:e c::type-sint)
                            (:e c::type-nonchar-integerp))
               :use
               (,arg1-thm-name
                ,arg2-thm-name
                (:instance
                 ,(case (binop-kind op)
                    (:logand
                     'simpadd0-expr-binary-logand-first-support-lemma)
                    (:logor
                     'simpadd0-expr-binary-logor-first-support-lemma))
                 (old-arg1 (mv-nth 1 (ldm-expr ',arg1)))
                 (old-arg2 (mv-nth 1 (ldm-expr ',arg2)))
                 (new-arg1 (mv-nth 1 (ldm-expr ',arg1-new)))
                 (new-arg2 (mv-nth 1 (ldm-expr ',arg2-new))))
                (:instance
                 ,(case (binop-kind op)
                    (:logand
                     'simpadd0-expr-binary-logand-second-support-lemma)
                    (:logor
                     'simpadd0-expr-binary-logor-second-support-lemma))
                 (old-arg1 (mv-nth 1 (ldm-expr ',arg1)))
                 (old-arg2 (mv-nth 1 (ldm-expr ',arg2)))
                 (new-arg1 (mv-nth 1 (ldm-expr ',arg1-new)))
                 (new-arg2 (mv-nth 1 (ldm-expr ',arg2-new))))
                (:instance
                 ,(case (binop-kind op)
                    (:logand
                     'simpadd0-expr-binary-logand-first-error-support-lemma)
                    (:logor
                     'simpadd0-expr-binary-logor-first-error-support-lemma))
                 (arg1 (mv-nth 1 (ldm-expr ',arg1)))
                 (arg2 (mv-nth 1 (ldm-expr ',arg2))))
                (:instance
                 ,(case (binop-kind op)
                    (:logand
                     'simpadd0-expr-binary-logand-second-error-support-lemma)
                    (:logor
                     'simpadd0-expr-binary-logor-second-error-support-lemma))
                 (arg1 (mv-nth 1 (ldm-expr ',arg1)))
                 (arg2 (mv-nth 1 (ldm-expr ',arg2))))))))
           ((mv thm-event thm-name thm-index)
            (simpadd0-gen-expr-pure-thm expr
                                        expr-new
                                        vartys
                                        gin.const-new
                                        gin.thm-index
                                        hints)))
        (mv expr-new
            (make-simpadd0-gout :events (append arg1-events
                                                arg2-events
                                                (list thm-event))
                                :thm-name thm-name
                                :thm-index thm-index
                                :names-to-avoid (cons thm-name
                                                      gin.names-to-avoid)
                                :vartys vartys))))
     ((eq (binop-kind op) :asg)
      (b* (((unless (and (expr-case arg1 :ident)
                         (expr-purep arg2)
                         (equal (expr-type arg1)
                                (expr-type arg2))
                         (type-integerp (expr-type arg1))))
            (mv expr-new gout-no-thm))
           (vartys
            (simpadd0-vartys-from-valid-table (c$::binary-info->table info)))
           ((unless (omap::submap arg1-vartys vartys))
            (raise "Internal error: ~
                    argument variables ~x0 are not a submap of ~
                    validation table variables ~x1."
                   arg1-vartys vartys)
            (mv (irr-expr) (irr-simpadd0-gout)))
           ((unless (omap::submap arg2-vartys vartys))
            (raise "Internal error: ~
                    argument variables ~x0 are not a submap of ~
                    validation table variables ~x1."
                   arg2-vartys vartys)
            (mv (irr-expr) (irr-simpadd0-gout)))
           (vartys-lemma-instances
            (simpadd0-expr-asg-lemma-instances
             vartys (expr-ident->ident arg1) arg2))
           (hints
            `(("Goal"
               :in-theory
               '((:e ldm-expr)
                 (:e ldm-ident)
                 (:e ldm-type)
                 (:e ident)
                 (:e c::expr-kind)
                 (:e c::expr-ident)
                 (:e c::expr-binary)
                 (:e c::binop-asg)
                 (:e c::ident)
                 (:e c::type-nonchar-integerp)
                 c::not-errorp-when-compustate-has-var-with-type-p
                 c::type-of-value-when-compustate-has-var-with-type-p
                 c::valuep-of-read-object-of-objdesign-of-var
                 c::not-errorp-when-valuep)
               :use (,arg1-thm-name
                     ,arg2-thm-name
                     (:instance
                      simpadd0-expr-binary-asg-support-lemma
                      (old-arg (mv-nth 1 (ldm-expr ',arg2)))
                      (new-arg (mv-nth 1 (ldm-expr ',arg2-new)))
                      (var (mv-nth 1 (ldm-ident
                                      ',(expr-ident->ident arg1)))))
                     (:instance
                      simpadd0-expr-binary-asg-error-support-lemma
                      (var (mv-nth 1 (ldm-ident
                                      ',(expr-ident->ident arg1))))
                      (expr (mv-nth 1 (ldm-expr ',arg2)))
                      (fenv old-fenv))
                     ,@vartys-lemma-instances))))
           ((mv thm-event thm-name thm-index)
            (simpadd0-gen-expr-asg-thm expr
                                       expr-new
                                       vartys
                                       gin.const-new
                                       gin.thm-index
                                       hints)))
        (mv expr-new
            (make-simpadd0-gout :events (append arg1-events
                                                arg2-events
                                                (list thm-event))
                                :thm-name thm-name
                                :thm-index thm-index
                                :names-to-avoid (cons thm-name
                                                      gin.names-to-avoid)
                                :vartys vartys))))
     (t (mv expr-new gout-no-thm))))

  :prepwork
  ((define simpadd0-expr-asg-lemma-instances ((vartys ident-type-mapp)
                                              (asg-var identp)
                                              (asg-expr exprp))
     :returns (lemma-instances true-listp)
     :parents nil
     (b* (((when (omap::emptyp vartys)) nil)
          ((mv var type) (omap::head vartys))
          (lemma-instance
           `(:instance simpadd0-expr-binary-asg-vartys-support-lemma
                       (var (mv-nth 1 (ldm-ident ',asg-var)))
                       (expr (mv-nth 1 (ldm-expr ',asg-expr)))
                       (fenv old-fenv)
                       (var1 (mv-nth 1 (ldm-ident ',var)))
                       (type (mv-nth 1 (ldm-type ',type)))))
          (lemma-instances
           (simpadd0-expr-asg-lemma-instances (omap::tail vartys)
                                              asg-var
                                              asg-expr)))
       (cons lemma-instance lemma-instances))))

  ///

  (defret expr-unamp-of-simpadd0-expr-binary
    (expr-unambp expr)
    :hyp (and (expr-unambp arg1-new)
              (expr-unambp arg2-new))
    :hints (("Goal" :in-theory (enable irr-expr))))

  (defruled simpadd0-expr-binary-pure-strict-support-lemma
    (b* ((old (c::expr-binary op old-arg1 old-arg2))
         (new (c::expr-binary op new-arg1 new-arg2))
         (old-arg1-result (c::exec-expr-pure old-arg1 compst))
         (old-arg2-result (c::exec-expr-pure old-arg2 compst))
         (new-arg1-result (c::exec-expr-pure new-arg1 compst))
         (new-arg2-result (c::exec-expr-pure new-arg2 compst))
         (old-arg1-value (c::expr-value->value old-arg1-result))
         (old-arg2-value (c::expr-value->value old-arg2-result))
         (new-arg1-value (c::expr-value->value new-arg1-result))
         (new-arg2-value (c::expr-value->value new-arg2-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type1 (c::type-of-value old-arg1-value))
         (type2 (c::type-of-value old-arg2-value)))
      (implies (and (c::binop-purep op)
                    (c::binop-strictp op)
                    (not (c::errorp old-result))
                    (not (c::errorp new-arg1-result))
                    (not (c::errorp new-arg2-result))
                    (equal old-arg1-value new-arg1-value)
                    (equal old-arg2-value new-arg2-value)
                    (c::type-nonchar-integerp type1)
                    (c::type-nonchar-integerp type2))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value)
                           (cond ((member-equal (c::binop-kind op)
                                                '(:mul :div :rem :add :sub
                                                  :bitand :bitxor :bitior))
                                  (c::uaconvert-types type1 type2))
                                 ((member-equal (c::binop-kind op)
                                                '(:shl :shr))
                                  (c::promote-type type1))
                                 (t (c::type-sint)))))))
    :expand ((c::exec-expr-pure (c::expr-binary op old-arg1 old-arg2) compst)
             (c::exec-expr-pure (c::expr-binary op new-arg1 new-arg2) compst))
    :disable ((:e c::type-sint))
    :enable (c::binop-purep
             c::binop-strictp
             c::exec-binary-strict-pure
             c::eval-binary-strict-pure
             c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-binary-pure-strict-error-support-lemma
    (implies (and (c::binop-strictp op)
                  (or (c::errorp (c::exec-expr-pure arg1 compst))
                      (c::errorp (c::exec-expr-pure arg2 compst))))
             (c::errorp
              (c::exec-expr-pure (c::expr-binary op arg1 arg2) compst)))
    :expand (c::exec-expr-pure (c::expr-binary op arg1 arg2) compst)
    :enable c::binop-strictp)

  (defruledl c::add-values-of-sint-and-sint0
    (implies (and (c::valuep val)
                  (c::value-case val :sint)
                  (equal sint0 (c::value-sint 0)))
             (equal (c::add-values val sint0)
                    val))
    :enable (c::add-values
             c::add-arithmetic-values
             c::add-integer-values
             c::value-arithmeticp-when-sintp
             c::value-integerp-when-sintp
             c::uaconvert-values-when-sintp-and-sintp
             c::sintp-alt-def
             c::type-of-value-when-sintp
             c::result-integer-value
             c::integer-type-rangep
             fix
             ifix))

  (defruled simpadd0-expr-binary-simp-support-lemma
    (b* ((zero (c::expr-const
                (c::const-int
                 (c::make-iconst
                  :value 0
                  :base (c::iconst-base-oct)
                  :unsignedp nil
                  :length (c::iconst-length-none)))))
         (expr+zero (c::expr-binary (c::binop-add) expr zero))
         (expr-result (c::exec-expr-pure expr compst))
         (expr-value (c::expr-value->value expr-result))
         (expr+zero-result (c::exec-expr-pure expr+zero compst))
         (expr+zero-value (c::expr-value->value expr+zero-result)))
      (implies (and (not (c::errorp expr-result))
                    (equal (c::type-of-value expr-value) (c::type-sint)))
               (equal expr+zero-value expr-value)))
    :enable (c::exec-expr-pure
             c::exec-binary-strict-pure
             c::eval-binary-strict-pure
             c::apconvert-expr-value-when-not-array
             c::add-values-of-sint-and-sint0
             c::type-of-value))

  (defruled simpadd0-expr-binary-logand-first-support-lemma
    (b* ((old (c::expr-binary (c::binop-logand) old-arg1 old-arg2))
         (new (c::expr-binary (c::binop-logand) new-arg1 new-arg2))
         (old-arg1-result (c::exec-expr-pure old-arg1 compst))
         (new-arg1-result (c::exec-expr-pure new-arg1 compst))
         (old-arg1-value (c::expr-value->value old-arg1-result))
         (new-arg1-value (c::expr-value->value new-arg1-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type1 (c::type-of-value old-arg1-value)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-arg1-result))
                    (equal old-arg1-value new-arg1-value)
                    (c::type-nonchar-integerp type1)
                    (not (c::test-value old-arg1-value)))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value) (c::type-sint)))))
    :expand ((c::exec-expr-pure (c::expr-binary '(:logand) old-arg1 old-arg2)
                                compst)
             (c::exec-expr-pure (c::expr-binary '(:logand) new-arg1 new-arg2)
                                compst))
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-binary-logand-second-support-lemma
    (b* ((old (c::expr-binary (c::binop-logand) old-arg1 old-arg2))
         (new (c::expr-binary (c::binop-logand) new-arg1 new-arg2))
         (old-arg1-result (c::exec-expr-pure old-arg1 compst))
         (old-arg2-result (c::exec-expr-pure old-arg2 compst))
         (new-arg1-result (c::exec-expr-pure new-arg1 compst))
         (new-arg2-result (c::exec-expr-pure new-arg2 compst))
         (old-arg1-value (c::expr-value->value old-arg1-result))
         (old-arg2-value (c::expr-value->value old-arg2-result))
         (new-arg1-value (c::expr-value->value new-arg1-result))
         (new-arg2-value (c::expr-value->value new-arg2-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type1 (c::type-of-value old-arg1-value))
         (type2 (c::type-of-value old-arg2-value)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-arg1-result))
                    (not (c::errorp new-arg2-result))
                    (equal old-arg1-value new-arg1-value)
                    (equal old-arg2-value new-arg2-value)
                    (c::type-nonchar-integerp type1)
                    (c::type-nonchar-integerp type2)
                    (c::test-value old-arg1-value))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value) (c::type-sint)))))
    :expand ((c::exec-expr-pure (c::expr-binary '(:logand) old-arg1 old-arg2)
                                compst)
             (c::exec-expr-pure (c::expr-binary '(:logand) new-arg1 new-arg2)
                                compst))
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-binary-logand-first-error-support-lemma
    (implies (c::errorp (c::exec-expr-pure arg1 compst))
             (c::errorp
              (c::exec-expr-pure (c::expr-binary (c::binop-logand) arg1 arg2)
                                 compst)))
    :expand (c::exec-expr-pure (c::expr-binary '(:logand) arg1 arg2) compst))

  (defruled simpadd0-expr-binary-logand-second-error-support-lemma
    (implies (and (not (c::errorp (c::exec-expr-pure arg1 compst)))
                  (c::type-nonchar-integerp
                   (c::type-of-value
                    (c::expr-value->value (c::exec-expr-pure arg1 compst))))
                  (c::test-value
                   (c::expr-value->value (c::exec-expr-pure arg1 compst)))
                  (c::errorp (c::exec-expr-pure arg2 compst)))
             (c::errorp
              (c::exec-expr-pure (c::expr-binary (c::binop-logand) arg1 arg2)
                                 compst)))
    :expand (c::exec-expr-pure (c::expr-binary '(:logand) arg1 arg2) compst)
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-binary-logor-first-support-lemma
    (b* ((old (c::expr-binary (c::binop-logor) old-arg1 old-arg2))
         (new (c::expr-binary (c::binop-logor) new-arg1 new-arg2))
         (old-arg1-result (c::exec-expr-pure old-arg1 compst))
         (new-arg1-result (c::exec-expr-pure new-arg1 compst))
         (old-arg1-value (c::expr-value->value old-arg1-result))
         (new-arg1-value (c::expr-value->value new-arg1-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type1 (c::type-of-value old-arg1-value)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-arg1-result))
                    (equal old-arg1-value new-arg1-value)
                    (c::type-nonchar-integerp type1)
                    (c::test-value old-arg1-value))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value) (c::type-sint)))))
    :expand ((c::exec-expr-pure (c::expr-binary '(:logor) old-arg1 old-arg2)
                                compst)
             (c::exec-expr-pure (c::expr-binary '(:logor) new-arg1 new-arg2)
                                compst))
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-binary-logor-second-support-lemma
    (b* ((old (c::expr-binary (c::binop-logor) old-arg1 old-arg2))
         (new (c::expr-binary (c::binop-logor) new-arg1 new-arg2))
         (old-arg1-result (c::exec-expr-pure old-arg1 compst))
         (old-arg2-result (c::exec-expr-pure old-arg2 compst))
         (new-arg1-result (c::exec-expr-pure new-arg1 compst))
         (new-arg2-result (c::exec-expr-pure new-arg2 compst))
         (old-arg1-value (c::expr-value->value old-arg1-result))
         (old-arg2-value (c::expr-value->value old-arg2-result))
         (new-arg1-value (c::expr-value->value new-arg1-result))
         (new-arg2-value (c::expr-value->value new-arg2-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type1 (c::type-of-value old-arg1-value))
         (type2 (c::type-of-value old-arg2-value)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-arg1-result))
                    (not (c::errorp new-arg2-result))
                    (equal old-arg1-value new-arg1-value)
                    (equal old-arg2-value new-arg2-value)
                    (c::type-nonchar-integerp type1)
                    (c::type-nonchar-integerp type2)
                    (not (c::test-value old-arg1-value)))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value) (c::type-sint)))))
    :expand ((c::exec-expr-pure (c::expr-binary '(:logor) old-arg1 old-arg2)
                                compst)
             (c::exec-expr-pure (c::expr-binary '(:logor) new-arg1 new-arg2)
                                compst))
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-binary-logor-first-error-support-lemma
    (implies (c::errorp (c::exec-expr-pure arg1 compst))
             (c::errorp
              (c::exec-expr-pure (c::expr-binary (c::binop-logor) arg1 arg2)
                                 compst)))
    :expand (c::exec-expr-pure (c::expr-binary '(:logor) arg1 arg2) compst))

  (defruled simpadd0-expr-binary-logor-second-error-support-lemma
    (implies (and (not (c::errorp (c::exec-expr-pure arg1 compst)))
                  (c::type-nonchar-integerp
                   (c::type-of-value
                    (c::expr-value->value (c::exec-expr-pure arg1 compst))))
                  (not (c::test-value
                        (c::expr-value->value (c::exec-expr-pure arg1 compst))))
                  (c::errorp (c::exec-expr-pure arg2 compst)))
             (c::errorp
              (c::exec-expr-pure (c::expr-binary (c::binop-logor) arg1 arg2)
                                 compst)))
    :expand (c::exec-expr-pure (c::expr-binary '(:logor) arg1 arg2) compst)
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-binary-asg-support-lemma
    (b* ((old (c::expr-binary (c::binop-asg) (c::expr-ident var) old-arg))
         (new (c::expr-binary (c::binop-asg) (c::expr-ident var) new-arg))
         (old-arg-result (c::exec-expr-pure old-arg compst))
         (new-arg-result (c::exec-expr-pure new-arg compst))
         (old-arg-value (c::expr-value->value old-arg-result))
         (new-arg-value (c::expr-value->value new-arg-result))
         (old-compst (c::exec-expr-asg old compst old-fenv limit))
         (new-compst (c::exec-expr-asg new compst new-fenv limit))
         (val (c::read-object (c::objdesign-of-var var compst) compst))
         (type (c::type-of-value val)))
      (implies (and (not (equal (c::expr-kind old-arg) :call))
                    (not (equal (c::expr-kind new-arg) :call))
                    (not (c::errorp val))
                    (c::type-nonchar-integerp type)
                    (not (c::errorp old-compst))
                    (not (c::errorp new-arg-result))
                    (equal old-arg-value new-arg-value)
                    (equal (c::type-of-value old-arg-value) type))
               (and (not (c::errorp new-compst))
                    (equal old-compst new-compst))))
    :expand ((c::exec-expr-asg
              (c::expr-binary '(:asg) (c::expr-ident var) old-arg)
              compst old-fenv limit)
             (c::exec-expr-asg
              (c::expr-binary '(:asg) (c::expr-ident var) new-arg)
              compst new-fenv limit))
    :enable (c::exec-expr-call-or-pure
             c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp)
    :use (:instance
          lemma
          (val1 (c::read-object (c::objdesign-of-var var compst) compst))
          (val2 (c::expr-value->value (c::exec-expr-pure old-arg compst))))
    :prep-lemmas
    ((defruled lemma
       (implies (equal (c::type-of-value val1)
                       (c::type-of-value val2))
                (equal (c::value-integerp val1)
                       (c::value-integerp val2)))
       :enable (c::type-of-value
                c::value-integerp
                c::value-unsigned-integerp
                c::value-signed-integerp))))

  (defruled simpadd0-expr-binary-asg-error-support-lemma
    (implies (and (not (equal (c::expr-kind expr) :call))
                  (or (c::errorp (c::exec-expr-pure (c::expr-ident var) compst))
                      (c::errorp (c::exec-expr-pure expr compst))))
             (c::errorp
              (c::exec-expr-asg (c::expr-binary (c::binop-asg)
                                                (c::expr-ident var)
                                                expr)
                                compst fenv limit)))
    :expand (c::exec-expr-asg (c::expr-binary '(:asg) (c::expr-ident var) expr)
                              compst fenv limit)
    :enable c::exec-expr-call-or-pure)

  (defruled simpadd0-expr-binary-asg-vartys-support-lemma
    (implies (not (equal (c::expr-kind expr) :call))
             (b* ((asg (c::expr-binary (c::binop-asg) (c::expr-ident var) expr))
                  (compst1 (c::exec-expr-asg asg compst fenv limit)))
               (implies (and (not (c::errorp compst1))
                             (equal (c::type-of-value
                                     (c::read-object
                                      (c::objdesign-of-var var compst)
                                      compst))
                                    (c::type-of-value
                                     (c::expr-value->value
                                      (c::exec-expr-pure expr compst))))
                             (c::type-nonchar-integerp
                              (c::type-of-value
                               (c::expr-value->value
                                (c::exec-expr-pure expr compst))))
                             (c::compustate-has-var-with-type-p var1 type compst))
                        (c::compustate-has-var-with-type-p var1 type compst1))))
    :expand (c::exec-expr-asg (c::expr-binary '(:asg) (c::expr-ident var) expr)
                              compst fenv limit)
    :enable (c::compustate-has-var-with-type-p
             c::exec-expr-call-or-pure
             c::exec-expr-pure
             c::exec-ident
             c::objdesign-of-var-of-write-object
             c::read-object-of-write-object-when-auto-or-static
             c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-cond ((test exprp)
                            (test-new exprp)
                            (test-events pseudo-event-form-listp)
                            (test-thm-name symbolp)
                            (test-vartys ident-type-mapp)
                            (then expr-optionp)
                            (then-new expr-optionp)
                            (then-events pseudo-event-form-listp)
                            (then-thm-name symbolp)
                            (then-vartys ident-type-mapp)
                            (else exprp)
                            (else-new exprp)
                            (else-events pseudo-event-form-listp)
                            (else-thm-name symbolp)
                            (else-vartys ident-type-mapp)
                            (gin simpadd0-ginp))
  :guard (and (expr-unambp test)
              (expr-unambp test-new)
              (expr-option-unambp then)
              (expr-option-unambp then-new)
              (expr-unambp else)
              (expr-unambp else-new))
  :returns (mv (expr exprp) (gou simpadd0-goutp))
  :short "Transform a conditional expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     combining the possibly transformed argument expression.")
   (xdoc::p
    "We generate a theorem iff
     a theorem was generated for the argument expressions.
     The theorem is proved via a few general ones that we prove below.
     These are a bit more complicated than for strict expressions,
     because conditional expressions are non-strict:
     the branch not taken could return an error
     while the conditional expression does not."))
  (b* (((simpadd0-gin gin) gin)
       (expr (make-expr-cond :test test :then then :else else))
       (expr-new (make-expr-cond :test test-new :then then-new :else else-new))
       (test-vartys (ident-type-map-fix test-vartys))
       (then-vartys (ident-type-map-fix then-vartys))
       (else-vartys (ident-type-map-fix else-vartys))
       (vartys (simpadd0-join-vartys then-vartys else-vartys))
       (vartys (simpadd0-join-vartys test-vartys vartys))
       ((unless (and test-thm-name
                     then-thm-name
                     else-thm-name))
        (mv expr-new
            (make-simpadd0-gout
             :events (append test-events
                             then-events
                             else-events)
             :thm-name nil
             :thm-index gin.thm-index
             :names-to-avoid gin.names-to-avoid
             :vartys vartys)))
       (hints `(("Goal"
                 :in-theory '((:e ldm-expr)
                              (:e ldm-ident)
                              (:e ident)
                              (:e c::expr-cond)
                              (:e c::type-nonchar-integerp))
                 :use (,test-thm-name
                       ,then-thm-name
                       ,else-thm-name
                       (:instance
                        simpadd0-expr-cond-true-support-lemma
                        (old-test (mv-nth 1 (ldm-expr ',test)))
                        (old-then (mv-nth 1 (ldm-expr ',then)))
                        (old-else (mv-nth 1 (ldm-expr ',else)))
                        (new-test (mv-nth 1 (ldm-expr ',test-new)))
                        (new-then (mv-nth 1 (ldm-expr ',then-new)))
                        (new-else (mv-nth 1 (ldm-expr ',else-new))))
                       (:instance
                        simpadd0-expr-cond-false-support-lemma
                        (old-test (mv-nth 1 (ldm-expr ',test)))
                        (old-then (mv-nth 1 (ldm-expr ',then)))
                        (old-else (mv-nth 1 (ldm-expr ',else)))
                        (new-test (mv-nth 1 (ldm-expr ',test-new)))
                        (new-then (mv-nth 1 (ldm-expr ',then-new)))
                        (new-else (mv-nth 1 (ldm-expr ',else-new))))
                       (:instance
                        simpadd0-expr-cond-test-error-support-lemma
                        (test (mv-nth 1 (ldm-expr ',test)))
                        (then (mv-nth 1 (ldm-expr ',then)))
                        (else (mv-nth 1 (ldm-expr ',else))))
                       (:instance
                        simpadd0-expr-cond-then-error-support-lemma
                        (test (mv-nth 1 (ldm-expr ',test)))
                        (then (mv-nth 1 (ldm-expr ',then)))
                        (else (mv-nth 1 (ldm-expr ',else))))
                       (:instance
                        simpadd0-expr-cond-else-error-support-lemma
                        (test (mv-nth 1 (ldm-expr ',test)))
                        (then (mv-nth 1 (ldm-expr ',then)))
                        (else (mv-nth 1 (ldm-expr ',else))))))))
       ((mv thm-event thm-name thm-index)
        (simpadd0-gen-expr-pure-thm expr
                                    expr-new
                                    vartys
                                    gin.const-new
                                    gin.thm-index
                                    hints)))
    (mv expr-new
        (make-simpadd0-gout :events (append test-events
                                            then-events
                                            else-events
                                            (list thm-event))
                            :thm-name thm-name
                            :thm-index thm-index
                            :names-to-avoid (cons thm-name gin.names-to-avoid)
                            :vartys vartys)))

  ///

  (defret expr-unambp-of-simpadd0-expr-cond
    (expr-unambp expr)
    :hyp (and (expr-unambp test-new)
              (expr-option-unambp then-new)
              (expr-unambp else-new))
    :hints (("Goal" :in-theory (enable irr-expr))))

  (defruled simpadd0-expr-cond-true-support-lemma
    (b* ((old (c::expr-cond old-test old-then old-else))
         (new (c::expr-cond new-test new-then new-else))
         (old-test-result (c::exec-expr-pure old-test compst))
         (old-then-result (c::exec-expr-pure old-then compst))
         (new-test-result (c::exec-expr-pure new-test compst))
         (new-then-result (c::exec-expr-pure new-then compst))
         (old-test-value (c::expr-value->value old-test-result))
         (old-then-value (c::expr-value->value old-then-result))
         (new-test-value (c::expr-value->value new-test-result))
         (new-then-value (c::expr-value->value new-then-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type-test (c::type-of-value old-test-value))
         (type-then (c::type-of-value old-then-value)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-test-result))
                    (not (c::errorp new-then-result))
                    (equal old-test-value new-test-value)
                    (equal old-then-value new-then-value)
                    (c::type-nonchar-integerp type-test)
                    (c::type-nonchar-integerp type-then)
                    (c::test-value old-test-value))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value) type-then))))
    :expand ((c::exec-expr-pure (c::expr-cond old-test old-then old-else)
                                compst)
             (c::exec-expr-pure (c::expr-cond new-test new-then new-else)
                                compst))
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-cond-false-support-lemma
    (b* ((old (c::expr-cond old-test old-then old-else))
         (new (c::expr-cond new-test new-then new-else))
         (old-test-result (c::exec-expr-pure old-test compst))
         (old-else-result (c::exec-expr-pure old-else compst))
         (new-test-result (c::exec-expr-pure new-test compst))
         (new-else-result (c::exec-expr-pure new-else compst))
         (old-test-value (c::expr-value->value old-test-result))
         (old-else-value (c::expr-value->value old-else-result))
         (new-test-value (c::expr-value->value new-test-result))
         (new-else-value (c::expr-value->value new-else-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type-test (c::type-of-value old-test-value))
         (type-else (c::type-of-value old-else-value)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-test-result))
                    (not (c::errorp new-else-result))
                    (equal old-test-value new-test-value)
                    (equal old-else-value new-else-value)
                    (c::type-nonchar-integerp type-test)
                    (c::type-nonchar-integerp type-else)
                    (not (c::test-value old-test-value)))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value) type-else))))
    :expand ((c::exec-expr-pure (c::expr-cond old-test old-then old-else)
                                compst)
             (c::exec-expr-pure (c::expr-cond new-test new-then new-else)
                                compst))
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-cond-test-error-support-lemma
    (implies (c::errorp (c::exec-expr-pure test compst))
             (c::errorp
              (c::exec-expr-pure (c::expr-cond test then else) compst)))
    :expand (c::exec-expr-pure (c::expr-cond test then else) compst))

  (defruled simpadd0-expr-cond-then-error-support-lemma
    (implies (and (not (c::errorp (c::exec-expr-pure test compst)))
                  (c::type-nonchar-integerp
                   (c::type-of-value
                    (c::expr-value->value (c::exec-expr-pure test compst))))
                  (c::test-value
                   (c::expr-value->value (c::exec-expr-pure test compst)))
                  (c::errorp (c::exec-expr-pure then compst)))
             (c::errorp
              (c::exec-expr-pure (c::expr-cond test then else) compst)))
    :expand (c::exec-expr-pure (c::expr-cond test then else) compst)
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-cond-else-error-support-lemma
    (implies (and (not (c::errorp (c::exec-expr-pure test compst)))
                  (c::type-nonchar-integerp
                   (c::type-of-value
                    (c::expr-value->value (c::exec-expr-pure test compst))))
                  (not (c::test-value
                        (c::expr-value->value (c::exec-expr-pure test compst))))
                  (c::errorp (c::exec-expr-pure else compst)))
             (c::errorp
              (c::exec-expr-pure (c::expr-cond test then else) compst)))
    :expand (c::exec-expr-pure (c::expr-cond test then else) compst)
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-stmt-expr ((expr? expr-optionp)
                            (expr?-new expr-optionp)
                            (expr?-events pseudo-event-form-listp)
                            (expr?-thm-name symbolp)
                            (expr?-vartys ident-type-mapp)
                            (gin simpadd0-ginp))
  :guard (and (expr-option-unambp expr?)
              (expr-option-unambp expr?-new)
              (iff expr? expr?-new))
  :returns (mv (stmt stmtp) (gout simpadd0-goutp))
  :short "Transform an expression statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put the optional expression into an expression statement.")
   (xdoc::p
    "We generate a theorem
     if there is no expression (i.e. the null statement),
     or if there is an assignment expression
     for which a theorem was generated."))
  (b* (((simpadd0-gin gin) gin)
       (stmt (stmt-expr expr?))
       (stmt-new (stmt-expr expr?-new))
       ((unless (iff expr? expr?-new))
        (raise "Internal error: ~
                return statement with optional expression ~x0 ~
                is transformed into ~
                return statement with optional expression ~x1."
               expr? expr?-new)
        (mv (irr-stmt) (irr-simpadd0-gout)))
       ((unless (or (not expr?)
                    (and expr?-thm-name
                         (not (expr-purep expr?)))))
        (mv stmt-new
            (make-simpadd0-gout
             :events expr?-events
             :thm-name nil
             :thm-index gin.thm-index
             :names-to-avoid gin.names-to-avoid
             :vartys expr?-vartys)))
       (hints
        (if expr?
            `(("Goal"
               :in-theory '((:e ldm-stmt)
                            (:e ldm-expr)
                            (:e ident)
                            (:e c::expr-kind)
                            (:e c::stmt-expr))
               :use ((:instance
                      ,expr?-thm-name
                      (limit (- limit 2)))
                     (:instance
                      simpadd0-stmt-expr-asg-support-lemma
                      (old-expr (mv-nth 1 (ldm-expr ',expr?)))
                      (new-expr (mv-nth 1 (ldm-expr ',expr?-new))))
                     (:instance
                      simpadd0-stmt-expr-asg-error-support-lemma
                      (expr (mv-nth 1 (ldm-expr ',expr?)))
                      (fenv old-fenv)))))
          `(("Goal"
             :in-theory '((:e ldm-stmt)
                          (:e c::stmt-null))
             :use simpadd0-stmt-null-support-lemma))))
       ((mv thm-event thm-name thm-index)
        (simpadd0-gen-stmt-thm stmt
                               stmt-new
                               expr?-vartys
                               nil ; no thms about post variables yet
                               gin.const-new
                               gin.thm-index
                               hints)))
    (mv stmt-new
        (make-simpadd0-gout :events (append expr?-events
                                            (list thm-event))
                            :thm-name thm-name
                            :thm-index thm-index
                            :names-to-avoid (cons thm-name gin.names-to-avoid)
                            :vartys expr?-vartys)))

  ///

  (defret stmt-unambp-of-simpadd0-stmt-expr
    (stmt-unambp stmt)
    :hyp (expr-option-unambp expr?-new)
    :hints (("Goal" :in-theory (enable irr-stmt))))

  (defruled simpadd0-stmt-null-support-lemma
    (b* ((old (c::stmt-null))
         (new (c::stmt-null))
         ((mv old-result old-compst) (c::exec-stmt old compst old-fenv limit))
         ((mv new-result new-compst) (c::exec-stmt new compst new-fenv limit)))
      (implies (not (c::errorp old-result))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :none))))
    :enable c::exec-stmt)

  (defruled simpadd0-stmt-expr-asg-support-lemma
    (b* ((old (c::stmt-expr old-expr))
         (new (c::stmt-expr new-expr))
         (old-expr-compst (c::exec-expr-asg
                           old-expr compst old-fenv (- limit 2)))
         (new-expr-compst (c::exec-expr-asg
                           new-expr compst new-fenv (- limit 2)))
         ((mv old-result old-compst) (c::exec-stmt old compst old-fenv limit))
         ((mv new-result new-compst) (c::exec-stmt new compst new-fenv limit)))
      (implies (and (not (equal (c::expr-kind old-expr) :call))
                    (not (equal (c::expr-kind new-expr) :call))
                    (not (c::errorp old-result))
                    (not (c::errorp new-expr-compst))
                    (equal old-expr-compst new-expr-compst))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :none))))
    :expand ((c::exec-stmt (c::stmt-expr old-expr) compst old-fenv limit)
             (c::exec-stmt (c::stmt-expr new-expr) compst new-fenv limit))
    :enable (c::exec-expr-call-or-asg))

  (defruled simpadd0-stmt-expr-asg-error-support-lemma
    (implies (and (not (equal (c::expr-kind expr) :call))
                  (c::errorp (c::exec-expr-asg expr compst fenv (- limit 2))))
             (c::errorp
              (mv-nth 0 (c::exec-stmt (c::stmt-expr expr) compst fenv limit))))
    :expand (c::exec-stmt (c::stmt-expr expr) compst fenv limit)
    :enable c::exec-expr-call-or-asg))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-stmt-return ((expr? expr-optionp)
                              (expr?-new expr-optionp)
                              (expr?-events pseudo-event-form-listp)
                              (expr?-thm-name symbolp)
                              (expr?-vartys ident-type-mapp)
                              (gin simpadd0-ginp))
  :guard (and (expr-option-unambp expr?)
              (expr-option-unambp expr?-new)
              (iff expr? expr?-new))
  :returns (mv (stmt stmtp) (gout simpadd0-goutp))
  :short "Transform a return statement."
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
     old and new statements cannot differ.
     If the expression is present,
     the theorem is proved via two general ones proved below;
     if the expression is absent,
     the theorem is proved via another general one proved below."))
  (b* (((simpadd0-gin gin) gin)
       (stmt (stmt-return expr?))
       (stmt-new (stmt-return expr?-new))
       ((unless (iff expr? expr?-new))
        (raise "Internal error: ~
                return statement with optional expression ~x0 ~
                is transformed into ~
                return statement with optional expression ~x1."
               expr? expr?-new)
        (mv (irr-stmt) (irr-simpadd0-gout)))
       ((unless (or (not expr?)
                    expr?-thm-name))
        (mv stmt-new
            (make-simpadd0-gout
             :events expr?-events
             :thm-name nil
             :thm-index gin.thm-index
             :names-to-avoid gin.names-to-avoid
             :vartys expr?-vartys)))
       (hints (if expr?
                  `(("Goal"
                     :in-theory '((:e ldm-stmt)
                                  (:e ldm-expr)
                                  (:e ldm-ident)
                                  (:e ident)
                                  (:e c::expr-kind)
                                  (:e c::stmt-return)
                                  (:e c::type-nonchar-integerp))
                     :use (,expr?-thm-name
                           (:instance
                            simpadd0-stmt-return-value-support-lemma
                            (old-expr (mv-nth 1 (ldm-expr ',expr?)))
                            (new-expr (mv-nth 1 (ldm-expr ',expr?-new))))
                           (:instance
                            simpadd0-stmt-return-error-support-lemma
                            (expr (mv-nth 1 (ldm-expr ',expr?)))
                            (fenv old-fenv)))))
                '(("Goal"
                   :in-theory '((:e ldm-stmt)
                                (:e c::stmt-return))
                   :use simpadd0-stmt-return-novalue-support-lemma))))
       ((mv thm-event thm-name thm-index)
        (simpadd0-gen-stmt-thm stmt
                               stmt-new
                               expr?-vartys
                               nil ; no thms about post variables yet
                               gin.const-new
                               gin.thm-index
                               hints)))
    (mv stmt-new
        (make-simpadd0-gout :events (append expr?-events
                                            (list thm-event))
                            :thm-name thm-name
                            :thm-index thm-index
                            :names-to-avoid (cons thm-name gin.names-to-avoid)
                            :vartys expr?-vartys)))

  ///

  (defret stmt-unambp-of-simpadd0-stmt-return
    (stmt-unambp stmt)
    :hyp (expr-option-unambp expr?-new)
    :hints (("Goal" :in-theory (enable irr-stmt))))

  (defruled simpadd0-stmt-return-value-support-lemma
    (b* ((old (c::stmt-return old-expr))
         (new (c::stmt-return new-expr))
         (old-expr-result (c::exec-expr-pure old-expr compst))
         (new-expr-result (c::exec-expr-pure new-expr compst))
         (old-expr-value (c::expr-value->value old-expr-result))
         (new-expr-value (c::expr-value->value new-expr-result))
         ((mv old-result old-compst) (c::exec-stmt old compst old-fenv limit))
         ((mv new-result new-compst) (c::exec-stmt new compst new-fenv limit))
         (type (c::type-of-value old-expr-value)))
      (implies (and old-expr
                    new-expr
                    (not (equal (c::expr-kind old-expr) :call))
                    (not (equal (c::expr-kind new-expr) :call))
                    (not (c::errorp old-result))
                    (not (c::errorp new-expr-result))
                    (equal old-expr-value new-expr-value)
                    (c::type-nonchar-integerp type))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    (c::stmt-value-return->value? old-result)
                    (equal (c::type-of-value
                            (c::stmt-value-return->value? old-result))
                           type))))
    :expand ((c::exec-stmt (c::stmt-return old-expr) compst old-fenv limit)
             (c::exec-stmt (c::stmt-return new-expr) compst new-fenv limit))
    :enable (c::exec-expr-call-or-pure
             c::type-of-value
             c::apconvert-expr-value-when-not-array
             c::type-nonchar-integerp))

  (defruled simpadd0-stmt-return-novalue-support-lemma
    (b* ((old (c::stmt-return nil))
         (new (c::stmt-return nil))
         ((mv old-result old-compst) (c::exec-stmt old compst old-fenv limit))
         ((mv new-result new-compst) (c::exec-stmt new compst new-fenv limit)))
      (implies (not (c::errorp old-result))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    (not (c::stmt-value-return->value? old-result)))))
    :enable c::exec-stmt)

  (defruled simpadd0-stmt-return-error-support-lemma
    (implies (and expr
                  (not (equal (c::expr-kind expr) :call))
                  (c::errorp (c::exec-expr-pure expr compst)))
             (c::errorp
              (mv-nth 0 (c::exec-stmt (c::stmt-return expr)
                                      compst
                                      fenv
                                      limit))))
    :expand (c::exec-stmt (c::stmt-return expr) compst fenv limit)
    :enable c::exec-expr-call-or-pure))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-block-item-stmt ((stmt stmtp)
                                  (stmt-new stmtp)
                                  (stmt-events pseudo-event-form-listp)
                                  (stmt-thm-name symbolp)
                                  (stmt-vartys ident-type-mapp)
                                  (gin simpadd0-ginp))
  :guard (and (stmt-unambp stmt)
              (stmt-unambp stmt-new))
  :returns (mv (item block-itemp) (gout simpadd0-goutp))
  :short "Transform a block item that consists of a statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put the new statement into a block item.")
   (xdoc::p
    "We generate a theorem iff
     a theorem was generated for the statement.
     That theorem is used to prove the theorem for the block item,
     along with using three general theorems proved below.
     Note that the limit in the theorem for the statement
     must be shifted by one,
     since @(tsee c::exec-block-item) decreases the limit by 1
     before calling @(tsee c::exec-stmt)."))
  (b* (((simpadd0-gin gin) gin)
       (item (block-item-stmt stmt))
       (item-new (block-item-stmt stmt-new))
       ((unless stmt-thm-name)
        (mv item-new
            (make-simpadd0-gout :events stmt-events
                                :thm-name nil
                                :thm-index gin.thm-index
                                :names-to-avoid gin.names-to-avoid
                                :vartys stmt-vartys)))
       (type (stmt-type stmt))
       (support-lemma
        (cond ((not type)
               'simpadd0-block-item-stmt-none-support-lemma)
              ((type-case type :void)
               'simpadd0-block-item-stmt-novalue-support-lemma)
              (t 'simpadd0-block-item-stmt-value-support-lemma)))
       (hints `(("Goal"
                 :in-theory '((:e ldm-block-item)
                              (:e ldm-stmt)
                              (:e ldm-ident)
                              (:e ident)
                              (:e c::block-item-stmt)
                              (:e c::type-nonchar-integerp))
                 :use ((:instance ,stmt-thm-name (limit (1- limit)))
                       (:instance
                        ,support-lemma
                        (old-stmt (mv-nth 1 (ldm-stmt ',stmt)))
                        (new-stmt (mv-nth 1 (ldm-stmt ',stmt-new))))
                       (:instance
                        simpadd0-block-item-stmt-error-support-lemma
                        (stmt (mv-nth 1 (ldm-stmt ',stmt)))
                        (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (simpadd0-gen-block-item-thm item
                                     item-new
                                     stmt-vartys
                                     gin.const-new
                                     gin.thm-index
                                     hints)))
    (mv item-new
        (make-simpadd0-gout :events (append stmt-events
                                            (list thm-event))
                            :thm-name thm-name
                            :thm-index thm-index
                            :names-to-avoid (cons thm-name gin.names-to-avoid)
                            :vartys stmt-vartys)))

  ///

  (defret block-item-unambp-of-simpadd0-block-item-stmt
    (block-item-unambp item)
    :hyp (stmt-unambp stmt-new))

  (defruled simpadd0-block-item-stmt-value-support-lemma
    (b* ((old (c::block-item-stmt old-stmt))
         (new (c::block-item-stmt new-stmt))
         ((mv old-stmt-result old-stmt-compst)
          (c::exec-stmt old-stmt compst old-fenv (1- limit)))
         ((mv new-stmt-result new-stmt-compst)
          (c::exec-stmt new-stmt compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item new compst new-fenv limit))
         (type (c::type-of-value
                (c::stmt-value-return->value? old-stmt-result))))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-stmt-result))
                    (equal old-stmt-result new-stmt-result)
                    (equal old-stmt-compst new-stmt-compst)
                    (equal (c::stmt-value-kind old-stmt-result) :return)
                    (c::stmt-value-return->value? old-stmt-result)
                    (c::type-nonchar-integerp type))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    (c::stmt-value-return->value? old-result)
                    (equal (c::type-of-value
                            (c::stmt-value-return->value? old-result))
                           type))))
    :expand
    ((c::exec-block-item (c::block-item-stmt old-stmt) compst old-fenv limit)
     (c::exec-block-item (c::block-item-stmt new-stmt) compst new-fenv limit)))

  (defruled simpadd0-block-item-stmt-novalue-support-lemma
    (b* ((old (c::block-item-stmt old-stmt))
         (new (c::block-item-stmt new-stmt))
         ((mv old-stmt-result old-stmt-compst)
          (c::exec-stmt old-stmt compst old-fenv (1- limit)))
         ((mv new-stmt-result new-stmt-compst)
          (c::exec-stmt new-stmt compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item new compst new-fenv limit)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-stmt-result))
                    (equal old-stmt-result new-stmt-result)
                    (equal old-stmt-compst new-stmt-compst)
                    (equal (c::stmt-value-kind old-stmt-result) :return)
                    (not (c::stmt-value-return->value? old-stmt-result)))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    (not (c::stmt-value-return->value? old-result)))))
    :expand
    ((c::exec-block-item (c::block-item-stmt old-stmt) compst old-fenv limit)
     (c::exec-block-item (c::block-item-stmt new-stmt) compst new-fenv limit)))

  (defruled simpadd0-block-item-stmt-none-support-lemma
    (b* ((old (c::block-item-stmt old-stmt))
         (new (c::block-item-stmt new-stmt))
         ((mv old-stmt-result old-stmt-compst)
          (c::exec-stmt old-stmt compst old-fenv (1- limit)))
         ((mv new-stmt-result new-stmt-compst)
          (c::exec-stmt new-stmt compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item new compst new-fenv limit)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-stmt-result))
                    (equal old-stmt-result new-stmt-result)
                    (equal old-stmt-compst new-stmt-compst)
                    (equal (c::stmt-value-kind old-stmt-result) :none))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :none))))
    :expand
    ((c::exec-block-item (c::block-item-stmt old-stmt) compst old-fenv limit)
     (c::exec-block-item (c::block-item-stmt new-stmt) compst new-fenv limit)))

  (defruled simpadd0-block-item-stmt-error-support-lemma
    (implies (c::errorp (mv-nth 0 (c::exec-stmt stmt compst fenv (1- limit))))
             (c::errorp
              (mv-nth 0 (c::exec-block-item
                         (c::block-item-stmt stmt) compst fenv limit))))
    :expand (c::exec-block-item (c::block-item-stmt stmt) compst fenv limit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-block-item-list-empty ((gin simpadd0-ginp))
  :returns (gout simpadd0-goutp)
  :short "Transform an empty list of block items."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is introduced mainly for uniformity.
     It actually takes and returns no block item list,
     because there is only one empty block item list."))
  (b* (((simpadd0-gin gin) gin)
       (items nil)
       (hints '(("Goal"
                 :in-theory '((:e ldm-block-item-list))
                 :use simpadd0-block-item-list-empty-support-lemma)))
       (vartys nil)
       ((mv thm-event thm-name thm-index)
        (simpadd0-gen-block-item-list-thm items
                                          items
                                          vartys
                                          gin.const-new
                                          gin.thm-index
                                          hints)))
    (make-simpadd0-gout :events (list thm-event)
                        :thm-name thm-name
                        :thm-index thm-index
                        :names-to-avoid (cons thm-name gin.names-to-avoid)
                        :vartys vartys))
  :hooks (:fix)

  ///

  (defruled simpadd0-block-item-list-empty-support-lemma
    (b* ((old nil)
         (new nil)
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit)))
      (implies (not (c::errorp old-result))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :none))))
    :enable c::exec-block-item-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-block-item-list-cons ((item block-itemp)
                                       (item-new block-itemp)
                                       (item-events pseudo-event-form-listp)
                                       (item-thm-name symbolp)
                                       (item-vartys ident-type-mapp)
                                       (items block-item-listp)
                                       (items-new block-item-listp)
                                       (items-events pseudo-event-form-listp)
                                       (items-thm-name symbolp)
                                       (items-vartys ident-type-mapp)
                                       (gin simpadd0-ginp))
  :guard (and (block-item-unambp item)
              (block-item-unambp item-new)
              (block-item-list-unambp items)
              (block-item-list-unambp items-new))
  :returns (mv (item+items block-item-listp) (gout simpadd0-goutp))
  :short "Transform a non-empty list of block items."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting list of block items is obtained by
     @(tsee cons)ing the possibly transformed first item
     and the possibly transformed rest of the items.")
   (xdoc::p
    "We generate a theorem iff theorems were generated for
     both the first item and (the list of) the rest of the items."))
  (b* (((simpadd0-gin gin) gin)
       (item (block-item-fix item))
       (items (block-item-list-fix items))
       (item-new (block-item-fix item-new))
       (items-new (block-item-list-fix items-new))
       (item+items (cons item items))
       (item+items-new (cons item-new items-new))
       (item-vartys (ident-type-map-fix item-vartys))
       (items-vartys (ident-type-map-fix items-vartys))
       (vartys (simpadd0-join-vartys item-vartys items-vartys))
       (gout-no-thm
        (make-simpadd0-gout :events (append item-events items-events)
                            :thm-name nil
                            :thm-index gin.thm-index
                            :names-to-avoid gin.names-to-avoid
                            :vartys vartys))
       ((unless (and item-thm-name
                     items-thm-name
                     nil)) ; temporary
        (mv item+items-new gout-no-thm))
       (first-type (block-item-type item))
       (rest-type (block-item-list-type items))
       (support-lemma
        (cond
         ((not first-type)
          (cond
           ((not rest-type)
            'simpadd0-block-item-list-cons-rest-none-support-lemma)
           ((type-case rest-type :void)
            'simpadd0-block-item-list-cons-rest-novalue-support-lemma)
           (t 'simpadd0-block-item-list-cons-rest-value-support-lemma)))
         ((type-case first-type :void)
          'simpadd0-block-item-list-cons-first-novalue-support-lemma)
         (t 'simpadd0-block-item-list-cons-first-value-support-lemma)))
       (hints
        `(("Goal"
           :in-theory '((:e ldm-block-item)
                        (:e ldm-block-item-list)
                        (:e ldm-ident)
                        (:e ident)
                        (:e c::type-nonchar-integerp))
           :use ((:instance
                  ,item-thm-name
                  (limit (1- limit)))
                 (:instance
                  ,items-thm-name
                  (compst
                   (mv-nth 1 (c::exec-block-item
                              (mv-nth 1 (ldm-block-item ',item))
                              compst old-fenv (1- limit))))
                  (limit (1- limit)))
                 (:instance
                  ,support-lemma
                  (old-item (mv-nth 1 (ldm-block-item ',item)))
                  (old-items (mv-nth 1 (ldm-block-item-list ',items)))
                  (new-item (mv-nth 1 (ldm-block-item ',item-new)))
                  (new-items (mv-nth 1 (ldm-block-item-list ',items-new))))
                 (:instance
                  simpadd0-block-item-list-cons-first-error-support-lemma
                  (item (mv-nth 1 (ldm-block-item ',item)))
                  (items (mv-nth 1 (ldm-block-item-list ',items)))
                  (fenv old-fenv))
                 (:instance
                  simpadd0-block-item-list-cons-rest-error-support-lemma
                  (item (mv-nth 1 (ldm-block-item ',item)))
                  (items (mv-nth 1 (ldm-block-item-list ',items)))
                  (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (simpadd0-gen-block-item-list-thm item+items
                                          item+items-new
                                          vartys
                                          gin.const-new
                                          gin.thm-index
                                          hints)))
    (mv item+items-new
        (make-simpadd0-gout :events (append item-events
                                            items-events
                                            (list thm-event))
                            :thm-name thm-name
                            :thm-index thm-index
                            :names-to-avoid (cons thm-name gin.names-to-avoid)
                            :vartys vartys)))

  ///

  (fty::deffixequiv simpadd0-block-item-list-cons
    :args ((item block-itemp)
           (item-new block-itemp)
           (items block-item-listp)
           (items-new block-item-listp)))

  (defret block-item-list-unambp-of-simpadd0-block-item-list-cons
    (block-item-list-unambp item+items)
    :hyp (and (block-item-unambp item-new)
              (block-item-list-unambp items-new)))

  (defruled simpadd0-block-item-list-cons-first-value-support-lemma
    (b* ((old (cons old-item old-items))
         (new (cons new-item new-items))
         ((mv old-item-result old-item-compst)
          (c::exec-block-item old-item compst old-fenv (1- limit)))
         ((mv new-item-result new-item-compst)
          (c::exec-block-item new-item compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit))
         (val-item (c::stmt-value-return->value? old-item-result))
         (val (c::stmt-value-return->value? old-result))
         (type (c::type-of-value val-item)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-item-result))
                    (equal old-item-result new-item-result)
                    (equal old-item-compst new-item-compst)
                    (equal (c::stmt-value-kind old-item-result) :return)
                    val-item
                    (c::type-nonchar-integerp type))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    val
                    (equal (c::type-of-value val) type))))
    :expand ((c::exec-block-item-list
              (cons old-item old-items) compst old-fenv limit)
             (c::exec-block-item-list
              (cons new-item new-items) compst new-fenv limit)))

  (defruled simpadd0-block-item-list-cons-first-novalue-support-lemma
    (b* ((old (cons old-item old-items))
         (new (cons new-item new-items))
         ((mv old-item-result old-item-compst)
          (c::exec-block-item old-item compst old-fenv (1- limit)))
         ((mv new-item-result new-item-compst)
          (c::exec-block-item new-item compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit))
         (val-item (c::stmt-value-return->value? old-item-result))
         (val (c::stmt-value-return->value? old-result)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-item-result))
                    (equal old-item-result new-item-result)
                    (equal old-item-compst new-item-compst)
                    (equal (c::stmt-value-kind old-item-result) :return)
                    (not val-item))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    (not val))))
    :expand ((c::exec-block-item-list
              (cons old-item old-items) compst old-fenv limit)
             (c::exec-block-item-list
              (cons new-item new-items) compst new-fenv limit)))

  (defruled simpadd0-block-item-list-cons-rest-value-support-lemma
    (b* ((old (cons old-item old-items))
         (new (cons new-item new-items))
         ((mv old-item-result old-item-compst)
          (c::exec-block-item old-item compst old-fenv (1- limit)))
         ((mv new-item-result new-item-compst)
          (c::exec-block-item new-item compst new-fenv (1- limit)))
         ((mv old-items-result old-items-compst)
          (c::exec-block-item-list
           old-items old-item-compst old-fenv (1- limit)))
         ((mv new-items-result new-items-compst)
          (c::exec-block-item-list
           new-items new-item-compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit))
         (val-items (c::stmt-value-return->value? old-items-result))
         (val (c::stmt-value-return->value? old-result))
         (type (c::type-of-value val-items)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-item-result))
                    (not (c::errorp new-items-result))
                    (equal old-item-result new-item-result)
                    (equal old-items-result new-items-result)
                    (equal old-item-compst new-item-compst)
                    (equal old-items-compst new-items-compst)
                    (equal (c::stmt-value-kind old-item-result) :none)
                    (equal (c::stmt-value-kind old-items-result) :return)
                    val-items
                    (c::type-nonchar-integerp type))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    val
                    (equal (c::type-of-value val) type))))
    :expand ((c::exec-block-item-list
              (cons old-item old-items) compst old-fenv limit)
             (c::exec-block-item-list
              (cons new-item new-items) compst new-fenv limit)))

  (defruled simpadd0-block-item-list-cons-rest-novalue-support-lemma
    (b* ((old (cons old-item old-items))
         (new (cons new-item new-items))
         ((mv old-item-result old-item-compst)
          (c::exec-block-item old-item compst old-fenv (1- limit)))
         ((mv new-item-result new-item-compst)
          (c::exec-block-item new-item compst new-fenv (1- limit)))
         ((mv old-items-result old-items-compst)
          (c::exec-block-item-list old-items old-item-compst old-fenv (1- limit)))
         ((mv new-items-result new-items-compst)
          (c::exec-block-item-list new-items new-item-compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit))
         (val-items (c::stmt-value-return->value? old-items-result))
         (val (c::stmt-value-return->value? old-result)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-item-result))
                    (not (c::errorp new-items-result))
                    (equal old-item-result new-item-result)
                    (equal old-items-result new-items-result)
                    (equal old-item-compst new-item-compst)
                    (equal old-items-compst new-items-compst)
                    (equal (c::stmt-value-kind old-item-result) :none)
                    (equal (c::stmt-value-kind old-items-result) :return)
                    (not val-items))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    (not val))))
    :expand ((c::exec-block-item-list
              (cons old-item old-items) compst old-fenv limit)
             (c::exec-block-item-list
              (cons new-item new-items) compst new-fenv limit)))

  (defruled simpadd0-block-item-list-cons-rest-none-support-lemma
    (b* ((old (cons old-item old-items))
         (new (cons new-item new-items))
         ((mv old-item-result old-item-compst)
          (c::exec-block-item old-item compst old-fenv (1- limit)))
         ((mv new-item-result new-item-compst)
          (c::exec-block-item new-item compst new-fenv (1- limit)))
         ((mv old-items-result old-items-compst)
          (c::exec-block-item-list
           old-items old-item-compst old-fenv (1- limit)))
         ((mv new-items-result new-items-compst)
          (c::exec-block-item-list
           new-items new-item-compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-item-result))
                    (not (c::errorp new-items-result))
                    (equal old-item-result new-item-result)
                    (equal old-items-result new-items-result)
                    (equal old-item-compst new-item-compst)
                    (equal old-items-compst new-items-compst)
                    (equal (c::stmt-value-kind old-item-result) :none)
                    (equal (c::stmt-value-kind old-items-result) :none))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :none))))
    :expand ((c::exec-block-item-list
              (cons old-item old-items) compst old-fenv limit)
             (c::exec-block-item-list
              (cons new-item new-items) compst new-fenv limit)))

  (defruled simpadd0-block-item-list-cons-first-error-support-lemma
    (implies (c::errorp
              (mv-nth 0 (c::exec-block-item item compst fenv (1- limit))))
             (c::errorp
              (mv-nth 0 (c::exec-block-item-list
                         (cons item items) compst fenv limit))))
    :expand (c::exec-block-item-list (cons item items) compst fenv limit))

  (defruled simpadd0-block-item-list-cons-rest-error-support-lemma
    (b* (((mv result compst1) (c::exec-block-item item compst fenv (1- limit))))
      (implies (and (not (c::errorp result))
                    (equal (c::stmt-value-kind result) :none)
                    (c::errorp (mv-nth 0 (c::exec-block-item-list
                                          items compst1 fenv (1- limit)))))
               (c::errorp
                (mv-nth 0 (c::exec-block-item-list
                           (cons item items) compst fenv limit)))))
    :expand (c::exec-block-item-list (cons item items) compst fenv limit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-block-item-list-one ((item block-itemp)
                                      (item-new block-itemp)
                                      (item-events pseudo-event-form-listp)
                                      (item-thm-name symbolp)
                                      (item-vartys ident-type-mapp)
                                      (gin simpadd0-ginp))
  :guard (and (block-item-unambp item)
              (block-item-unambp item-new))
  :returns (mv (items block-item-listp) (gout simpadd0-goutp))
  :short "Transform a singleton list of block items."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a theorem iff
     a theorem was generated for the block item.
     That theorem is used to prove the theorem for the block item,
     along with using two general theorems proved below.
     Note that the limit in the theorem for the block item
     must be shifted by one,
     since @(tsee c::exec-block-item-list) decreases the limit by 1
     before calling @(tsee c::exec-block-item)."))
  (b* (((simpadd0-gin gin) gin)
       (items (list (block-item-fix item)))
       (items-new (list (block-item-fix item-new)))
       ((unless item-thm-name)
        (mv items-new
            (make-simpadd0-gout :events item-events
                                :thm-name nil
                                :thm-index gin.thm-index
                                :names-to-avoid gin.names-to-avoid
                                :vartys item-vartys)))
       (type (block-item-type item))
       (support-lemma
        (cond ((not type)
               'simpadd0-block-item-list-none-support-lemma)
              ((type-case type :void)
               'simpadd0-block-item-list-novalue-support-lemma)
              (t 'simpadd0-block-item-list-value-support-lemma)))
       (hints `(("Goal"
                 :in-theory '((:e ldm-block-item-list)
                              (:e ldm-block-item)
                              (:e ldm-ident)
                              (:e ident)
                              (:e c::type-nonchar-integerp))
                 :use ((:instance ,item-thm-name (limit (1- limit)))
                       (:instance
                        ,support-lemma
                        (old-item (mv-nth 1 (ldm-block-item ',item)))
                        (new-item (mv-nth 1 (ldm-block-item ',item-new))))
                       (:instance
                        simpadd0-block-item-list-error-support-lemma
                        (item (mv-nth 1 (ldm-block-item ',item)))
                        (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (simpadd0-gen-block-item-list-thm items
                                          items-new
                                          item-vartys
                                          gin.const-new
                                          gin.thm-index
                                          hints)))
    (mv items-new
        (make-simpadd0-gout :events (append item-events
                                            (list thm-event))
                            :thm-name thm-name
                            :thm-index thm-index
                            :names-to-avoid (cons thm-name gin.names-to-avoid)
                            :vartys item-vartys)))

  ///

  (defret block-item-list-unambp-of-simpadd0-block-item-list-one
    (block-item-list-unambp items)
    :hyp (block-item-unambp item-new))

  (defruled simpadd0-block-item-list-value-support-lemma
    (b* ((old (list old-item))
         (new (list new-item))
         ((mv old-item-result old-item-compst)
          (c::exec-block-item old-item compst old-fenv (1- limit)))
         ((mv new-item-result new-item-compst)
          (c::exec-block-item new-item compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit))
         (type (c::type-of-value
                (c::stmt-value-return->value? old-item-result))))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-item-result))
                    (equal old-item-result new-item-result)
                    (equal old-item-compst new-item-compst)
                    (equal (c::stmt-value-kind old-item-result) :return)
                    (c::stmt-value-return->value? old-item-result)
                    (c::type-nonchar-integerp type))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    (c::stmt-value-return->value? old-result)
                    (equal (c::type-of-value
                            (c::stmt-value-return->value? old-result))
                           type))))
    :expand ((c::exec-block-item-list (list old-item) compst old-fenv limit)
             (c::exec-block-item-list (list new-item) compst new-fenv limit))
    :enable (c::exec-block-item-list
             c::value-optionp-when-value-option-resultp-and-not-errorp))

  (defruled simpadd0-block-item-list-novalue-support-lemma
    (b* ((old (list old-item))
         (new (list new-item))
         ((mv old-item-result old-item-compst)
          (c::exec-block-item old-item compst old-fenv (1- limit)))
         ((mv new-item-result new-item-compst)
          (c::exec-block-item new-item compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-item-result))
                    (equal old-item-result new-item-result)
                    (equal old-item-compst new-item-compst)
                    (equal (c::stmt-value-kind old-item-result) :return)
                    (not (c::stmt-value-return->value? old-item-result)))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    (not (c::stmt-value-return->value? old-result)))))
    :expand ((c::exec-block-item-list (list old-item) compst old-fenv limit)
             (c::exec-block-item-list (list new-item) compst new-fenv limit))
    :enable c::exec-block-item-list)

  (defruled simpadd0-block-item-list-none-support-lemma
    (b* ((old (list old-item))
         (new (list new-item))
         ((mv old-item-result old-item-compst)
          (c::exec-block-item old-item compst old-fenv (1- limit)))
         ((mv new-item-result new-item-compst)
          (c::exec-block-item new-item compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-item-result))
                    (equal old-item-result new-item-result)
                    (equal old-item-compst new-item-compst)
                    (equal (c::stmt-value-kind old-item-result) :none))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :none))))
    :expand ((c::exec-block-item-list (list old-item) compst old-fenv limit)
             (c::exec-block-item-list (list new-item) compst new-fenv limit))
    :enable c::exec-block-item-list)

  (defruled simpadd0-block-item-list-error-support-lemma
    (implies (c::errorp
              (mv-nth 0 (c::exec-block-item item compst fenv (1- limit))))
             (c::errorp
              (mv-nth 0 (c::exec-block-item-list
                         (list item) compst fenv limit))))
    :expand (c::exec-block-item-list (list item) compst fenv limit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines simpadd0-exprs/decls/stmts
  :short "Transform expressions, declarations, statements,
          and related entities."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only generate theorems for certain kinds of expressions.
     We are in the process of extending the implementation to generate theorems
     for additional kinds of expressions and for other constructs."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr ((expr exprp) (gin simpadd0-ginp) state)
    :guard (expr-unambp expr)
    :returns (mv (new-expr exprp) (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an expression."
    (b* (((simpadd0-gin gin) gin))
      (expr-case
       expr
       :ident (simpadd0-expr-ident expr.ident
                                   (coerce-var-info expr.info)
                                   gin)
       :const (simpadd0-expr-const expr.const gin)
       :string (mv (expr-fix expr)
                   (make-simpadd0-gout :events nil
                                       :thm-name nil
                                       :thm-index gin.thm-index
                                       :names-to-avoid gin.names-to-avoid
                                       :vartys nil))
       :paren
       (b* (((mv new-inner (simpadd0-gout gout-inner))
             (simpadd0-expr expr.inner gin state))
            (gin (simpadd0-gin-update gin gout-inner)))
         (simpadd0-expr-paren expr.inner
                              new-inner
                              gout-inner.events
                              gout-inner.thm-name
                              gout-inner.vartys
                              gin))
       :gensel
       (b* (((mv new-control (simpadd0-gout gout-control))
             (simpadd0-expr expr.control gin state))
            (gin (simpadd0-gin-update gin gout-control))
            ((mv new-assocs (simpadd0-gout gout-assocs))
             (simpadd0-genassoc-list expr.assocs gin state)))
         (mv (make-expr-gensel :control new-control
                               :assocs new-assocs)
             (make-simpadd0-gout
              :events (append gout-control.events gout-assocs.events)
              :thm-name nil
              :thm-index gout-assocs.thm-index
              :names-to-avoid gout-assocs.names-to-avoid
              :vartys (omap::update* gout-control.vartys gout-assocs.vartys))))
       :arrsub
       (b* (((mv new-arg1 (simpadd0-gout gout-arg1))
             (simpadd0-expr expr.arg1 gin state))
            (gin (simpadd0-gin-update gin gout-arg1))
            ((mv new-arg2 (simpadd0-gout gout-arg2))
             (simpadd0-expr expr.arg2 gin state))
            (new-expr (make-expr-arrsub :arg1 new-arg1
                                        :arg2 new-arg2)))
         (mv new-expr
             (make-simpadd0-gout
              :events (append gout-arg1.events gout-arg2.events)
              :thm-name nil
              :thm-index gout-arg2.thm-index
              :names-to-avoid gout-arg2.names-to-avoid
              :vartys (omap::update* gout-arg1.vartys gout-arg2.vartys))))
       :funcall
       (b* (((mv new-fun (simpadd0-gout gout-fun))
             (simpadd0-expr expr.fun gin state))
            (gin (simpadd0-gin-update gin gout-fun))
            ((mv new-args (simpadd0-gout gout-args))
             (simpadd0-expr-list expr.args gin state)))
         (mv (make-expr-funcall :fun new-fun
                                :args new-args)
             (make-simpadd0-gout
              :events (append gout-fun.events gout-args.events)
              :thm-name nil
              :thm-index gout-args.thm-index
              :names-to-avoid gout-args.names-to-avoid
              :vartys (omap::update* gout-fun.vartys gout-args.vartys))))
       :member
       (b* (((mv new-arg (simpadd0-gout gout-arg))
             (simpadd0-expr expr.arg gin state)))
         (mv (make-expr-member :arg new-arg
                               :name expr.name)
             (make-simpadd0-gout
              :events gout-arg.events
              :thm-name nil
              :thm-index gout-arg.thm-index
              :names-to-avoid gout-arg.names-to-avoid
              :vartys gout-arg.vartys)))
       :memberp
       (b* (((mv new-arg (simpadd0-gout gout-arg))
             (simpadd0-expr expr.arg gin state)))
         (mv (make-expr-memberp :arg new-arg
                                :name expr.name)
             (make-simpadd0-gout
              :events gout-arg.events
              :thm-name nil
              :thm-index gout-arg.thm-index
              :names-to-avoid gout-arg.names-to-avoid
              :vartys gout-arg.vartys)))
       :complit
       (b* (((mv new-type (simpadd0-gout gout-type))
             (simpadd0-tyname expr.type gin state))
            (gin (simpadd0-gin-update gin gout-type))
            ((mv new-elems (simpadd0-gout gout-elems))
             (simpadd0-desiniter-list expr.elems gin state)))
         (mv (make-expr-complit :type new-type
                                :elems new-elems
                                :final-comma expr.final-comma)
             (make-simpadd0-gout
              :events (append gout-type.events gout-elems.events)
              :thm-name nil
              :thm-index gout-elems.thm-index
              :names-to-avoid gout-elems.names-to-avoid
              :vartys (omap::update* gout-type.vartys gout-elems.vartys))))
       :unary
       (b* (((mv new-arg (simpadd0-gout gout-arg))
             (simpadd0-expr expr.arg gin state))
            (gin (simpadd0-gin-update gin gout-arg)))
         (simpadd0-expr-unary expr.op
                              expr.arg
                              new-arg
                              gout-arg.events
                              gout-arg.thm-name
                              gout-arg.vartys
                              (coerce-unary-info expr.info)
                              gin))
       :sizeof
       (b* (((mv new-type (simpadd0-gout gout-type))
             (simpadd0-tyname expr.type gin state)))
         (mv (expr-sizeof new-type)
             (make-simpadd0-gout
              :events gout-type.events
              :thm-name nil
              :thm-index gout-type.thm-index
              :names-to-avoid gout-type.names-to-avoid
              :vartys gout-type.vartys)))
       :alignof
       (b* (((mv new-type (simpadd0-gout gout-type))
             (simpadd0-tyname expr.type gin state)))
         (mv (make-expr-alignof :type new-type
                                :uscores expr.uscores)
             (make-simpadd0-gout
              :events gout-type.events
              :thm-name nil
              :thm-index gout-type.thm-index
              :names-to-avoid gout-type.names-to-avoid
              :vartys gout-type.vartys)))
       :cast
       (b* (((mv new-type (simpadd0-gout gout-type))
             (simpadd0-tyname expr.type gin state))
            (gin (simpadd0-gin-update gin gout-type))
            ((mv new-arg (simpadd0-gout gout-arg))
             (simpadd0-expr expr.arg gin state))
            (gin (simpadd0-gin-update gin gout-arg)))
         (simpadd0-expr-cast expr.type
                             new-type
                             gout-type.events
                             gout-type.thm-name
                             gout-type.vartys
                             expr.arg
                             new-arg
                             gout-arg.events
                             gout-arg.thm-name
                             gout-arg.vartys
                             (coerce-tyname-info (c$::tyname->info expr.type))
                             gin))
       :binary
       (b* (((mv new-arg1 (simpadd0-gout gout-arg1))
             (simpadd0-expr expr.arg1 gin state))
            (gin (simpadd0-gin-update gin gout-arg1))
            ((mv new-arg2 (simpadd0-gout gout-arg2))
             (simpadd0-expr expr.arg2 gin state))
            (gin (simpadd0-gin-update gin gout-arg2)))
         (simpadd0-expr-binary expr.op
                               expr.arg1
                               new-arg1
                               gout-arg1.events
                               gout-arg1.thm-name
                               gout-arg1.vartys
                               expr.arg2
                               new-arg2
                               gout-arg2.events
                               gout-arg2.thm-name
                               gout-arg2.vartys
                               (coerce-binary-info expr.info)
                               gin))
       :cond
       (b* (((mv new-test (simpadd0-gout gout-test))
             (simpadd0-expr expr.test gin state))
            (gin (simpadd0-gin-update gin gout-test))
            ((mv new-then (simpadd0-gout gout-then))
             (simpadd0-expr-option expr.then gin state))
            (gin (simpadd0-gin-update gin gout-then))
            ((mv new-else (simpadd0-gout gout-else))
             (simpadd0-expr expr.else gin state))
            (gin (simpadd0-gin-update gin gout-else)))
         (simpadd0-expr-cond expr.test
                             new-test
                             gout-test.events
                             gout-test.thm-name
                             gout-test.vartys
                             expr.then
                             new-then
                             gout-then.events
                             gout-then.thm-name
                             gout-then.vartys
                             expr.else
                             new-else
                             gout-else.events
                             gout-else.thm-name
                             gout-else.vartys
                             gin))
       :comma
       (b* (((mv new-first (simpadd0-gout gout-first))
             (simpadd0-expr expr.first gin state))
            (gin (simpadd0-gin-update gin gout-first))
            ((mv new-next (simpadd0-gout gout-next))
             (simpadd0-expr expr.next gin state)))
         (mv (make-expr-comma :first new-first
                              :next new-next)
             (make-simpadd0-gout
              :events (append gout-first.events gout-next.events)
              :thm-name nil
              :thm-index gout-next.thm-index
              :names-to-avoid gout-next.names-to-avoid
              :vartys (omap::update* gout-first.vartys gout-next.vartys))))
       :stmt
       (b* (((mv new-items (simpadd0-gout gout-items))
             (simpadd0-block-item-list expr.items gin state)))
         (mv (expr-stmt new-items)
             (make-simpadd0-gout
              :events gout-items.events
              :thm-name nil
              :thm-index gout-items.thm-index
              :names-to-avoid gout-items.names-to-avoid
              :vartys gout-items.vartys)))
       :tycompat
       (b* (((mv new-type1 (simpadd0-gout gout-type1))
             (simpadd0-tyname expr.type1 gin state))
            (gin (simpadd0-gin-update gin gout-type1))
            ((mv new-type2 (simpadd0-gout gout-type2))
             (simpadd0-tyname expr.type2 gin state)))
         (mv (make-expr-tycompat :type1 new-type1
                                 :type2 new-type2)
             (make-simpadd0-gout
              :events (append gout-type1.events gout-type2.events)
              :thm-name nil
              :thm-index gout-type2.thm-index
              :names-to-avoid gout-type2.names-to-avoid
              :vartys (omap::update* gout-type1.vartys gout-type2.vartys))))
       :offsetof
       (b* (((mv new-type (simpadd0-gout gout-type))
             (simpadd0-tyname expr.type gin state))
            (gin (simpadd0-gin-update gin gout-type))
            ((mv new-member (simpadd0-gout gout-member))
             (simpadd0-member-designor expr.member gin state)))
         (mv (make-expr-offsetof :type new-type
                                 :member new-member)
             (make-simpadd0-gout
              :events (append gout-type.events gout-member.events)
              :thm-name nil
              :thm-index gout-member.thm-index
              :names-to-avoid gout-member.names-to-avoid
              :vartys (omap::update* gout-type.vartys gout-member.vartys))))
       :va-arg
       (b* (((mv new-list (simpadd0-gout gout-list))
             (simpadd0-expr expr.list gin state))
            (gin (simpadd0-gin-update gin gout-list))
            ((mv new-type (simpadd0-gout gout-type))
             (simpadd0-tyname expr.type gin state)))
         (mv (make-expr-va-arg :list new-list
                               :type new-type)
             (make-simpadd0-gout
              :events (append gout-list.events gout-type.events)
              :thm-name nil
              :thm-index gout-type.thm-index
              :names-to-avoid gout-type.names-to-avoid
              :vartys (omap::update* gout-list.vartys gout-type.vartys))))
       :extension
       (b* (((mv new-expr (simpadd0-gout gout-expr))
             (simpadd0-expr expr.expr gin state)))
         (mv (expr-extension new-expr)
             (make-simpadd0-gout
              :events gout-expr.events
              :thm-name nil
              :thm-index gout-expr.thm-index
              :names-to-avoid gout-expr.names-to-avoid
              :vartys gout-expr.vartys)))
       :otherwise (prog2$ (impossible) (mv (irr-expr) (irr-simpadd0-gout)))))
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr-list ((exprs expr-listp) (gin simpadd0-ginp) state)
    :guard (expr-list-unambp exprs)
    :returns (mv (new-exprs expr-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of expressions."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp exprs))
          (mv nil
              (make-simpadd0-gout :events nil
                                  :thm-name nil
                                  :thm-index gin.thm-index
                                  :names-to-avoid gin.names-to-avoid
                                  :vartys nil)))
         ((mv new-expr (simpadd0-gout gout-expr))
          (simpadd0-expr (car exprs) gin state))
         (gin (simpadd0-gin-update gin gout-expr))
         ((mv new-exprs (simpadd0-gout gout-exprs))
          (simpadd0-expr-list (cdr exprs) gin state)))
      (mv (cons new-expr new-exprs)
          (make-simpadd0-gout
           :events (append gout-expr.events gout-exprs.events)
           :thm-name nil
           :thm-index gout-exprs.thm-index
           :names-to-avoid gout-exprs.names-to-avoid
           :vartys (omap::update* gout-expr.vartys gout-exprs.vartys))))
    :measure (expr-list-count exprs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr-option ((expr? expr-optionp) (gin simpadd0-ginp) state)
    :guard (expr-option-unambp expr?)
    :returns (mv (new-expr? expr-optionp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional expression."
    (b* (((simpadd0-gin gin) gin))
      (expr-option-case
       expr?
       :some (simpadd0-expr expr?.val gin state)
       :none (mv nil
                 (make-simpadd0-gout :events nil
                                     :thm-name nil
                                     :thm-index gin.thm-index
                                     :names-to-avoid gin.names-to-avoid
                                     :vartys nil))))
    :measure (expr-option-count expr?)

    ///

    (defret simpadd0-expr-option-iff-expr-option
      (iff new-expr? expr?)
      :hints (("Goal" :expand (simpadd0-expr-option expr? gin state)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-const-expr ((cexpr const-exprp) (gin simpadd0-ginp) state)
    :guard (const-expr-unambp cexpr)
    :returns (mv (new-cexpr const-exprp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a constant expression."
    (b* (((simpadd0-gin gin) gin)
         ((mv new-expr (simpadd0-gout gout-expr))
          (simpadd0-expr (const-expr->expr cexpr) gin state)))
      (mv (const-expr new-expr)
          (make-simpadd0-gout :events gout-expr.events
                              :thm-name nil
                              :thm-index gout-expr.thm-index
                              :names-to-avoid gout-expr.names-to-avoid
                              :vartys gout-expr.vartys)))
    :measure (const-expr-count cexpr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-const-expr-option ((cexpr? const-expr-optionp)
                                      (gin simpadd0-ginp)
                                      state)
    :guard (const-expr-option-unambp cexpr?)
    :returns (mv (new-cexpr? const-expr-optionp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional constant expression."
    (b* (((simpadd0-gin gin) gin))
      (const-expr-option-case
       cexpr?
       :some (simpadd0-const-expr cexpr?.val gin state)
       :none (mv nil
                 (make-simpadd0-gout :events nil
                                     :thm-name nil
                                     :thm-index gin.thm-index
                                     :names-to-avoid gin.names-to-avoid
                                     :vartys nil))))
    :measure (const-expr-option-count cexpr?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-genassoc ((genassoc genassocp) (gin simpadd0-ginp) state)
    :guard (genassoc-unambp genassoc)
    :returns (mv (new-genassoc genassocp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a generic association."
    (b* (((simpadd0-gin gin) gin))
      (genassoc-case
       genassoc
       :type
       (b* (((mv new-type (simpadd0-gout gout-type))
             (simpadd0-tyname genassoc.type gin state))
            (gin (simpadd0-gin-update gin gout-type))
            ((mv new-expr (simpadd0-gout gout-expr))
             (simpadd0-expr genassoc.expr gin state)))
         (mv (make-genassoc-type :type new-type
                                 :expr new-expr)
             (make-simpadd0-gout
              :events (append gout-type.events gout-expr.events)
              :thm-name nil
              :thm-index gout-expr.thm-index
              :names-to-avoid gout-expr.names-to-avoid
              :vartys (omap::update* gout-type.vartys gout-expr.vartys))))
       :default
       (b* (((mv new-expr (simpadd0-gout gout-expr))
             (simpadd0-expr genassoc.expr gin state)))
         (mv (genassoc-default new-expr)
             (make-simpadd0-gout
              :events gout-expr.events
              :thm-name nil
              :thm-index gout-expr.thm-index
              :names-to-avoid gout-expr.names-to-avoid
              :vartys gout-expr.vartys)))))
    :measure (genassoc-count genassoc))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-genassoc-list ((genassocs genassoc-listp)
                                  (gin simpadd0-ginp)
                                  state)
    :guard (genassoc-list-unambp genassocs)
    :returns (mv (new-genassocs genassoc-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of generic associations."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp genassocs))
          (mv nil
              (make-simpadd0-gout :events nil
                                  :thm-name nil
                                  :thm-index gin.thm-index
                                  :names-to-avoid gin.names-to-avoid
                                  :vartys nil)))
         ((mv new-assoc (simpadd0-gout gout-assoc))
          (simpadd0-genassoc (car genassocs) gin state))
         (gin (simpadd0-gin-update gin gout-assoc))
         ((mv new-assocs (simpadd0-gout gout-assocs))
          (simpadd0-genassoc-list (cdr genassocs) gin state)))
      (mv (cons new-assoc new-assocs)
          (make-simpadd0-gout
           :events (append gout-assoc.events gout-assocs.events)
           :thm-name nil
           :thm-index gout-assocs.thm-index
           :names-to-avoid gout-assocs.names-to-avoid
           :vartys (omap::update* gout-assoc.vartys gout-assocs.vartys))))
    :measure (genassoc-list-count genassocs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-member-designor ((memdes member-designorp)
                                    (gin simpadd0-ginp)
                                    state)
    :guard (member-designor-unambp memdes)
    :returns (mv (new-memdes member-designorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a member designator."
    (b* (((simpadd0-gin gin) gin))
      (member-designor-case
       memdes
       :ident (mv (member-designor-fix memdes)
                  (make-simpadd0-gout :events nil
                                      :thm-name nil
                                      :thm-index gin.thm-index
                                      :names-to-avoid gin.names-to-avoid
                                      :vartys nil))
       :dot
       (b* (((mv new-member (simpadd0-gout gout-member))
             (simpadd0-member-designor memdes.member gin state)))
         (mv (make-member-designor-dot :member new-member
                                       :name memdes.name)
             (make-simpadd0-gout
              :events gout-member.events
              :thm-name nil
              :thm-index gout-member.thm-index
              :names-to-avoid gout-member.names-to-avoid
              :vartys gout-member.vartys)))
       :sub
       (b* (((mv new-member (simpadd0-gout gout-member))
             (simpadd0-member-designor memdes.member gin state))
            (gin (simpadd0-gin-update gin gout-member))
            ((mv new-index (simpadd0-gout gout-index))
             (simpadd0-expr memdes.index gin state)))
         (mv (make-member-designor-sub :member new-member
                                       :index new-index)
             (make-simpadd0-gout
              :events (append gout-member.events gout-index.events)
              :thm-name nil
              :thm-index gout-index.thm-index
              :names-to-avoid gout-index.names-to-avoid
              :vartys (omap::update* gout-member.vartys gout-index.vartys))))))
    :measure (member-designor-count memdes))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-type-spec ((tyspec type-specp) (gin simpadd0-ginp) state)
    :guard (type-spec-unambp tyspec)
    :returns (mv (new-tyspec type-specp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a type specifier."
    (b* (((simpadd0-gin gin) gin)
         (gout0 (make-simpadd0-gout :events nil
                                    :thm-name nil
                                    :thm-index gin.thm-index
                                    :names-to-avoid gin.names-to-avoid
                                    :vartys nil)))
      (type-spec-case
       tyspec
       :void (mv (type-spec-fix tyspec) gout0)
       :char (mv (type-spec-fix tyspec) gout0)
       :short (mv (type-spec-fix tyspec) gout0)
       :int (mv (type-spec-fix tyspec) gout0)
       :long (mv (type-spec-fix tyspec) gout0)
       :float (mv (type-spec-fix tyspec) gout0)
       :double (mv (type-spec-fix tyspec) gout0)
       :signed (mv (type-spec-fix tyspec) gout0)
       :unsigned (mv (type-spec-fix tyspec) gout0)
       :bool (mv (type-spec-fix tyspec) gout0)
       :complex (mv (type-spec-fix tyspec) gout0)
       :atomic (b* (((mv new-type (simpadd0-gout gout-type))
                     (simpadd0-tyname tyspec.type gin state)))
                 (mv (type-spec-atomic new-type)
                     (make-simpadd0-gout
                      :events gout-type.events
                      :thm-name nil
                      :thm-index gout-type.thm-index
                      :names-to-avoid gout-type.names-to-avoid
                      :vartys gout-type.vartys)))
       :struct (b* (((mv new-spec (simpadd0-gout gout-spec))
                     (simpadd0-struni-spec tyspec.spec gin state)))
                 (mv (type-spec-struct new-spec)
                     (make-simpadd0-gout
                      :events gout-spec.events
                      :thm-name nil
                      :thm-index gout-spec.thm-index
                      :names-to-avoid gout-spec.names-to-avoid
                      :vartys gout-spec.vartys)))
       :union (b* (((mv new-spec (simpadd0-gout gout-spec))
                    (simpadd0-struni-spec tyspec.spec gin state)))
                (mv (type-spec-union new-spec)
                    (make-simpadd0-gout
                     :events gout-spec.events
                     :thm-name nil
                     :thm-index gout-spec.thm-index
                     :names-to-avoid gout-spec.names-to-avoid
                     :vartys gout-spec.vartys)))
       :enum (b* (((mv new-spec (simpadd0-gout gout-spec))
                   (simpadd0-enumspec tyspec.spec gin state)))
               (mv (type-spec-enum new-spec)
                   (make-simpadd0-gout
                    :events gout-spec.events
                    :thm-name nil
                    :thm-index gout-spec.thm-index
                    :names-to-avoid gout-spec.names-to-avoid
                    :vartys gout-spec.vartys)))
       :typedef (mv (type-spec-fix tyspec) gout0)
       :int128 (mv (type-spec-fix tyspec) gout0)
       :float32 (mv (type-spec-fix tyspec) gout0)
       :float32x (mv (type-spec-fix tyspec) gout0)
       :float64 (mv (type-spec-fix tyspec) gout0)
       :float64x (mv (type-spec-fix tyspec) gout0)
       :float128 (mv (type-spec-fix tyspec) gout0)
       :float128x (mv (type-spec-fix tyspec) gout0)
       :builtin-va-list (mv (type-spec-fix tyspec) gout0)
       :struct-empty (mv (type-spec-fix tyspec) gout0)
       :typeof-expr (b* (((mv new-expr (simpadd0-gout gout-expr))
                          (simpadd0-expr tyspec.expr gin state)))
                      (mv (make-type-spec-typeof-expr :expr new-expr
                                                      :uscores tyspec.uscores)
                          (make-simpadd0-gout
                           :events gout-expr.events
                           :thm-name nil
                           :thm-index gout-expr.thm-index
                           :names-to-avoid gout-expr.names-to-avoid
                           :vartys gout-expr.vartys)))
       :typeof-type (b* (((mv new-type (simpadd0-gout gout-type))
                          (simpadd0-tyname tyspec.type gin state)))
                      (mv (make-type-spec-typeof-type :type new-type
                                                      :uscores tyspec.uscores)
                          (make-simpadd0-gout
                           :events gout-type.events
                           :thm-name nil
                           :thm-index gout-type.thm-index
                           :names-to-avoid gout-type.names-to-avoid
                           :vartys gout-type.vartys)))
       :typeof-ambig (prog2$ (impossible)
                             (mv (irr-type-spec) (irr-simpadd0-gout)))
       :auto-type (mv (type-spec-fix tyspec) gout0)))
    :measure (type-spec-count tyspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-spec/qual ((specqual spec/qual-p)
                              (gin simpadd0-ginp)
                              state)
    :guard (spec/qual-unambp specqual)
    :returns (mv (new-specqual spec/qual-p)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a type specifier or qualifier."
    (b* (((simpadd0-gin gin) gin))
      (spec/qual-case
       specqual
       :typespec (b* (((mv new-spec (simpadd0-gout gout-spec))
                       (simpadd0-type-spec specqual.spec gin state)))
                   (mv (spec/qual-typespec new-spec)
                       (make-simpadd0-gout
                        :events gout-spec.events
                        :thm-name nil
                        :thm-index gout-spec.thm-index
                        :names-to-avoid gout-spec.names-to-avoid
                        :vartys gout-spec.vartys)))
       :typequal (mv (spec/qual-fix specqual)
                     (make-simpadd0-gout
                      :events nil
                      :thm-name nil
                      :thm-index gin.thm-index
                      :names-to-avoid gin.names-to-avoid
                      :vartys nil))
       :align (b* (((mv new-spec (simpadd0-gout gout-spec))
                    (simpadd0-align-spec specqual.spec gin state)))
                (mv (spec/qual-align new-spec)
                    (make-simpadd0-gout
                     :events gout-spec.events
                     :thm-name nil
                     :thm-index gout-spec.thm-index
                     :names-to-avoid gout-spec.names-to-avoid
                     :vartys gout-spec.vartys)))
       :attrib (mv (spec/qual-fix specqual)
                   (make-simpadd0-gout
                    :events nil
                    :thm-name nil
                    :thm-index gin.thm-index
                    :names-to-avoid gin.names-to-avoid
                    :vartys nil))))
    :measure (spec/qual-count specqual))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-spec/qual-list ((specquals spec/qual-listp)
                                   (gin simpadd0-ginp)
                                   state)
    :guard (spec/qual-list-unambp specquals)
    :returns (mv (new-specquals spec/qual-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of type specifiers and qualifiers."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp specquals))
          (mv nil
              (make-simpadd0-gout
               :events nil
               :thm-name nil
               :thm-index gin.thm-index
               :names-to-avoid gin.names-to-avoid
               :vartys nil)))
         ((mv new-specqual (simpadd0-gout gout-specqual))
          (simpadd0-spec/qual (car specquals) gin state))
         (gin (simpadd0-gin-update gin gout-specqual))
         ((mv new-specquals (simpadd0-gout gout-specquals))
          (simpadd0-spec/qual-list (cdr specquals) gin state)))
      (mv (cons new-specqual new-specquals)
          (make-simpadd0-gout
           :events (append gout-specqual.events gout-specquals.events)
           :thm-name nil
           :thm-index gout-specquals.thm-index
           :names-to-avoid gout-specquals.names-to-avoid
           :vartys (omap::update* gout-specqual.vartys gout-specquals.vartys))))
    :measure (spec/qual-list-count specquals))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-align-spec ((alignspec align-specp)
                               (gin simpadd0-ginp)
                               state)
    :guard (align-spec-unambp alignspec)
    :returns (mv (new-alignspec align-specp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an alignment specifier."
    (b* (((simpadd0-gin gin) gin))
      (align-spec-case
       alignspec
       :alignas-type (b* (((mv new-type (simpadd0-gout gout-type))
                           (simpadd0-tyname alignspec.type gin state)))
                       (mv (align-spec-alignas-type new-type)
                           (make-simpadd0-gout
                            :events gout-type.events
                            :thm-name nil
                            :thm-index gout-type.thm-index
                            :names-to-avoid gout-type.names-to-avoid
                            :vartys gout-type.vartys)))
       :alignas-expr (b* (((mv new-expr (simpadd0-gout gout-expr))
                           (simpadd0-const-expr alignspec.expr gin state)))
                       (mv (align-spec-alignas-expr new-expr)
                           (make-simpadd0-gout
                            :events gout-expr.events
                            :thm-name nil
                            :thm-index gout-expr.thm-index
                            :names-to-avoid gout-expr.names-to-avoid
                            :vartys gout-expr.vartys)))
       :alignas-ambig (prog2$ (impossible)
                              (mv (irr-align-spec) (irr-simpadd0-gout)))))
    :measure (align-spec-count alignspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-decl-spec ((declspec decl-specp) (gin simpadd0-ginp) state)
    :guard (decl-spec-unambp declspec)
    :returns (mv (new-declspec decl-specp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a declaration specifier."
    (b* (((simpadd0-gin gin) gin))
      (decl-spec-case
       declspec
       :stoclass (mv (decl-spec-fix declspec)
                     (make-simpadd0-gout
                      :events nil
                      :thm-name nil
                      :thm-index gin.thm-index
                      :names-to-avoid gin.names-to-avoid
                      :vartys nil))
       :typespec (b* (((mv new-spec (simpadd0-gout gout-spec))
                       (simpadd0-type-spec declspec.spec gin state)))
                   (mv (decl-spec-typespec new-spec)
                       (make-simpadd0-gout
                        :events gout-spec.events
                        :thm-name nil
                        :thm-index gout-spec.thm-index
                        :names-to-avoid gout-spec.names-to-avoid
                        :vartys gout-spec.vartys)))
       :typequal (mv (decl-spec-fix declspec)
                     (make-simpadd0-gout
                      :events nil
                      :thm-name nil
                      :thm-index gin.thm-index
                      :names-to-avoid gin.names-to-avoid
                      :vartys nil))
       :function (mv (decl-spec-fix declspec)
                     (make-simpadd0-gout
                      :events nil
                      :thm-name nil
                      :thm-index gin.thm-index
                      :names-to-avoid gin.names-to-avoid
                      :vartys nil))
       :align (b* (((mv new-spec (simpadd0-gout gout-spec))
                    (simpadd0-align-spec declspec.spec gin state)))
                (mv (decl-spec-align new-spec)
                    (make-simpadd0-gout
                     :events gout-spec.events
                     :thm-name nil
                     :thm-index gout-spec.thm-index
                     :names-to-avoid gout-spec.names-to-avoid
                     :vartys gout-spec.vartys)))
       :attrib (mv (decl-spec-fix declspec)
                   (make-simpadd0-gout
                    :events nil
                    :thm-name nil
                    :thm-index gin.thm-index
                    :names-to-avoid gin.names-to-avoid
                    :vartys nil))
       :stdcall (mv (decl-spec-fix declspec)
                    (make-simpadd0-gout
                     :events nil
                     :thm-name nil
                     :thm-index gin.thm-index
                     :names-to-avoid gin.names-to-avoid
                     :vartys nil))
       :declspec (mv (decl-spec-fix declspec)
                     (make-simpadd0-gout
                      :events nil
                      :thm-name nil
                      :thm-index gin.thm-index
                      :names-to-avoid gin.names-to-avoid
                      :vartys nil))))
    :measure (decl-spec-count declspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-decl-spec-list ((declspecs decl-spec-listp)
                                   (gin simpadd0-ginp)
                                   state)
    :guard (decl-spec-list-unambp declspecs)
    :returns (mv (new-declspecs decl-spec-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of declaration specifiers."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp declspecs))
          (mv nil
              (make-simpadd0-gout
               :events nil
               :thm-name nil
               :thm-index gin.thm-index
               :names-to-avoid gin.names-to-avoid
               :vartys nil)))
         ((mv new-declspec (simpadd0-gout gout-declspec))
          (simpadd0-decl-spec (car declspecs) gin state))
         (gin (simpadd0-gin-update gin gout-declspec))
         ((mv new-declspecs (simpadd0-gout gout-declspecs))
          (simpadd0-decl-spec-list (cdr declspecs) gin state)))
      (mv (cons new-declspec new-declspecs)
          (make-simpadd0-gout
           :events (append gout-declspec.events gout-declspecs.events)
           :thm-name nil
           :thm-index gout-declspecs.thm-index
           :names-to-avoid gout-declspecs.names-to-avoid
           :vartys (omap::update* gout-declspec.vartys gout-declspecs.vartys))))
    :measure (decl-spec-list-count declspecs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initer ((initer initerp) (gin simpadd0-ginp) state)
    :guard (initer-unambp initer)
    :returns (mv (new-initer initerp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an initializer."
    (b* (((simpadd0-gin gin) gin))
      (initer-case
       initer
       :single (b* (((mv new-expr (simpadd0-gout gout-expr))
                     (simpadd0-expr initer.expr gin state)))
                 (mv (initer-single new-expr)
                     (make-simpadd0-gout
                      :events gout-expr.events
                      :thm-name nil
                      :thm-index gout-expr.thm-index
                      :names-to-avoid gout-expr.names-to-avoid
                      :vartys gout-expr.vartys)))
       :list (b* (((mv new-elems (simpadd0-gout gout-elems))
                   (simpadd0-desiniter-list initer.elems gin state)))
               (mv (make-initer-list :elems new-elems
                                     :final-comma initer.final-comma)
                   (make-simpadd0-gout
                    :events gout-elems.events
                    :thm-name nil
                    :thm-index gout-elems.thm-index
                    :names-to-avoid gout-elems.names-to-avoid
                    :vartys gout-elems.vartys)))))
    :measure (initer-count initer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initer-option ((initer? initer-optionp)
                                  (gin simpadd0-ginp)
                                  state)
    :guard (initer-option-unambp initer?)
    :returns (mv (new-initer? initer-optionp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional initializer."
    (b* (((simpadd0-gin gin) gin))
      (initer-option-case
       initer?
       :some (simpadd0-initer initer?.val gin state)
       :none (mv nil
                 (make-simpadd0-gout
                  :events nil
                  :thm-name nil
                  :thm-index gin.thm-index
                  :names-to-avoid gin.names-to-avoid
                  :vartys nil))))
    :measure (initer-option-count initer?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-desiniter ((desiniter desiniterp)
                              (gin simpadd0-ginp)
                              state)
    :guard (desiniter-unambp desiniter)
    :returns (mv (new-desiniter desiniterp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an initializer with optional designations."
    (b* (((desiniter desiniter) desiniter)
         ((mv new-designors (simpadd0-gout gout-designors))
          (simpadd0-designor-list desiniter.designors gin state))
         ((mv new-initer (simpadd0-gout gout-initer))
          (simpadd0-initer desiniter.initer gin state)))
      (mv (make-desiniter :designors new-designors
                          :initer new-initer)
          (make-simpadd0-gout
           :events (append gout-designors.events gout-initer.events)
           :thm-name nil
           :thm-index gout-initer.thm-index
           :names-to-avoid gout-initer.names-to-avoid
           :vartys (omap::update* gout-designors.vartys gout-initer.vartys))))
    :measure (desiniter-count desiniter))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-desiniter-list ((desiniters desiniter-listp)
                                   (gin simpadd0-ginp)
                                   state)
    :guard (desiniter-list-unambp desiniters)
    :returns (mv (new-desiniters desiniter-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of initializers with optional designations."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp desiniters))
          (mv nil
              (make-simpadd0-gout
               :events nil
               :thm-name nil
               :thm-index gin.thm-index
               :names-to-avoid gin.names-to-avoid
               :vartys nil)))
         ((mv new-desiniter (simpadd0-gout gout-desiniter))
          (simpadd0-desiniter (car desiniters) gin state))
         (gin (simpadd0-gin-update gin gout-desiniter))
         ((mv new-desiniters (simpadd0-gout gout-desiniters))
          (simpadd0-desiniter-list (cdr desiniters) gin state)))
      (mv (cons new-desiniter new-desiniters)
          (make-simpadd0-gout
           :events (append gout-desiniter.events gout-desiniters.events)
           :thm-name nil
           :thm-index gout-desiniters.thm-index
           :names-to-avoid gout-desiniters.names-to-avoid
           :vartys (omap::update* gout-desiniter.vartys gout-desiniters.vartys))))
    :measure (desiniter-list-count desiniters))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-designor ((designor designorp) (gin simpadd0-ginp) state)
    :guard (designor-unambp designor)
    :returns (mv (new-designor designorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a designator."
    (b* (((simpadd0-gin gin) gin))
      (designor-case
       designor
       :sub (b* (((mv new-index (simpadd0-gout gout-index))
                  (simpadd0-const-expr designor.index gin state)))
              (mv (designor-sub new-index)
                  (make-simpadd0-gout
                   :events gout-index.events
                   :thm-name nil
                   :thm-index gout-index.thm-index
                   :names-to-avoid gout-index.names-to-avoid
                   :vartys gout-index.vartys)))
       :dot (mv (designor-fix designor)
                (make-simpadd0-gout
                 :events nil
                 :thm-name nil
                 :thm-index gin.thm-index
                 :names-to-avoid gin.names-to-avoid
                 :vartys nil))))
    :measure (designor-count designor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-designor-list ((designors designor-listp)
                                  (gin simpadd0-ginp)
                                  state)
    :guard (designor-list-unambp designors)
    :returns (mv (new-designors designor-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of designators."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp designors))
          (mv nil
              (make-simpadd0-gout
               :events nil
               :thm-name nil
               :thm-index gin.thm-index
               :names-to-avoid gin.names-to-avoid
               :vartys nil)))
         ((mv new-designor (simpadd0-gout gout-designor))
          (simpadd0-designor (car designors) gin state))
         (gin (simpadd0-gin-update gin gout-designor))
         ((mv new-designors (simpadd0-gout gout-designors))
          (simpadd0-designor-list (cdr designors) gin state)))
      (mv (cons new-designor new-designors)
          (make-simpadd0-gout
           :events (append gout-designor.events gout-designors.events)
           :thm-name nil
           :thm-index gout-designors.thm-index
           :names-to-avoid gout-designors.names-to-avoid
           :vartys (omap::update* gout-designor.vartys gout-designors.vartys))))
    :measure (designor-list-count designors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-declor ((declor declorp) (gin simpadd0-ginp) state)
    :guard (declor-unambp declor)
    :returns (mv (new-declor declorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a declarator."
    (b* (((simpadd0-gin gin) gin)
         ((declor declor) declor)
         ((mv new-direct (simpadd0-gout gout-direct))
          (simpadd0-dirdeclor declor.direct gin state)))
      (mv (make-declor :pointers declor.pointers
                       :direct new-direct)
          (make-simpadd0-gout
           :events gout-direct.events
           :thm-name nil
           :thm-index gout-direct.thm-index
           :names-to-avoid gout-direct.names-to-avoid
           :vartys gout-direct.vartys)))
    :measure (declor-count declor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-declor-option ((declor? declor-optionp)
                                  (gin simpadd0-ginp)
                                  state)
    :guard (declor-option-unambp declor?)
    :returns (mv (new-declor? declor-optionp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional declarator."
    (b* (((simpadd0-gin gin) gin))
      (declor-option-case
       declor?
       :some (simpadd0-declor declor?.val gin state)
       :none (mv nil
                 (make-simpadd0-gout
                  :events nil
                  :thm-name nil
                  :thm-index gin.thm-index
                  :names-to-avoid gin.names-to-avoid
                  :vartys nil))))
    :measure (declor-option-count declor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-dirdeclor ((dirdeclor dirdeclorp) (gin simpadd0-ginp) state)
    :guard (dirdeclor-unambp dirdeclor)
    :returns (mv (new-dirdeclor dirdeclorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a direct declarator."
    (b* (((simpadd0-gin gin) gin))
      (dirdeclor-case
       dirdeclor
       :ident (mv (dirdeclor-fix dirdeclor)
                  (make-simpadd0-gout
                   :events nil
                   :thm-name nil
                   :thm-index gin.thm-index
                   :names-to-avoid gin.names-to-avoid
                   :vartys nil))
       :paren (b* (((mv new-declor (simpadd0-gout gout-declor))
                    (simpadd0-declor dirdeclor.inner gin state)))
                (mv (dirdeclor-paren new-declor)
                    (make-simpadd0-gout
                     :events gout-declor.events
                     :thm-name nil
                     :thm-index gout-declor.thm-index
                     :names-to-avoid gout-declor.names-to-avoid
                     :vartys gout-declor.vartys)))
       :array (b* (((mv new-decl (simpadd0-gout gout-decl))
                    (simpadd0-dirdeclor dirdeclor.declor gin state))
                   (gin (simpadd0-gin-update gin gout-decl))
                   ((mv new-expr? (simpadd0-gout gout-expr?))
                    (simpadd0-expr-option dirdeclor.size? gin state)))
                (mv (make-dirdeclor-array :declor new-decl
                                          :qualspecs dirdeclor.qualspecs
                                          :size? new-expr?)
                    (make-simpadd0-gout
                     :events (append gout-decl.events gout-expr?.events)
                     :thm-name nil
                     :thm-index gout-expr?.thm-index
                     :names-to-avoid gout-expr?.names-to-avoid
                     :vartys (omap::update* gout-decl.vartys gout-expr?.vartys))))
       :array-static1 (b* (((mv new-decl (simpadd0-gout gout-decl))
                            (simpadd0-dirdeclor dirdeclor.declor gin state))
                           (gin (simpadd0-gin-update gin gout-decl))
                           ((mv new-expr (simpadd0-gout gout-expr))
                            (simpadd0-expr dirdeclor.size gin state)))
                        (mv (make-dirdeclor-array-static1
                             :declor new-decl
                             :qualspecs dirdeclor.qualspecs
                             :size new-expr)
                            (make-simpadd0-gout
                             :events (append gout-decl.events gout-expr.events)
                             :thm-name nil
                             :thm-index gout-expr.thm-index
                             :names-to-avoid gout-expr.names-to-avoid
                             :vartys (omap::update* gout-decl.vartys
                                                    gout-expr.vartys))))
       :array-static2 (b* (((mv new-decl (simpadd0-gout gout-decl))
                            (simpadd0-dirdeclor dirdeclor.declor gin state))
                           (gin (simpadd0-gin-update gin gout-decl))
                           ((mv new-expr (simpadd0-gout gout-expr))
                            (simpadd0-expr dirdeclor.size gin state)))
                        (mv (make-dirdeclor-array-static2
                             :declor new-decl
                             :qualspecs dirdeclor.qualspecs
                             :size new-expr)
                            (make-simpadd0-gout
                             :events (append gout-decl.events gout-expr.events)
                             :thm-name nil
                             :thm-index gout-expr.thm-index
                             :names-to-avoid gout-expr.names-to-avoid
                             :vartys (omap::update* gout-decl.vartys
                                                    gout-expr.vartys))))
       :array-star (b* (((mv new-decl (simpadd0-gout gout-decl))
                         (simpadd0-dirdeclor dirdeclor.declor gin state)))
                     (mv (make-dirdeclor-array-star
                          :declor new-decl
                          :qualspecs dirdeclor.qualspecs)
                         (make-simpadd0-gout
                          :events gout-decl.events
                          :thm-name nil
                          :thm-index gout-decl.thm-index
                          :names-to-avoid gout-decl.names-to-avoid
                          :vartys gout-decl.vartys)))
       :function-params (b* (((mv new-decl (simpadd0-gout gout-decl))
                              (simpadd0-dirdeclor dirdeclor.declor gin state))
                             (gin (simpadd0-gin-update gin gout-decl))
                             ((mv new-params (simpadd0-gout gout-params))
                              (simpadd0-param-declon-list dirdeclor.params
                                                          gin
                                                          state)))
                          (mv (make-dirdeclor-function-params
                               :declor new-decl
                               :params new-params
                               :ellipsis dirdeclor.ellipsis)
                              (make-simpadd0-gout
                               :events (append gout-decl.events
                                               gout-params.events)
                               :thm-name nil
                               :thm-index gout-params.thm-index
                               :names-to-avoid gout-params.names-to-avoid
                               :vartys (omap::update* gout-decl.vartys
                                                      gout-params.vartys))))
       :function-names (b* (((mv new-decl (simpadd0-gout gout-decl))
                             (simpadd0-dirdeclor dirdeclor.declor gin state)))
                         (mv (make-dirdeclor-function-names
                              :declor new-decl
                              :names dirdeclor.names)
                             (make-simpadd0-gout
                              :events gout-decl.events
                              :thm-name nil
                              :thm-index gout-decl.thm-index
                              :names-to-avoid gout-decl.names-to-avoid
                              :vartys gout-decl.vartys)))))
    :measure (dirdeclor-count dirdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-absdeclor ((absdeclor absdeclorp) (gin simpadd0-ginp) state)
    :guard (absdeclor-unambp absdeclor)
    :returns (mv (new-absdeclor absdeclorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an abstract declarator."
    (b* (((simpadd0-gin gin) gin)
         ((absdeclor absdeclor) absdeclor)
         ((mv new-direct? (simpadd0-gout gout-direct?))
          (simpadd0-dirabsdeclor-option absdeclor.direct? gin state)))
      (mv (make-absdeclor :pointers absdeclor.pointers
                          :direct? new-direct?)
          (make-simpadd0-gout
           :events gout-direct?.events
           :thm-name nil
           :thm-index gout-direct?.thm-index
           :names-to-avoid gout-direct?.names-to-avoid
           :vartys gout-direct?.vartys)))
    :measure (absdeclor-count absdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-absdeclor-option ((absdeclor? absdeclor-optionp)
                                     (gin simpadd0-ginp)
                                     state)
    :guard (absdeclor-option-unambp absdeclor?)
    :returns (mv (new-absdeclor? absdeclor-optionp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional abstract declarator."
    (b* (((simpadd0-gin gin) gin))
      (absdeclor-option-case
       absdeclor?
       :some (simpadd0-absdeclor absdeclor?.val gin state)
       :none (mv nil
                 (make-simpadd0-gout
                  :events nil
                  :thm-name nil
                  :thm-index gin.thm-index
                  :names-to-avoid gin.names-to-avoid
                  :vartys nil))))
    :measure (absdeclor-option-count absdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-dirabsdeclor ((dirabsdeclor dirabsdeclorp)
                                 (gin simpadd0-ginp)
                                 state)
    :guard (dirabsdeclor-unambp dirabsdeclor)
    :returns (mv (new-dirabsdeclor dirabsdeclorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a direct abstract declarator."
    (b* (((simpadd0-gin gin) gin))
      (dirabsdeclor-case
       dirabsdeclor
       :dummy-base (prog2$
                    (raise "Misusage error: ~x0."
                           (dirabsdeclor-fix dirabsdeclor))
                    (mv (irr-dirabsdeclor) (irr-simpadd0-gout)))
       :paren (b* (((mv new-inner (simpadd0-gout gout-inner))
                    (simpadd0-absdeclor dirabsdeclor.inner gin state)))
                (mv (dirabsdeclor-paren new-inner)
                    (make-simpadd0-gout
                     :events gout-inner.events
                     :thm-name nil
                     :thm-index gout-inner.thm-index
                     :names-to-avoid gout-inner.names-to-avoid
                     :vartys gout-inner.vartys)))
       :array (b* (((mv new-declor? (simpadd0-gout gout-declor?))
                    (simpadd0-dirabsdeclor-option
                     dirabsdeclor.declor? gin state))
                   (gin (simpadd0-gin-update gin gout-declor?))
                   ((mv new-size? (simpadd0-gout gout-expr?))
                    (simpadd0-expr-option dirabsdeclor.size? gin state)))
                (mv (make-dirabsdeclor-array
                     :declor? new-declor?
                     :qualspecs dirabsdeclor.qualspecs
                     :size? new-size?)
                    (make-simpadd0-gout
                     :events (append gout-declor?.events gout-expr?.events)
                     :thm-name nil
                     :thm-index gout-expr?.thm-index
                     :names-to-avoid gout-expr?.names-to-avoid
                     :vartys (omap::update* gout-declor?.vartys
                                            gout-expr?.vartys))))
       :array-static1 (b* (((mv new-declor? (simpadd0-gout gout-declor?))
                            (simpadd0-dirabsdeclor-option dirabsdeclor.declor?
                                                          gin
                                                          state))
                           (gin (simpadd0-gin-update gin gout-declor?))
                           ((mv new-size (simpadd0-gout gout-expr))
                            (simpadd0-expr dirabsdeclor.size gin state)))
                        (mv (make-dirabsdeclor-array-static1
                             :declor? new-declor?
                             :qualspecs dirabsdeclor.qualspecs
                             :size new-size)
                            (make-simpadd0-gout
                             :events (append gout-declor?.events
                                             gout-expr.events)
                             :thm-name nil
                             :thm-index gout-expr.thm-index
                             :names-to-avoid gout-expr.names-to-avoid
                             :vartys (omap::update* gout-declor?.vartys
                                                    gout-expr.vartys))))
       :array-static2 (b* (((mv new-declor? (simpadd0-gout gout-declor?))
                            (simpadd0-dirabsdeclor-option dirabsdeclor.declor?
                                                          gin state))
                           (gin (simpadd0-gin-update gin gout-declor?))
                           ((mv new-size (simpadd0-gout gout-expr))
                            (simpadd0-expr dirabsdeclor.size gin state)))
                        (mv (make-dirabsdeclor-array-static2
                             :declor? new-declor?
                             :qualspecs dirabsdeclor.qualspecs
                             :size new-size)
                            (make-simpadd0-gout
                             :events (append gout-declor?.events
                                             gout-expr.events)
                             :thm-name nil
                             :thm-index gout-expr.thm-index
                             :names-to-avoid gout-expr.names-to-avoid
                             :vartys (omap::update* gout-declor?.vartys
                                                    gout-expr.vartys))))
       :array-star (b* (((mv new-declor? (simpadd0-gout gout-declor?))
                         (simpadd0-dirabsdeclor-option dirabsdeclor.declor?
                                                       gin
                                                       state)))
                     (mv (dirabsdeclor-array-star new-declor?)
                         (make-simpadd0-gout
                          :events gout-declor?.events
                          :thm-name nil
                          :thm-index gout-declor?.thm-index
                          :names-to-avoid gout-declor?.names-to-avoid
                          :vartys gout-declor?.vartys)))
       :function (b* (((mv new-declor? (simpadd0-gout gout-declor?))
                       (simpadd0-dirabsdeclor-option dirabsdeclor.declor?
                                                     gin
                                                     state))
                      (gin (simpadd0-gin-update gin gout-declor?))
                      ((mv new-params (simpadd0-gout gout-params))
                       (simpadd0-param-declon-list dirabsdeclor.params gin state)))
                   (mv (make-dirabsdeclor-function
                        :declor? new-declor?
                        :params new-params
                        :ellipsis dirabsdeclor.ellipsis)
                       (make-simpadd0-gout
                        :events (append gout-declor?.events gout-params.events)
                        :thm-name nil
                        :thm-index gout-params.thm-index
                        :names-to-avoid gout-params.names-to-avoid
                        :vartys (omap::update* gout-declor?.vartys
                                               gout-params.vartys))))))
    :measure (dirabsdeclor-count dirabsdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-dirabsdeclor-option ((dirabsdeclor? dirabsdeclor-optionp)
                                        (gin simpadd0-ginp)
                                        state)
    :guard (dirabsdeclor-option-unambp dirabsdeclor?)
    :returns (mv (new-dirabsdeclor? dirabsdeclor-optionp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional direct abstract declarator."
    (b* (((simpadd0-gin gin) gin))
      (dirabsdeclor-option-case
       dirabsdeclor?
       :some (simpadd0-dirabsdeclor dirabsdeclor?.val gin state)
       :none (mv nil
                 (make-simpadd0-gout
                  :events nil
                  :thm-name nil
                  :thm-index gin.thm-index
                  :names-to-avoid gin.names-to-avoid
                  :vartys nil))))
    :measure (dirabsdeclor-option-count dirabsdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-param-declon ((paramdecl param-declonp) (gin simpadd0-ginp) state)
    :guard (param-declon-unambp paramdecl)
    :returns (mv (new-paramdecl param-declonp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a parameter declaration."
    (b* (((simpadd0-gin gin) gin)
         ((param-declon paramdecl) paramdecl)
         ((mv new-specs (simpadd0-gout gout-specs))
          (simpadd0-decl-spec-list paramdecl.specs gin state))
         (gin (simpadd0-gin-update gin gout-specs))
         ((mv new-declor (simpadd0-gout gout-declor))
          (simpadd0-param-declor paramdecl.declor gin state)))
      (mv (make-param-declon :specs new-specs
                             :declor new-declor)
          (make-simpadd0-gout
           :events (append gout-specs.events gout-declor.events)
           :thm-name nil
           :thm-index gout-declor.thm-index
           :names-to-avoid gout-declor.names-to-avoid
           :vartys (omap::update* gout-specs.vartys gout-declor.vartys))))
    :measure (param-declon-count paramdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-param-declon-list ((paramdecls param-declon-listp)
                                      (gin simpadd0-ginp)
                                      state)
    :guard (param-declon-list-unambp paramdecls)
    :returns (mv (new-paramdecls param-declon-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of parameter declarations."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp paramdecls))
          (mv nil
              (make-simpadd0-gout
               :events nil
               :thm-name nil
               :thm-index gin.thm-index
               :names-to-avoid gin.names-to-avoid
               :vartys nil)))
         ((mv new-paramdecl (simpadd0-gout gout-paramdecl))
          (simpadd0-param-declon (car paramdecls) gin state))
         (gin (simpadd0-gin-update gin gout-paramdecl))
         ((mv new-paramdecls (simpadd0-gout gout-paramdecls))
          (simpadd0-param-declon-list (cdr paramdecls) gin state)))
      (mv (cons new-paramdecl new-paramdecls)
          (make-simpadd0-gout
           :events (append gout-paramdecl.events gout-paramdecls.events)
           :thm-name nil
           :thm-index gout-paramdecls.thm-index
           :names-to-avoid gout-paramdecls.names-to-avoid
           :vartys (omap::update* gout-paramdecl.vartys gout-paramdecls.vartys))))
    :measure (param-declon-list-count paramdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-param-declor ((paramdeclor param-declorp)
                                 (gin simpadd0-ginp)
                                 state)
    :guard (param-declor-unambp paramdeclor)
    :returns (mv (new-paramdeclor param-declorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a parameter declarator."
    (b* (((simpadd0-gin gin) gin))
      (param-declor-case
       paramdeclor
       :nonabstract (b* (((mv new-declor (simpadd0-gout gout-declor))
                          (simpadd0-declor paramdeclor.declor gin state)))
                      (mv (param-declor-nonabstract new-declor)
                          (make-simpadd0-gout
                           :events gout-declor.events
                           :thm-name nil
                           :thm-index gout-declor.thm-index
                           :names-to-avoid gout-declor.names-to-avoid
                           :vartys gout-declor.vartys)))
       :abstract (b* (((mv new-absdeclor (simpadd0-gout gout-absdeclor))
                       (simpadd0-absdeclor paramdeclor.declor gin state)))
                   (mv (param-declor-abstract new-absdeclor)
                       (make-simpadd0-gout
                        :events gout-absdeclor.events
                        :thm-name nil
                        :thm-index gout-absdeclor.thm-index
                        :names-to-avoid gout-absdeclor.names-to-avoid
                        :vartys gout-absdeclor.vartys)))
       :none (mv (param-declor-none)
                 (make-simpadd0-gout
                  :events nil
                  :thm-name nil
                  :thm-index gin.thm-index
                  :names-to-avoid gin.names-to-avoid
                  :vartys nil))
       :ambig (prog2$ (impossible) (mv (irr-param-declor) (irr-simpadd0-gout)))))
    :measure (param-declor-count paramdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-tyname ((tyname tynamep) (gin simpadd0-ginp) state)
    :guard (tyname-unambp tyname)
    :returns (mv (new-tyname tynamep)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a type name."
    (b* (((simpadd0-gin gin) gin)
         ((tyname tyname) tyname)
         ((mv new-specquals (simpadd0-gout gout-specqual))
          (simpadd0-spec/qual-list tyname.specquals gin state))
         (gin (simpadd0-gin-update gin gout-specqual))
         ((mv new-declor? (simpadd0-gout gout-declor?))
          (simpadd0-absdeclor-option tyname.declor? gin state)))
      (mv (make-tyname :specquals new-specquals
                       :declor? new-declor?
                       :info tyname.info)
          (make-simpadd0-gout
           :events (append gout-specqual.events gout-declor?.events)
           :thm-name nil
           :thm-index gout-declor?.thm-index
           :names-to-avoid gout-declor?.names-to-avoid
           :vartys (omap::update* gout-specqual.vartys gout-declor?.vartys))))
    :measure (tyname-count tyname))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-struni-spec ((struni-spec struni-specp)
                               (gin simpadd0-ginp)
                               state)
    :guard (struni-spec-unambp struni-spec)
    :returns (mv (new-struni-spec struni-specp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure or union specifier."
    (b* (((simpadd0-gin gin) gin)
         ((struni-spec struni-spec) struni-spec)
         ((mv new-members (simpadd0-gout gout-members))
          (simpadd0-structdecl-list struni-spec.members gin state)))
      (mv (make-struni-spec :name? struni-spec.name?
                            :members new-members)
          (make-simpadd0-gout
           :events gout-members.events
           :thm-name nil
           :thm-index gout-members.thm-index
           :names-to-avoid gout-members.names-to-avoid
           :vartys gout-members.vartys)))
    :measure (struni-spec-count struni-spec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdecl ((structdecl structdeclp)
                               (gin simpadd0-ginp)
                               state)
    :guard (structdecl-unambp structdecl)
    :returns (mv (new-structdecl structdeclp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure declaration."
    (b* (((simpadd0-gin gin) gin))
      (structdecl-case
       structdecl
       :member (b* (((mv new-specqual (simpadd0-gout gout-specqual))
                     (simpadd0-spec/qual-list structdecl.specqual gin state))
                    (gin (simpadd0-gin-update gin gout-specqual))
                    ((mv new-declor (simpadd0-gout gout-declor))
                     (simpadd0-structdeclor-list structdecl.declor gin state)))
                 (mv (make-structdecl-member
                      :extension structdecl.extension
                      :specqual new-specqual
                      :declor new-declor
                      :attrib structdecl.attrib)
                     (make-simpadd0-gout
                      :events (append gout-specqual.events
                                      gout-declor.events)
                      :thm-name nil
                      :thm-index gout-declor.thm-index
                      :names-to-avoid gout-declor.names-to-avoid
                      :vartys (omap::update* gout-specqual.vartys
                                             gout-declor.vartys))))
       :statassert (b* (((mv new-structdecl (simpadd0-gout gout-structdecl))
                         (simpadd0-statassert structdecl.unwrap gin state)))
                     (mv (structdecl-statassert new-structdecl)
                         (make-simpadd0-gout
                          :events gout-structdecl.events
                          :thm-name nil
                          :thm-index gout-structdecl.thm-index
                          :names-to-avoid gout-structdecl.names-to-avoid
                          :vartys gout-structdecl.vartys)))
       :empty (mv (structdecl-empty)
                  (make-simpadd0-gout
                   :events nil
                   :thm-name nil
                   :thm-index gin.thm-index
                   :names-to-avoid gin.names-to-avoid
                   :vartys nil))))
    :measure (structdecl-count structdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdecl-list ((structdecls structdecl-listp)
                                    (gin simpadd0-ginp)
                                    state)
    :guard (structdecl-list-unambp structdecls)
    :returns (mv (new-structdecls structdecl-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of structure declarations."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp structdecls))
          (mv nil
              (make-simpadd0-gout
               :events nil
               :thm-name nil
               :thm-index gin.thm-index
               :names-to-avoid gin.names-to-avoid
               :vartys nil)))
         ((mv new-structdecl (simpadd0-gout gout-structdecl))
          (simpadd0-structdecl (car structdecls) gin state))
         (gin (simpadd0-gin-update gin gout-structdecl))
         ((mv new-structdecls (simpadd0-gout gout-structdecls))
          (simpadd0-structdecl-list (cdr structdecls) gin state)))
      (mv (cons new-structdecl new-structdecls)
          (make-simpadd0-gout
           :events (append gout-structdecl.events gout-structdecls.events)
           :thm-name nil
           :thm-index gout-structdecls.thm-index
           :names-to-avoid gout-structdecls.names-to-avoid
           :vartys (omap::update* gout-structdecl.vartys
                                  gout-structdecls.vartys))))
    :measure (structdecl-list-count structdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdeclor ((structdeclor structdeclorp)
                                 (gin simpadd0-ginp)
                                 state)
    :guard (structdeclor-unambp structdeclor)
    :returns (mv (new-structdeclor structdeclorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure declarator."
    (b* (((simpadd0-gin gin) gin)
         ((structdeclor structdeclor) structdeclor)
         ((mv new-declor? (simpadd0-gout gout-declor?))
          (simpadd0-declor-option structdeclor.declor? gin state))
         (gin (simpadd0-gin-update gin gout-declor?))
         ((mv new-expr? (simpadd0-gout gout-expr?))
          (simpadd0-const-expr-option structdeclor.expr? gin state)))
      (mv (make-structdeclor :declor? new-declor?
                             :expr? new-expr?)
          (make-simpadd0-gout
           :events (append gout-declor?.events gout-expr?.events)
           :thm-name nil
           :thm-index gout-expr?.thm-index
           :names-to-avoid gout-expr?.names-to-avoid
           :vartys (omap::update* gout-declor?.vartys gout-expr?.vartys))))
    :measure (structdeclor-count structdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdeclor-list ((structdeclors structdeclor-listp)
                                      (gin simpadd0-ginp)
                                      state)
    :guard (structdeclor-list-unambp structdeclors)
    :returns (mv (new-structdeclors structdeclor-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of structure declarators."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp structdeclors))
          (mv nil
              (make-simpadd0-gout
               :events nil
               :thm-name nil
               :thm-index gin.thm-index
               :names-to-avoid gin.names-to-avoid
               :vartys nil)))
         ((mv new-structdeclor (simpadd0-gout gout-structdeclor))
          (simpadd0-structdeclor (car structdeclors) gin state))
         (gin (simpadd0-gin-update gin gout-structdeclor))
         ((mv new-structdeclors (simpadd0-gout gout-structdeclors))
          (simpadd0-structdeclor-list (cdr structdeclors) gin state)))
      (mv (cons new-structdeclor new-structdeclors)
          (make-simpadd0-gout
           :events (append gout-structdeclor.events
                           gout-structdeclors.events)
           :thm-name nil
           :thm-index gout-structdeclors.thm-index
           :names-to-avoid gout-structdeclors.names-to-avoid
           :vartys (omap::update* gout-structdeclor.vartys
                                  gout-structdeclors.vartys))))
    :measure (structdeclor-list-count structdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumspec ((enumspec enumspecp) (gin simpadd0-ginp) state)
    :guard (enumspec-unambp enumspec)
    :returns (mv (new-enumspec enumspecp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an enumeration specifier."
    (b* (((simpadd0-gin gin) gin)
         ((enumspec enumspec) enumspec)
         ((mv new-list (simpadd0-gout gout-list))
          (simpadd0-enumer-list enumspec.list gin state)))
      (mv (make-enumspec :name enumspec.name
                         :list new-list
                         :final-comma enumspec.final-comma)
          (make-simpadd0-gout
           :events gout-list.events
           :thm-name nil
           :thm-index gout-list.thm-index
           :names-to-avoid gout-list.names-to-avoid
           :vartys gout-list.vartys)))
    :measure (enumspec-count enumspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumer ((enumer enumerp) (gin simpadd0-ginp) state)
    :guard (enumer-unambp enumer)
    :returns (mv (new-enumer enumerp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an enumerator."
    (b* (((simpadd0-gin gin) gin)
         ((enumer enumer) enumer)
         ((mv new-value (simpadd0-gout gout-value))
          (simpadd0-const-expr-option enumer.value gin state)))
      (mv (make-enumer :name enumer.name
                       :value new-value)
          (make-simpadd0-gout
           :events gout-value.events
           :thm-name nil
           :thm-index gout-value.thm-index
           :names-to-avoid gout-value.names-to-avoid
           :vartys gout-value.vartys)))
    :measure (enumer-count enumer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumer-list ((enumers enumer-listp)
                                (gin simpadd0-ginp)
                                state)
    :guard (enumer-list-unambp enumers)
    :returns (mv (new-enumers enumer-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of enumerators."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp enumers))
          (mv nil
              (make-simpadd0-gout
               :events nil
               :thm-name nil
               :thm-index gin.thm-index
               :names-to-avoid gin.names-to-avoid
               :vartys nil)))
         ((mv new-enumer (simpadd0-gout gout-enumer))
          (simpadd0-enumer (car enumers) gin state))
         (gin (simpadd0-gin-update gin gout-enumer))
         ((mv new-enumers (simpadd0-gout gout-enumers))
          (simpadd0-enumer-list (cdr enumers) gin state)))
      (mv (cons new-enumer new-enumers)
          (make-simpadd0-gout
           :events (append gout-enumer.events gout-enumers.events)
           :thm-name nil
           :thm-index gout-enumers.thm-index
           :names-to-avoid gout-enumers.names-to-avoid
           :vartys (omap::update* gout-enumer.vartys gout-enumers.vartys))))
    :measure (enumer-list-count enumers))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-statassert ((statassert statassertp)
                               (gin simpadd0-ginp)
                               state)
    :guard (statassert-unambp statassert)
    :returns (mv (new-statassert statassertp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an static assertion declaration."
    (b* (((simpadd0-gin gin) gin)
         ((statassert statassert) statassert)
         ((mv new-test (simpadd0-gout gout-test))
          (simpadd0-const-expr statassert.test gin state)))
      (mv (make-statassert :test new-test
                           :message statassert.message)
          (make-simpadd0-gout
           :events gout-test.events
           :thm-name nil
           :thm-index gout-test.thm-index
           :names-to-avoid gout-test.names-to-avoid
           :vartys gout-test.vartys)))
    :measure (statassert-count statassert))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initdeclor ((initdeclor initdeclorp)
                               (gin simpadd0-ginp)
                               state)
    :guard (initdeclor-unambp initdeclor)
    :returns (mv (new-initdeclor initdeclorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an initializer declarator."
    (b* (((simpadd0-gin gin) gin)
         ((initdeclor initdeclor) initdeclor)
         ((mv new-declor (simpadd0-gout gout-declor))
          (simpadd0-declor initdeclor.declor gin state))
         (gin (simpadd0-gin-update gin gout-declor))
         ((mv new-init? (simpadd0-gout gout-init?))
          (simpadd0-initer-option initdeclor.init? gin state)))
      (mv (make-initdeclor :declor new-declor
                           :asm? initdeclor.asm?
                           :attribs initdeclor.attribs
                           :init? new-init?)
          (make-simpadd0-gout
           :events (append gout-declor.events gout-init?.events)
           :thm-name nil
           :thm-index gout-init?.thm-index
           :names-to-avoid gout-init?.names-to-avoid
           :vartys (omap::update* gout-declor.vartys gout-init?.vartys))))
    :measure (initdeclor-count initdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initdeclor-list ((initdeclors initdeclor-listp)
                                    (gin simpadd0-ginp)
                                    state)
    :guard (initdeclor-list-unambp initdeclors)
    :returns (mv (new-initdeclors initdeclor-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of initializer declarators."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp initdeclors))
          (mv nil
              (make-simpadd0-gout
               :events nil
               :thm-name nil
               :thm-index gin.thm-index
               :names-to-avoid gin.names-to-avoid
               :vartys nil)))
         ((mv new-initdeclor (simpadd0-gout gout-initdeclor))
          (simpadd0-initdeclor (car initdeclors) gin state))
         (gin (simpadd0-gin-update gin gout-initdeclor))
         ((mv new-initdeclors (simpadd0-gout gout-initdeclors))
          (simpadd0-initdeclor-list (cdr initdeclors) gin state)))
      (mv (cons new-initdeclor new-initdeclors)
          (make-simpadd0-gout
           :events (append gout-initdeclor.events
                           gout-initdeclors.events)
           :thm-name nil
           :thm-index gout-initdeclors.thm-index
           :names-to-avoid gout-initdeclors.names-to-avoid
           :vartys (omap::update* gout-initdeclor.vartys
                                  gout-initdeclors.vartys))))
    :measure (initdeclor-list-count initdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-decl ((decl declp) (gin simpadd0-ginp) state)
    :guard (decl-unambp decl)
    :returns (mv (new-decl declp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a declaration."
    (b* (((simpadd0-gin gin) gin))
      (decl-case
       decl
       :decl (b* (((mv new-specs (simpadd0-gout gout-specs))
                   (simpadd0-decl-spec-list decl.specs gin state))
                  (gin (simpadd0-gin-update gin gout-specs))
                  ((mv new-init (simpadd0-gout gout-init))
                   (simpadd0-initdeclor-list decl.init gin state)))
               (mv (make-decl-decl :extension decl.extension
                                   :specs new-specs
                                   :init new-init)
                   (make-simpadd0-gout
                    :events (append gout-specs.events
                                    gout-init.events)
                    :thm-name nil
                    :thm-index gout-init.thm-index
                    :names-to-avoid gout-init.names-to-avoid
                    :vartys (omap::update* gout-specs.vartys gout-init.vartys))))
       :statassert (b* (((mv new-decl (simpadd0-gout gout-decl))
                         (simpadd0-statassert decl.unwrap gin state)))
                     (mv (decl-statassert new-decl)
                         (make-simpadd0-gout
                          :events gout-decl.events
                          :thm-name nil
                          :thm-index gout-decl.thm-index
                          :names-to-avoid gout-decl.names-to-avoid
                          :vartys gout-decl.vartys)))))
    :measure (decl-count decl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-decl-list ((decls decl-listp) (gin simpadd0-ginp) state)
    :guard (decl-list-unambp decls)
    :returns (mv (new-decls decl-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of declarations."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp decls))
          (mv nil
              (make-simpadd0-gout
               :events nil
               :thm-name nil
               :thm-index gin.thm-index
               :names-to-avoid gin.names-to-avoid
               :vartys nil)))
         ((mv new-decl (simpadd0-gout gout-decl))
          (simpadd0-decl (car decls) gin state))
         (gin (simpadd0-gin-update gin gout-decl))
         ((mv new-decls (simpadd0-gout gout-decls))
          (simpadd0-decl-list (cdr decls) gin state)))
      (mv (cons new-decl new-decls)
          (make-simpadd0-gout
           :events (append gout-decl.events gout-decls.events)
           :thm-name nil
           :thm-index gout-decls.thm-index
           :names-to-avoid gout-decls.names-to-avoid
           :vartys (omap::update* gout-decl.vartys gout-decls.vartys))))
    :measure (decl-list-count decls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-label ((label labelp) (gin simpadd0-ginp) state)
    :guard (label-unambp label)
    :returns (mv (new-label labelp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a label."
    (b* (((simpadd0-gin gin) gin))
      (label-case
       label
       :name (mv (label-fix label)
                 (make-simpadd0-gout
                  :events nil
                  :thm-name nil
                  :thm-index gin.thm-index
                  :names-to-avoid gin.names-to-avoid
                  :vartys nil))
       :casexpr (b* (((mv new-expr (simpadd0-gout gout-expr))
                      (simpadd0-const-expr label.expr gin state))
                     (gin (simpadd0-gin-update gin gout-expr))
                     ((mv new-range? (simpadd0-gout gout-range?))
                      (simpadd0-const-expr-option label.range? gin state)))
                  (mv (make-label-casexpr :expr new-expr
                                          :range? new-range?)
                      (make-simpadd0-gout
                       :events (append gout-expr.events gout-range?.events)
                       :thm-name nil
                       :thm-index gout-range?.thm-index
                       :names-to-avoid gout-range?.names-to-avoid
                       :vartys (omap::update* gout-expr.vartys
                                              gout-range?.vartys))))
       :default (mv (label-fix label)
                    (make-simpadd0-gout
                     :events nil
                     :thm-name nil
                     :thm-index gin.thm-index
                     :names-to-avoid gin.names-to-avoid
                     :vartys nil))))
    :measure (label-count label))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-stmt ((stmt stmtp) (gin simpadd0-ginp) state)
    :guard (stmt-unambp stmt)
    :returns (mv (new-stmt stmtp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a statement."
    (b* (((simpadd0-gin gin) gin))
      (stmt-case
       stmt
       :labeled (b* (((mv new-label (simpadd0-gout gout-label))
                      (simpadd0-label stmt.label gin state))
                     (gin (simpadd0-gin-update gin gout-label))
                     ((mv new-stmt (simpadd0-gout gout-stmt))
                      (simpadd0-stmt stmt.stmt gin state)))
                  (mv (make-stmt-labeled :label new-label
                                         :stmt new-stmt)
                      (make-simpadd0-gout
                       :events (append gout-label.events
                                       gout-stmt.events)
                       :thm-name nil
                       :thm-index gout-stmt.thm-index
                       :names-to-avoid gout-stmt.names-to-avoid
                       :vartys (omap::update* gout-label.vartys
                                              gout-stmt.vartys))))
       :compound (b* (((mv new-items (simpadd0-gout gout-items))
                       (simpadd0-block-item-list stmt.items gin state)))
                   (mv (stmt-compound new-items)
                       (make-simpadd0-gout
                        :events gout-items.events
                        :thm-name nil
                        :thm-index gout-items.thm-index
                        :names-to-avoid gout-items.names-to-avoid
                        :vartys gout-items.vartys)))
       :expr (b* (((mv new-expr? (simpadd0-gout gout-expr?))
                   (simpadd0-expr-option stmt.expr? gin state))
                  (gin (simpadd0-gin-update gin gout-expr?)))
               (simpadd0-stmt-expr stmt.expr?
                                   new-expr?
                                   gout-expr?.events
                                   gout-expr?.thm-name
                                   gout-expr?.vartys
                                   gin))
       :if (b* (((mv new-test (simpadd0-gout gout-test))
                 (simpadd0-expr stmt.test gin state))
                (gin (simpadd0-gin-update gin gout-test))
                ((mv new-then (simpadd0-gout gout-then))
                 (simpadd0-stmt stmt.then gin state)))
             (mv (make-stmt-if :test new-test
                               :then new-then)
                 (make-simpadd0-gout
                  :events (append gout-test.events gout-then.events)
                  :thm-name nil
                  :thm-index gout-then.thm-index
                  :names-to-avoid gout-then.names-to-avoid
                  :vartys (omap::update* gout-test.vartys gout-then.vartys))))
       :ifelse (b* (((mv new-test (simpadd0-gout gout-test))
                     (simpadd0-expr stmt.test gin state))
                    (gin (simpadd0-gin-update gin gout-test))
                    ((mv new-then (simpadd0-gout gout-then))
                     (simpadd0-stmt stmt.then gin state))
                    (gin (simpadd0-gin-update gin gout-then))
                    ((mv new-else (simpadd0-gout gout-else))
                     (simpadd0-stmt stmt.else gin state)))
                 (mv (make-stmt-ifelse :test new-test
                                       :then new-then
                                       :else new-else)
                     (make-simpadd0-gout
                      :events (append gout-test.events
                                      gout-then.events
                                      gout-else.events)
                      :thm-name nil
                      :thm-index gout-else.thm-index
                      :names-to-avoid gout-else.names-to-avoid
                      :vartys (omap::update* gout-test.vartys
                                             (omap::update* gout-then.vartys
                                                            gout-else.vartys)))))
       :switch (b* (((mv new-target (simpadd0-gout gout-target))
                     (simpadd0-expr stmt.target gin state))
                    (gin (simpadd0-gin-update gin gout-target))
                    ((mv new-body (simpadd0-gout gout-body))
                     (simpadd0-stmt stmt.body gin state)))
                 (mv (make-stmt-switch :target new-target
                                       :body new-body)
                     (make-simpadd0-gout
                      :events (append gout-target.events gout-body.events)
                      :thm-name nil
                      :thm-index gout-body.thm-index
                      :names-to-avoid gout-body.names-to-avoid
                      :vartys (omap::update* gout-target.vartys
                                             gout-body.vartys))))
       :while (b* (((mv new-test (simpadd0-gout gout-test))
                    (simpadd0-expr stmt.test gin state))
                   (gin (simpadd0-gin-update gin gout-test))
                   ((mv new-body (simpadd0-gout gout-body))
                    (simpadd0-stmt stmt.body gin state)))
                (mv (make-stmt-while :test new-test
                                     :body new-body)
                    (make-simpadd0-gout
                     :events (append gout-test.events gout-body.events)
                     :thm-name nil
                     :thm-index gout-body.thm-index
                     :names-to-avoid gout-body.names-to-avoid
                     :vartys (omap::update* gout-test.vartys gout-body.vartys))))
       :dowhile (b* (((mv new-body (simpadd0-gout gout-body))
                      (simpadd0-stmt stmt.body gin state))
                     (gin (simpadd0-gin-update gin gout-body))
                     ((mv new-test (simpadd0-gout gout-test))
                      (simpadd0-expr stmt.test gin state)))
                  (mv (make-stmt-dowhile :body new-body
                                         :test new-test)
                      (make-simpadd0-gout
                       :events (append gout-body.events gout-test.events)
                       :thm-name nil
                       :thm-index gout-test.thm-index
                       :names-to-avoid gout-test.names-to-avoid
                       :vartys (omap::update* gout-body.vartys gout-test.vartys))))
       :for-expr (b* (((mv new-init (simpadd0-gout gout-init))
                       (simpadd0-expr-option stmt.init gin state))
                      (gin (simpadd0-gin-update gin gout-init))
                      ((mv new-test (simpadd0-gout gout-test))
                       (simpadd0-expr-option stmt.test gin state))
                      (gin (simpadd0-gin-update gin gout-test))
                      ((mv new-next (simpadd0-gout gout-next))
                       (simpadd0-expr-option stmt.next gin state))
                      (gin (simpadd0-gin-update gin gout-next))
                      ((mv new-body (simpadd0-gout gout-body))
                       (simpadd0-stmt stmt.body gin state)))
                   (mv (make-stmt-for-expr :init new-init
                                           :test new-test
                                           :next new-next
                                           :body new-body)
                       (make-simpadd0-gout
                        :events (append gout-init.events
                                        gout-test.events
                                        gout-next.events
                                        gout-body.events)
                        :thm-name nil
                        :thm-index gout-body.thm-index
                        :names-to-avoid gout-body.names-to-avoid
                        :vartys (omap::update* gout-init.vartys
                                               (omap::update*
                                                gout-test.vartys
                                                (omap::update*
                                                 gout-next.vartys
                                                 gout-body.vartys))))))
       :for-decl (b* (((mv new-init (simpadd0-gout gout-init))
                       (simpadd0-decl stmt.init gin state))
                      (gin (simpadd0-gin-update gin gout-init))
                      ((mv new-test (simpadd0-gout gout-test))
                       (simpadd0-expr-option stmt.test gin state))
                      (gin (simpadd0-gin-update gin gout-test))
                      ((mv new-next (simpadd0-gout gout-next))
                       (simpadd0-expr-option stmt.next gin state))
                      (gin (simpadd0-gin-update gin gout-next))
                      ((mv new-body (simpadd0-gout gout-body))
                       (simpadd0-stmt stmt.body gin state)))
                   (mv (make-stmt-for-decl :init new-init
                                           :test new-test
                                           :next new-next
                                           :body new-body)
                       (make-simpadd0-gout
                        :events (append gout-init.events
                                        gout-test.events
                                        gout-next.events
                                        gout-body.events)
                        :thm-name nil
                        :thm-index gout-body.thm-index
                        :names-to-avoid gout-body.names-to-avoid
                        :vartys (omap::update* gout-init.vartys
                                               (omap::update*
                                                gout-test.vartys
                                                (omap::update*
                                                 gout-next.vartys
                                                 gout-body.vartys))))))
       :for-ambig (prog2$ (impossible) (mv (irr-stmt) (irr-simpadd0-gout)))
       :goto (mv (stmt-fix stmt)
                 (make-simpadd0-gout
                  :events nil
                  :thm-name nil
                  :thm-index gin.thm-index
                  :names-to-avoid gin.names-to-avoid
                  :vartys nil))
       :continue (mv (stmt-fix stmt)
                     (make-simpadd0-gout
                      :events nil
                      :thm-name nil
                      :thm-index gin.thm-index
                      :names-to-avoid gin.names-to-avoid
                      :vartys nil))
       :break (mv (stmt-fix stmt)
                  (make-simpadd0-gout
                   :events nil
                   :thm-name nil
                   :thm-index gin.thm-index
                   :names-to-avoid gin.names-to-avoid
                   :vartys nil))
       :return (b* (((mv new-expr? (simpadd0-gout gout-expr?))
                     (simpadd0-expr-option stmt.expr? gin state))
                    (gin (simpadd0-gin-update gin gout-expr?)))
                 (simpadd0-stmt-return stmt.expr?
                                       new-expr?
                                       gout-expr?.events
                                       gout-expr?.thm-name
                                       gout-expr?.vartys
                                       gin))
       :asm (mv (stmt-fix stmt)
                (make-simpadd0-gout
                 :events nil
                 :thm-name nil
                 :thm-index gin.thm-index
                 :names-to-avoid gin.names-to-avoid
                 :vartys nil))))
    :measure (stmt-count stmt))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-block-item ((item block-itemp) (gin simpadd0-ginp) state)
    :guard (block-item-unambp item)
    :returns (mv (new-item block-itemp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a block item."
    (b* (((simpadd0-gin gin) gin))
      (block-item-case
       item
       :decl (b* (((mv new-item (simpadd0-gout gout-item))
                   (simpadd0-decl item.unwrap gin state)))
               (mv (block-item-decl new-item)
                   (make-simpadd0-gout
                    :events gout-item.events
                    :thm-name nil
                    :thm-index gout-item.thm-index
                    :names-to-avoid gout-item.names-to-avoid
                    :vartys gout-item.vartys)))
       :stmt (b* (((mv new-stmt (simpadd0-gout gout-stmt))
                   (simpadd0-stmt item.unwrap gin state))
                  (gin (simpadd0-gin-update gin gout-stmt)))
               (simpadd0-block-item-stmt item.unwrap
                                         new-stmt
                                         gout-stmt.events
                                         gout-stmt.thm-name
                                         gout-stmt.vartys
                                         gin))
       :ambig (prog2$ (impossible) (mv (irr-block-item) (irr-simpadd0-gout)))))
    :measure (block-item-count item))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-block-item-list ((items block-item-listp)
                                    (gin simpadd0-ginp)
                                    state)
    :guard (block-item-list-unambp items)
    :returns (mv (new-items block-item-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of block items."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp items))
          (mv nil (simpadd0-block-item-list-empty gin)))
         ((mv new-item (simpadd0-gout gout-item))
          (simpadd0-block-item (car items) gin state))
         (gin (simpadd0-gin-update gin gout-item))
         ((when (endp (cdr items)))
          (simpadd0-block-item-list-one (block-item-fix (car items))
                                        new-item
                                        gout-item.events
                                        gout-item.thm-name
                                        gout-item.vartys
                                        gin))
         ((mv new-items (simpadd0-gout gout-items))
          (simpadd0-block-item-list (cdr items) gin state))
         (gin (simpadd0-gin-update gin gout-items)))
      (simpadd0-block-item-list-cons (car items)
                                     new-item
                                     gout-item.events
                                     gout-item.thm-name
                                     gout-item.vartys
                                     (cdr items)
                                     new-items
                                     gout-items.events
                                     gout-items.thm-name
                                     gout-items.vartys
                                     gin))
    :measure (block-item-list-count items))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable o< o-finp)))

  :verify-guards nil ; done after the unambiguity proofs

  ///

  (local (in-theory (enable irr-absdeclor
                            irr-dirabsdeclor)))

  (fty::deffixequiv-mutual simpadd0-exprs/decls/stmts)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual exprs/decls-unambp-of-simpadd0-exprs/decls
    (defret expr-unambp-of-simpadd0-expr
      (expr-unambp new-expr)
      :fn simpadd0-expr)
    (defret expr-list-unambp-of-simpadd0-expr-list
      (expr-list-unambp new-exprs)
      :fn simpadd0-expr-list)
    (defret expr-option-unambp-of-simpadd0-expr-option
      (expr-option-unambp new-expr?)
      :fn simpadd0-expr-option)
    (defret const-expr-unambp-of-simpadd0-const-expr
      (const-expr-unambp new-cexpr)
      :fn simpadd0-const-expr)
    (defret const-expr-option-unambp-of-simpadd0-const-expr-option
      (const-expr-option-unambp new-cexpr?)
      :fn simpadd0-const-expr-option)
    (defret genassoc-unambp-of-simpadd0-genassoc
      (genassoc-unambp new-genassoc)
      :fn simpadd0-genassoc)
    (defret genassoc-list-unambp-of-simpadd0-genassoc-list
      (genassoc-list-unambp new-genassocs)
      :fn simpadd0-genassoc-list)
    (defret member-designor-unambp-of-simpadd0-member-designor
      (member-designor-unambp new-memdes)
      :fn simpadd0-member-designor)
    (defret type-spec-unambp-of-simpadd0-type-spec
      (type-spec-unambp new-tyspec)
      :fn simpadd0-type-spec)
    (defret spec/qual-unambp-of-simpadd0-spec/qual
      (spec/qual-unambp new-specqual)
      :fn simpadd0-spec/qual)
    (defret spec/qual-list-unambp-of-simpadd0-spec/qual-list
      (spec/qual-list-unambp new-specquals)
      :fn simpadd0-spec/qual-list)
    (defret align-spec-unambp-of-simpadd0-align-spec
      (align-spec-unambp new-alignspec)
      :fn simpadd0-align-spec)
    (defret decl-spec-unambp-of-simpadd0-decl-spec
      (decl-spec-unambp new-declspec)
      :fn simpadd0-decl-spec)
    (defret decl-spec-list-unambp-of-simpadd0-decl-spec-list
      (decl-spec-list-unambp new-declspecs)
      :fn simpadd0-decl-spec-list)
    (defret initer-unambp-of-simpadd0-initer
      (initer-unambp new-initer)
      :fn simpadd0-initer)
    (defret initer-option-unambp-of-simpadd0-initer-option
      (initer-option-unambp new-initer?)
      :fn simpadd0-initer-option)
    (defret desiniter-unambp-of-simpadd0-desiniter
      (desiniter-unambp new-desiniter)
      :fn simpadd0-desiniter)
    (defret desiniter-list-unambp-of-simpadd0-desiniter-list
      (desiniter-list-unambp new-desiniters)
      :fn simpadd0-desiniter-list)
    (defret designor-unambp-of-simpadd0-designor
      (designor-unambp new-designor)
      :fn simpadd0-designor)
    (defret designor-list-unambp-of-simpadd0-designor-list
      (designor-list-unambp new-designors)
      :fn simpadd0-designor-list)
    (defret declor-unambp-of-simpadd0-declor
      (declor-unambp new-declor)
      :fn simpadd0-declor)
    (defret declor-option-unambp-of-simpadd0-declor-option
      (declor-option-unambp new-declor?)
      :fn simpadd0-declor-option)
    (defret dirdeclor-unambp-of-simpadd0-dirdeclor
      (dirdeclor-unambp new-dirdeclor)
      :fn simpadd0-dirdeclor)
    (defret absdeclor-unambp-of-simpadd0-absdeclor
      (absdeclor-unambp new-absdeclor)
      :fn simpadd0-absdeclor)
    (defret absdeclor-option-unambp-of-simpadd0-absdeclor-option
      (absdeclor-option-unambp new-absdeclor?)
      :fn simpadd0-absdeclor-option)
    (defret dirabsdeclor-unambp-of-simpadd0-dirabsdeclor
      (dirabsdeclor-unambp new-dirabsdeclor)
      :fn simpadd0-dirabsdeclor)
    (defret dirabsdeclor-option-unambp-of-simpadd0-dirabsdeclor-option
      (dirabsdeclor-option-unambp new-dirabsdeclor?)
      :fn simpadd0-dirabsdeclor-option)
    (defret param-declon-unambp-of-simpadd0-param-declon
      (param-declon-unambp new-paramdecl)
      :fn simpadd0-param-declon)
    (defret param-declon-list-unambp-of-simpadd0-param-declon-list
      (param-declon-list-unambp new-paramdecls)
      :fn simpadd0-param-declon-list)
    (defret param-declor-unambp-of-simpadd0-param-declor
      (param-declor-unambp new-paramdeclor)
      :fn simpadd0-param-declor)
    (defret tyname-unambp-of-simpadd0-tyname
      (tyname-unambp new-tyname)
      :fn simpadd0-tyname)
    (defret struni-spec-unambp-of-simpadd0-struni-spec
      (struni-spec-unambp new-struni-spec)
      :fn simpadd0-struni-spec)
    (defret structdecl-unambp-of-simpadd0-structdecl
      (structdecl-unambp new-structdecl)
      :fn simpadd0-structdecl)
    (defret structdecl-list-unambp-of-simpadd0-structdecl-list
      (structdecl-list-unambp new-structdecls)
      :fn simpadd0-structdecl-list)
    (defret structdeclor-unambp-of-simpadd0-structdeclor
      (structdeclor-unambp new-structdeclor)
      :fn simpadd0-structdeclor)
    (defret structdeclor-list-unambp-of-simpadd0-structdeclor-list
      (structdeclor-list-unambp new-structdeclors)
      :fn simpadd0-structdeclor-list)
    (defret enumspec-unambp-of-simpadd0-enumspec
      (enumspec-unambp new-enumspec)
      :fn simpadd0-enumspec)
    (defret enumer-unambp-of-simpadd0-enumer
      (enumer-unambp new-enumer)
      :fn simpadd0-enumer)
    (defret enumer-list-unambp-of-simpadd0-enumer-list
      (enumer-list-unambp new-enumers)
      :fn simpadd0-enumer-list)
    (defret statassert-unambp-of-simpadd0-statassert
      (statassert-unambp new-statassert)
      :fn simpadd0-statassert)
    (defret initdeclor-unambp-of-simpadd0-initdeclor
      (initdeclor-unambp new-initdeclor)
      :fn simpadd0-initdeclor)
    (defret initdeclor-list-unambp-of-simpadd0-initdeclor-list
      (initdeclor-list-unambp new-initdeclors)
      :fn simpadd0-initdeclor-list)
    (defret decl-unambp-of-simpadd0-decl
      (decl-unambp new-decl)
      :fn simpadd0-decl)
    (defret decl-list-unambp-of-simpadd0-decl-list
      (decl-list-unambp new-decls)
      :fn simpadd0-decl-list)
    (defret label-unambp-of-simpadd0-label
      (label-unambp new-label)
      :fn simpadd0-label)
    (defret stmt-unambp-of-simpadd0-stmt
      (stmt-unambp new-stmt)
      :fn simpadd0-stmt)
    (defret block-item-unambp-of-simpadd0-block-item
      (block-item-unambp new-item)
      :fn simpadd0-block-item)
    (defret block-item-list-unambp-of-simpadd0-block-item-list
      (block-item-list-unambp new-items)
      :fn simpadd0-block-item-list)
    :hints (("Goal" :in-theory (enable simpadd0-expr
                                       simpadd0-expr-list
                                       simpadd0-expr-option
                                       simpadd0-const-expr
                                       simpadd0-const-expr-option
                                       simpadd0-genassoc
                                       simpadd0-genassoc-list
                                       simpadd0-type-spec
                                       simpadd0-spec/qual
                                       simpadd0-spec/qual-list
                                       simpadd0-align-spec
                                       simpadd0-decl-spec
                                       simpadd0-decl-spec-list
                                       simpadd0-initer
                                       simpadd0-initer-option
                                       simpadd0-desiniter
                                       simpadd0-desiniter-list
                                       simpadd0-designor
                                       simpadd0-designor-list
                                       simpadd0-declor
                                       simpadd0-declor-option
                                       simpadd0-dirdeclor
                                       simpadd0-absdeclor
                                       simpadd0-absdeclor-option
                                       simpadd0-dirabsdeclor
                                       simpadd0-dirabsdeclor-option
                                       simpadd0-param-declon
                                       simpadd0-param-declon-list
                                       simpadd0-param-declor
                                       simpadd0-tyname
                                       simpadd0-struni-spec
                                       simpadd0-structdecl
                                       simpadd0-structdecl-list
                                       simpadd0-structdeclor
                                       simpadd0-structdeclor-list
                                       simpadd0-enumspec
                                       simpadd0-enumer
                                       simpadd0-enumer-list
                                       simpadd0-statassert
                                       simpadd0-initdeclor
                                       simpadd0-initdeclor-list
                                       simpadd0-decl
                                       simpadd0-decl-list
                                       simpadd0-label
                                       simpadd0-stmt
                                       simpadd0-block-item
                                       simpadd0-block-item-list
                                       irr-expr
                                       irr-const-expr
                                       irr-align-spec
                                       irr-dirabsdeclor
                                       irr-param-declor
                                       irr-type-spec
                                       irr-stmt
                                       irr-block-item))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards simpadd0-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-fundef ((fundef fundefp) (gin simpadd0-ginp) state)
  :guard (fundef-unambp fundef)
  :returns (mv (new-fundef fundefp)
               (gout simpadd0-goutp))
  :short "Transform a function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a theorem for the function
     only under certain conditions,
     including the fact that a theorem for the body was generated.")
   (xdoc::p
    "The generated theorem contains local theorems
     that are used in the proof of the main theorem.
     The local theorems are about the initial scope of the function,
     and about the parameters in the computation state
     at the beginning of the execution of the function body."))
  (b* (((fundef fundef) fundef)
       ((mv new-spec (simpadd0-gout gout-spec))
        (simpadd0-decl-spec-list fundef.spec gin state))
       (gin (simpadd0-gin-update gin gout-spec))
       ((mv new-declor (simpadd0-gout gout-declor))
        (simpadd0-declor fundef.declor gin state))
       (gin (simpadd0-gin-update gin gout-declor))
       ((mv new-decls (simpadd0-gout gout-decls))
        (simpadd0-decl-list fundef.decls gin state))
       (gin (simpadd0-gin-update gin gout-decls))
       ((unless (stmt-case fundef.body :compound))
        (raise "Internal error: the body of ~x0 is not a compound statement."
               (fundef-fix fundef))
        (mv (irr-fundef) (irr-simpadd0-gout)))
       (items (stmt-compound->items fundef.body))
       ((mv new-items (simpadd0-gout gout-body))
        (simpadd0-block-item-list items gin state))
       ((simpadd0-gin gin) (simpadd0-gin-update gin gout-body))
       (new-body (stmt-compound new-items))
       (new-fundef (make-fundef :extension fundef.extension
                                :spec new-spec
                                :declor new-declor
                                :asm? fundef.asm?
                                :attribs fundef.attribs
                                :decls new-decls
                                :body new-body))
       (gout-no-thm
        (make-simpadd0-gout
         :events (append gout-spec.events
                         gout-declor.events
                         gout-decls.events
                         gout-body.events)
         :thm-name nil
         :thm-index gin.thm-index
         :names-to-avoid gin.names-to-avoid
         :vartys (omap::update*
                  gout-spec.vartys
                  (omap::update* gout-declor.vartys
                                 (omap::update* gout-decls.vartys
                                                gout-body.vartys)))))
       ((unless gout-body.thm-name)
        (mv new-fundef gout-no-thm))
       ((unless (fundef-formalp fundef))
        (mv new-fundef gout-no-thm))
       ((declor declor) fundef.declor)
       ((when (consp declor.pointers))
        (mv new-fundef gout-no-thm))
       ((mv okp params dirdeclor)
        (dirdeclor-case
         declor.direct
         :function-params (mv t declor.direct.params declor.direct.declor)
         :function-names (mv (endp declor.direct.names)
                             nil
                             declor.direct.declor)
         :otherwise (mv nil nil (irr-dirdeclor))))
       ((unless okp)
        (mv new-fundef gout-no-thm))
       ((unless (dirdeclor-case dirdeclor :ident))
        (raise "Internal error: ~x0 is not just the function name."
               dirdeclor)
        (mv (irr-fundef) (irr-simpadd0-gout)))
       (fun (ident->unwrap (dirdeclor-ident->ident dirdeclor)))
       ((unless (stringp fun))
        (raise "Internal error: non-string identifier ~x0." fun)
        (mv (irr-fundef) (irr-simpadd0-gout)))
       ((mv erp ldm-params) (ldm-param-declon-list params))
       ((when erp) (mv new-fundef gout-no-thm))
       (type? (block-item-list-type items))
       (type (or type? (type-void)))
       ((unless (type-formalp type))
        (raise "Internal error: function ~x0 returns ~x1."
               (fundef-fix fundef) type)
        (mv (irr-fundef) (irr-simpadd0-gout)))
       ((mv & ctype) (ldm-type type)) ; ERP is NIL because TYPE-FORMALP holds
       ((mv okp args parargs arg-types arg-types-compst)
        (simpadd0-gen-from-params ldm-params gin))
       ((unless okp) (mv new-fundef gout-no-thm))
       ((mv init-scope-thm-event init-scope-thm-name)
        (simpadd0-gen-init-scope-thm ldm-params args parargs arg-types))
       ((mv param-thm-events param-thm-names)
        (simpadd0-gen-param-thms
         args arg-types-compst arg-types ldm-params args))
       (thm-name (packn-pos (list gin.const-new '-thm- gin.thm-index)
                            gin.const-new))
       (thm-index (1+ gin.thm-index))
       (formula
        `(b* ((old ',(fundef-fix fundef))
              (new ',new-fundef)
              (fun (mv-nth 1 (ldm-ident (ident ,fun))))
              ((mv old-result old-compst)
               (c::exec-fun fun (list ,@args) compst old-fenv limit))
              ((mv new-result new-compst)
               (c::exec-fun fun (list ,@args) compst new-fenv limit)))
           (implies (and ,@arg-types
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
                         ,@(if (type-case type :void)
                               '((not old-result))
                             `(old-result
                               (equal (c::type-of-value old-result)
                                      ',ctype)))))))
       (hints
        `(("Goal"
           :expand ((c::exec-fun
                     ',(c::ident fun) (list ,@args) compst old-fenv limit)
                    (c::exec-fun
                     ',(c::ident fun) (list ,@args) compst new-fenv limit))
           :use (,init-scope-thm-name
                 ,@(simpadd0-fundef-loop param-thm-names fun)
                 (:instance ,gout-body.thm-name
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
                        (:e ldm-block-item-list)
                        (:e ldm-fundef)
                        (:e ldm-ident)
                        (:e ldm-type)
                        (:e ldm-block-item-list)
                        (:e c::tyname-to-type)
                        (:e c::block-item-list-nocallsp)
                        c::errorp-of-error))))
       (thm-event `(defruled ,thm-name
                     ,formula
                     :hints ,hints
                     :prep-lemmas (,init-scope-thm-event
                                   ,@param-thm-events))))
    (mv new-fundef
        (make-simpadd0-gout
         :events (append gout-spec.events
                         gout-declor.events
                         gout-decls.events
                         gout-body.events
                         (list thm-event))
         :thm-name thm-name
         :thm-index thm-index
         :names-to-avoid (cons thm-name gout-body.names-to-avoid)
         :vartys (omap::update*
                  gout-spec.vartys
                  (omap::update* gout-declor.vartys
                                 (omap::update* gout-decls.vartys
                                                gout-body.vartys))))))
  :hooks (:fix)

  :prepwork
  ((define simpadd0-fundef-loop ((thms symbol-listp) (fun stringp))
     :returns (lemma-instances true-listp)
     :parents nil
     (b* (((when (endp thms)) nil)
          (thm (car thms))
          (lemma-instance
           `(:instance ,thm
                       (fun (mv-nth 1 (ldm-ident (ident ,fun))))
                       (compst0 compst)))
          (more-lemma-instances
           (simpadd0-fundef-loop (cdr thms) fun)))
       (cons lemma-instance more-lemma-instances))))

  ///

  (defret fundef-unambp-of-simpadd0-fundef
    (fundef-unambp new-fundef)
    :hints (("Goal" :in-theory (enable (:e irr-fundef))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-extdecl ((extdecl extdeclp) (gin simpadd0-ginp) state)
  :guard (extdecl-unambp extdecl)
  :returns (mv (new-extdecl extdeclp)
               (gout simpadd0-goutp))
  :short "Transform an external declaration."
  (b* (((simpadd0-gin gin) gin))
    (extdecl-case
     extdecl
     :fundef (b* (((mv new-fundef (simpadd0-gout gout-fundef))
                   (simpadd0-fundef extdecl.unwrap gin state)))
               (mv (extdecl-fundef new-fundef)
                   (make-simpadd0-gout
                    :events gout-fundef.events
                    :thm-name nil
                    :thm-index gout-fundef.thm-index
                    :names-to-avoid gout-fundef.names-to-avoid
                    :vartys gout-fundef.vartys)))
     :decl (b* (((mv new-decl (simpadd0-gout gout-decl))
                 (simpadd0-decl extdecl.unwrap gin state)))
             (mv (extdecl-decl new-decl)
                 (make-simpadd0-gout
                  :events gout-decl.events
                  :thm-name nil
                  :thm-index gout-decl.thm-index
                  :names-to-avoid gout-decl.names-to-avoid
                  :vartys gout-decl.vartys)))
     :empty (mv (extdecl-empty)
                (make-simpadd0-gout
                 :events nil
                 :thm-name nil
                 :thm-index gin.thm-index
                 :names-to-avoid gin.names-to-avoid
                 :vartys nil))
     :asm (mv (extdecl-fix extdecl)
              (make-simpadd0-gout
               :events nil
               :thm-name nil
               :thm-index gin.thm-index
               :names-to-avoid gin.names-to-avoid
               :vartys nil))))
  :hooks (:fix)

  ///

  (defret extdecl-unambp-of-simpadd0-extdecl
    (extdecl-unambp new-extdecl)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-extdecl-list ((extdecls extdecl-listp)
                               (gin simpadd0-ginp)
                               state)
  :guard (extdecl-list-unambp extdecls)
  :returns (mv (new-extdecls extdecl-listp)
               (gout simpadd0-goutp))
  :short "Transform a list of external declarations."
  (b* (((simpadd0-gin gin) gin)
       ((when (endp extdecls))
        (mv nil
            (make-simpadd0-gout
             :events nil
             :thm-name nil
             :thm-index gin.thm-index
             :names-to-avoid gin.names-to-avoid
             :vartys nil)))
       ((mv new-edecl (simpadd0-gout gout-edecl))
        (simpadd0-extdecl (car extdecls) gin state))
       (gin (simpadd0-gin-update gin gout-edecl))
       ((mv new-edecls (simpadd0-gout gout-edecls))
        (simpadd0-extdecl-list (cdr extdecls) gin state)))
    (mv (cons new-edecl new-edecls)
        (make-simpadd0-gout
         :events (append gout-edecl.events gout-edecls.events)
         :thm-name nil
         :thm-index gout-edecls.thm-index
         :names-to-avoid gout-edecls.names-to-avoid
         :vartys (omap::update* gout-edecl.vartys gout-edecls.vartys))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret extdecl-list-unambp-of-simpadd0-extdecl-list
    (extdecl-list-unambp new-extdecls)
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-transunit ((tunit transunitp) (gin simpadd0-ginp) state)
  :guard (transunit-unambp tunit)
  :returns (mv (new-tunit transunitp)
               (gout simpadd0-goutp))
  :short "Transform a translation unit."
  (b* (((simpadd0-gin gin) gin)
       ((transunit tunit) tunit)
       ((mv new-decls (simpadd0-gout gout-decls))
        (simpadd0-extdecl-list tunit.decls gin state)))
    (mv  (make-transunit :decls new-decls
                         :info tunit.info)
         (make-simpadd0-gout
          :events gout-decls.events
          :thm-name nil
          :thm-index gout-decls.thm-index
          :names-to-avoid gout-decls.names-to-avoid
          :vartys gout-decls.vartys)))
  :hooks (:fix)

  ///

  (defret transunit-unambp-of-simpadd0-transunit
    (transunit-unambp new-tunit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-filepath-transunit-map ((map filepath-transunit-mapp)
                                         (gin simpadd0-ginp)
                                         state)
  :guard (filepath-transunit-map-unambp map)
  :returns (mv (new-map filepath-transunit-mapp
                        :hyp (filepath-transunit-mapp map))
               (gout simpadd0-goutp))
  :short "Transform a map from file paths to translation units."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform both the file paths and the translation units."))
  (b* (((simpadd0-gin gin) gin)
       ((when (omap::emptyp map))
        (mv nil
            (make-simpadd0-gout
             :events nil
             :thm-name nil
             :thm-index gin.thm-index
             :names-to-avoid gin.names-to-avoid
             :vartys nil)))
       ((mv path tunit) (omap::head map))
       ((mv new-tunit (simpadd0-gout gout-tunit))
        (simpadd0-transunit tunit gin state))
       (gin (simpadd0-gin-update gin gout-tunit))
       ((mv new-map (simpadd0-gout gout-map))
        (simpadd0-filepath-transunit-map (omap::tail map) gin state)))
    (mv (omap::update path new-tunit new-map)
        (make-simpadd0-gout
         :events (append gout-tunit.events gout-map.events)
         :thm-name nil
         :thm-index gout-map.thm-index
         :names-to-avoid gout-map.names-to-avoid
         :vartys (omap::update* gout-tunit.vartys gout-map.vartys))))
  :verify-guards :after-returns

  ///

  (fty::deffixequiv simpadd0-filepath-transunit-map
    :args ((gin simpadd0-ginp)))

  (defret filepath-transunit-map-unambp-of-simpadd0-filepath-transunit-map
    (filepath-transunit-map-unambp new-map)
    :hyp (filepath-transunit-mapp map)
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-transunit-ensemble ((tunits transunit-ensemblep)
                                     (gin simpadd0-ginp)
                                     state)
  :guard (transunit-ensemble-unambp tunits)
  :returns (mv (new-tunits transunit-ensemblep)
               (gout simpadd0-goutp))
  :short "Transform a translation unit ensemble."
  (b* (((transunit-ensemble tunits) tunits)
       ((mv new-map (simpadd0-gout gout-map))
        (simpadd0-filepath-transunit-map tunits.unwrap gin state)))
    (mv (transunit-ensemble new-map)
        (make-simpadd0-gout
         :events gout-map.events
         :thm-name nil
         :thm-index gout-map.thm-index
         :names-to-avoid gout-map.names-to-avoid
         :vartys gout-map.vartys)))
  :hooks (:fix)

  ///

  (defret transunit-ensemble-unambp-of-simpadd0-transunit-ensemble
    (transunit-ensemble-unambp new-tunits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-code-ensemble ((code code-ensemblep)
                                (gin simpadd0-ginp)
                                state)
  :guard (code-ensemble-unambp code)
  :returns (mv (new-code code-ensemblep)
               (gout simpadd0-goutp))
  :short "Transform a code ensemble."
  (b* (((code-ensemble code) code)
       ((mv tunits-new (simpadd0-gout gout))
        (simpadd0-transunit-ensemble code.transunits gin state)))
    (mv (change-code-ensemble code :transunits tunits-new) gout))
  :hooks (:fix)

  ///

  (defret code-ensemble-unambp-of-simpadd0-code-ensemble
    (code-ensemble-unambp new-code)
    :hints
    (("Goal" :in-theory (enable c$::code-ensemble-unambp-of-code-ensemble)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-everything ((code-old code-ensemblep)
                                 (const-new symbolp)
                                 state)
  :guard (and (code-ensemble-unambp code-old)
              (code-ensemble-annop code-old))
  :returns (mv erp (event pseudo-event-formp))
  :short "Event expansion of the transformation."
  (b* (((reterr) '(_))
       (gin (make-simpadd0-gin :const-new const-new
                               :thm-index 1
                               :names-to-avoid nil))
       ((mv code-new (simpadd0-gout gout))
        (simpadd0-code-ensemble code-old gin state))
       (const-event `(defconst ,const-new ',code-new)))
    (retok `(encapsulate () ,const-event ,@gout.events))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-process-inputs-and-gen-everything (const-old
                                                    const-new
                                                    state)
  :returns (mv erp (event pseudo-event-formp))
  :parents (simpadd0-implementation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((erp code-old const-new)
        (simpadd0-process-inputs const-old const-new (w state))))
    (simpadd0-gen-everything code-old const-new state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-fn (const-old const-new (ctx ctxp) state)
  :returns (mv erp (event pseudo-event-formp) state)
  :parents (simpadd0-implementation)
  :short "Event expansion of @(tsee simpadd0)."
  (b* (((mv erp event)
        (simpadd0-process-inputs-and-gen-everything const-old
                                                    const-new
                                                    state))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection simpadd0-macro-definition
  :parents (simpadd0-implementation)
  :short "Definition of the @(tsee simpadd0) macro."
  (defmacro simpadd0 (const-old const-new)
    `(make-event
      (simpadd0-fn ',const-old ',const-new 'simpadd0 state))))
