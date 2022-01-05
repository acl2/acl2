; Yul Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "renaming-variables")
(include-book "unique-variables")

(include-book "../language/static-safety-checking")

(local (include-book "../library-extensions/omaps"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ disambiguator-variables-safety
  :parents (disambiguator)
  :short "Proof that
          the part of the @('Disambiguator') transformation for variables
          preserves the static safety checks."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in @(see renaming-variables),
     the renaming omap consists of
     the variables in scope for the old code (the keys of the omap) and
     the variables in scope for the new code (the values of the omap).
     Thus, we prove theorems saying that
     if two pieces of code are related by variable renaming,
     and the old code is safe with respect to
     the variables that are the keys of the renaming omap,
     then the new code is safe with respect to
     the variables that are the values of the renaming omap;
     furthermore, if the renaming omap is updated,
     the updated variables in scope are still the keys and values,
     for the old and new code;
     furthermore, if the static safety checks
     return information other than updated variables in scope
     (e.g. modes, or numbers of values),
     that information is the same for old and new code.
     For certain constructs (e.g. statements),
     the theorems have additional hypotheses saying that
     the new code has unique variables
     and that the keys in the renaming omap are
     a subset of all the variables encountered so far
     that are passed as input to @('...-unique-vars') functions.")
   (xdoc::p
    "The above is just a sketch.
     Things are explained in more detail below."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define varset-old ((ren identifier-identifier-mapp))
  :returns (varset identifier-setp)
  :short "Variables in scope for the old code in variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "This explicates the fact that, as mentioned in @(see renaming-variables),
     the keys of a renaming map are the variables in scope for the old code.")
   (xdoc::p
    "Also see @(tsee varset-new)."))
  (omap::keys (identifier-identifier-map-fix ren))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define varset-new ((ren identifier-identifier-mapp))
  :returns (varset identifier-setp)
  :short "Variables in scope for the new code in variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "This explicates the fact that, as mentioned in @(see renaming-variables),
     the values of a renaming map are the variables in scope for the old code.")
   (xdoc::p
    "Also see @(tsee varset-old)."))
  (omap::values (identifier-identifier-map-fix ren))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection varset-old/new-of-add-var/vars-to-var-renaming
  :short "Theorems about @(tsee varset-old) and @(tsee varset-new)
          applied to
          @(tsee add-var-to-var-renaming) and @(tsee add-vars-to-var-renaming)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These explicate the updated variables in scope
     when the renaming map is extended."))

  (defrule varset-old-of-add-var-to-var-renaming
    (b* ((ren1 (add-var-to-var-renaming old new ren)))
      (implies (not (resulterrp ren1))
               (equal (varset-old ren1)
                      (set::insert (identifier-fix old)
                                   (varset-old ren)))))
    :enable (add-var-to-var-renaming
             varset-old))

  (defrule varset-old-of-add-vars-to-var-renaming
    (b* ((ren1 (add-vars-to-var-renaming old new ren)))
      (implies (and (not (resulterrp ren1))
                    (identifier-listp old))
               (equal (varset-old ren1)
                      (set::list-insert old (varset-old ren)))))
    :enable (add-vars-to-var-renaming
             set::list-insert))

  (defrule varset-new-of-add-var-to-var-renaming
    (b* ((ren1 (add-var-to-var-renaming old new ren)))
      (implies (not (resulterrp ren1))
               (equal (varset-new ren1)
                      (set::insert (identifier-fix new)
                                   (varset-new ren)))))
    :enable (add-var-to-var-renaming
             varset-new))

  (defrule varset-new-of-add-vars-to-var-renaming
    (b* ((ren1 (add-vars-to-var-renaming old new ren)))
      (implies (and (not (resulterrp ren1))
                    (identifier-listp new))
               (equal (varset-new ren1)
                      (set::list-insert new (varset-new ren)))))
    :enable (add-vars-to-var-renaming
             set::list-insert)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled check-var-when-var-renamevar
  :short "If a variable is in scope for the old code,
          its renamed counterpart is in scope for the new code."
  (implies (and (not (resulterrp (var-renamevar old new ren)))
                (check-var old (varset-old ren)))
           (check-var new (varset-new ren)))
  :enable (var-renamevar
           check-var
           varset-new
           omap::in-values-when-in))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection check-safe-path/paths-when-path/paths-renamevar
  :short "If two (lists of) paths are related by variable renaming,
          the safety of the old one implies the safety of the new one."

  (defruled check-safe-path-when-path-renamevar
    (implies (not (resulterrp (path-renamevar old new ren)))
             (b* ((ok-old (check-safe-path old (varset-old ren)))
                  (ok-new (check-safe-path new (varset-new ren))))
               (implies (not (resulterrp ok-old))
                        (not (resulterrp ok-new)))))
    :enable (path-renamevar
             check-safe-path
             check-var-when-var-renamevar))

  (defruled check-safe-path-list-when-path-list-renamevar
    (implies (not (resulterrp (path-list-renamevar old new ren)))
             (b* ((ok-old (check-safe-path-list old (varset-old ren)))
                  (ok-new (check-safe-path-list new (varset-new ren))))
               (implies (not (resulterrp ok-old))
                        (not (resulterrp ok-new)))))
    :enable (path-list-renamevar
             check-safe-path-list
             check-safe-path-when-path-renamevar)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection add-var/vars-not-error-when-var/vars-unique-vars-of-larger
  :short "Variables that are unique may be safely added
          to any subset of the variables encountered so far."

  (defruled add-var-not-error-when-var-unique-vars-of-larger
    (implies (and (not (resulterrp (var-unique-vars var allvars)))
                  (set::subset (identifier-set-fix varset)
                               (identifier-set-fix allvars)))
             (not (resulterrp (add-var var varset))))
    :enable (var-unique-vars
             add-var
             not-resulterrp-when-identifier-setp
             set::subset-in-2))

  (defruled add-vars-not-error-when-var-list-unique-vars-of-larger
    (implies (and (not (resulterrp (var-list-unique-vars vars allvars)))
                  (set::subset (identifier-set-fix varset)
                               (identifier-set-fix allvars)))
             (not (resulterrp (add-vars vars varset))))
    :enable (var-list-unique-vars
             add-vars
             add-var-not-error-when-var-unique-vars-of-larger
             var-unique-vars-to-set-insert
             add-var-to-set-insert
             not-resulterrp-when-identifier-setp
             set::subset-transitive)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection renaming-variables-expression-safety
  :short "Proof that variable renaming preserves the safety of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "If two expressions are related by variable renaming,
     and the old expression is safe,
     then the new expression is also safe,
     and it returns the same number of values as the old one.
     This is proved via
     the induction schema on two expressions simultaneously;
     it also involves lists of expressions and function calls.
     The renaming map is not updated here,
     because expressions do not introduce new variables."))

  (local (include-book "../language/abstract-syntax-induction-schemas"))

  (local
   (defthm-expressions-induction2-flag

     (defthm theorem-for-expression-induct2
       (implies (not (resulterrp (expression-renamevar old new ren)))
                (b* ((n-old (check-safe-expression old
                                                   (varset-old ren)
                                                   funtab))
                     (n-new (check-safe-expression new
                                                   (varset-new ren)
                                                   funtab)))
                  (implies (not (resulterrp n-old))
                           (and (not (resulterrp n-new))
                                (equal n-new n-old)))))
       :flag expression-induct2)

     (defthm theorem-for-expression-list-induct2
       (implies (not (resulterrp (expression-list-renamevar old new ren)))
                (b* ((n-old (check-safe-expression-list old
                                                        (varset-old ren)
                                                        funtab))
                     (n-new (check-safe-expression-list new
                                                        (varset-new ren)
                                                        funtab)))
                  (implies (not (resulterrp n-old))
                           (and (not (resulterrp n-new))
                                (equal n-new n-old)))))
       :flag expression-list-induct2)

     (defthm theorem-for-funcall-induct2
       (implies (not (resulterrp (funcall-renamevar old new ren)))
                (b* ((n-old (check-safe-funcall old (varset-old ren) funtab))
                     (n-new (check-safe-funcall new (varset-new ren) funtab)))
                  (implies (not (resulterrp n-old))
                           (and (not (resulterrp n-new))
                                (equal n-new n-old)))))
       :flag funcall-induct2)

     :hints (("Goal"
              :in-theory (enable expression-renamevar
                                 expression-list-renamevar
                                 funcall-renamevar
                                 check-safe-expression
                                 check-safe-expression-list
                                 check-safe-funcall
                                 check-safe-path-when-path-renamevar)))))

  (defrule check-safe-expression-when-renamevar
    (implies (not (resulterrp (expression-renamevar old new ren)))
             (b* ((n-old (check-safe-expression old
                                                (varset-old ren)
                                                funtab))
                  (n-new (check-safe-expression new
                                                (varset-new ren)
                                                funtab)))
               (implies (not (resulterrp n-old))
                        (and (not (resulterrp n-new))
                             (equal n-new n-old))))))

  (defrule check-safe-expression-list-when-renamevar
    (implies (not (resulterrp (expression-list-renamevar old new ren)))
             (b* ((n-old (check-safe-expression-list old
                                                     (varset-old ren)
                                                     funtab))
                  (n-new (check-safe-expression-list new
                                                     (varset-new ren)
                                                     funtab)))
               (implies (not (resulterrp n-old))
                        (and (not (resulterrp n-new))
                             (equal n-new n-old))))))

  (defrule check-safe-funcall-when-renamevar
    (implies (not (resulterrp (funcall-renamevar old new ren)))
             (b* ((n-old (check-safe-funcall old (varset-old ren) funtab))
                  (n-new (check-safe-funcall new (varset-new ren) funtab)))
               (implies (not (resulterrp n-old))
                        (and (not (resulterrp n-new))
                             (equal n-new n-old)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection check-safe-subset-unique-vars
  :short "Variable subset preservation for
          safe statements with unique variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "If a statement has unique variables and is safe,
    and the variables in scope are a subset of
    all the ones encountered so far in checking uniqueness,
    then this subset relation is preserved for
    the updates variables in scope after the statement
    the updates variables encoutneres so far after the statement.
    The same applies to lists of statements.")
   (xdoc::p
    "This is proved via a custom induction scheme
     based on the safety check functions and the unqueness check functions."))

  (local
   (defines induction

     (define statement-induct ((stmt statementp)
                               (varset identifier-setp)
                               (funtab funtablep)
                               (allvars identifier-setp))
       (statement-case
        stmt
        :block (block-induct stmt.get varset funtab allvars)
        :variable-single nil
        :variable-multi nil
        :assign-single nil
        :assign-multi nil
        :funcall nil
        :if (block-induct stmt.body varset funtab allvars)
        :for (b* ((stmts (block->statements stmt.init))
                  ((ok funtab1) (add-funtypes (statements-to-fundefs stmts)
                                              funtab))
                  ((ok varsmodes) (check-safe-statement-list stmts
                                                             varset
                                                             funtab))
                  (varset1 (vars+modes->vars varsmodes))
                  ((ok allvars1) (statement-list-unique-vars stmts allvars))
                  ((ok allvars2) (block-unique-vars stmt.update allvars1)))
               (list (statement-list-induct stmts varset funtab allvars)
                     (block-induct stmt.update varset1 funtab1 allvars1)
                     (block-induct stmt.body varset1 funtab1 allvars2)))
        :switch (b* (((ok allvars1) (swcase-list-unique-vars stmt.cases
                                                             allvars)))
                  (list (swcase-list-induct stmt.cases varset funtab allvars)
                        (block-option-induct stmt.default
                                             varset
                                             funtab
                                             allvars1)))
        :leave nil
        :break nil
        :continue nil
        :fundef (fundef-induct stmt.get funtab allvars))
       :measure (statement-count stmt))

     (define statement-list-induct ((stmts statement-listp)
                                    (varset identifier-setp)
                                    (funtab funtablep)
                                    (allvars identifier-setp))
       (b* (((when (endp stmts)) nil)
            ((ok varsmodes) (check-safe-statement (car stmts) varset funtab))
            (varset1 (vars+modes->vars varsmodes))
            ((ok allvars1) (statement-unique-vars (car stmts) allvars)))
         (list (statement-induct (car stmts) varset funtab allvars)
               (statement-list-induct (cdr stmts) varset1 funtab allvars1)))
       :measure (statement-list-count stmts))

     (define block-induct ((block blockp)
                           (varset identifier-setp)
                           (funtab funtablep)
                           (allvars identifier-setp))
       (b* ((stmts (block->statements block))
            ((ok funtab1) (add-funtypes (statements-to-fundefs stmts) funtab)))
         (list (statement-list-induct stmts varset funtab1 allvars)))
       :measure (block-count block))

     (define block-option-induct ((block? block-optionp)
                                  (varset identifier-setp)
                                  (funtab funtablep)
                                  (allvars identifier-setp))
       (block-option-case
        block?
        :none nil
        :some (block-induct
               (block-option-some->val block?) varset funtab allvars))
       :measure (block-option-count block?))

     (define swcase-induct ((case swcasep)
                            (varset identifier-setp)
                            (funtab funtablep)
                            (allvars identifier-setp))
       (block-induct (swcase->body case) varset funtab allvars)
       :measure (swcase-count case))

     (define swcase-list-induct ((cases swcase-listp)
                                 (varset identifier-setp)
                                 (funtab funtablep)
                                 (allvars identifier-setp))
       (b* (((when (endp cases)) nil)
            ((ok allvars1) (swcase-unique-vars (car cases) allvars)))
         (list (swcase-induct (car cases) varset funtab allvars)
               (swcase-list-induct (cdr cases) varset funtab allvars1)))
       :measure (swcase-list-count cases))

     (define fundef-induct ((fundef fundefp)
                            (funtab funtablep)
                            (allvars identifier-setp))
       (b* (((fundef fundef) fundef)
            ((ok varset1) (add-vars (append fundef.inputs fundef.outputs) nil))
            ((ok allvars1) (var-list-unique-vars (append fundef.inputs
                                                         fundef.outputs)
                                                 allvars)))
         (block-induct fundef.body varset1 funtab allvars1))
       :measure (fundef-count fundef))

     :flag-local nil))

  (defrulel switch-lemma
    (implies (identifier-setp vars)
             (b* ((vars1 (swcase-list-unique-vars cases vars))
                  (vars2 (block-option-unique-vars block? vars1)))
               (implies (and (not (resulterrp vars1))
                             (not (resulterrp vars2)))
                        (set::subset vars vars2))))
    :use (:instance block-option-unique-vars-extend
          (allvars (swcase-list-unique-vars cases vars)))
    :disable block-option-unique-vars-extend
    :enable set::subset-transitive)

  (local
   (defthm-induction-flag

     (defthm theorem-for-statement-induct
       (b* ((allvars1 (statement-unique-vars stmt allvars))
            (varsmodes (check-safe-statement stmt varset funtab))
            (varset1 (vars+modes->vars varsmodes)))
         (implies (and (identifier-setp varset)
                       (identifier-setp allvars)
                       (set::subset varset allvars)
                       (not (resulterrp allvars1))
                       (not (resulterrp varsmodes)))
                  (set::subset varset1 allvars1)))
       :flag statement-induct)

     (defthm theorem-for-statement-list-induct
       (b* ((allvars1 (statement-list-unique-vars stmts allvars))
            (varsmodes (check-safe-statement-list stmts varset funtab))
            (varset1 (vars+modes->vars varsmodes)))
         (implies (and (identifier-setp varset)
                       (identifier-setp allvars)
                       (set::subset varset allvars)
                       (not (resulterrp allvars1))
                       (not (resulterrp varsmodes)))
                  (set::subset varset1 allvars1)))
       :flag statement-list-induct)

     (defthm theorem-for-block-induct
       t
       :rule-classes nil
       :flag block-induct)

     (defthm theorem-for-block-option-induct
       t
       :rule-classes nil
       :flag block-option-induct)

     (defthm theorem-for-swcase-induct
       t
       :rule-classes nil
       :flag swcase-induct)

     (defthm theorem-for-swcase-list-induct
       t
       :rule-classes nil
       :flag swcase-list-induct)

     (defthm theorem-for-fundef-induct
       t
       :rule-classes nil
       :flag fundef-induct)

     :hints
     (("Goal"
       :in-theory
       (enable check-safe-statement
               check-safe-statement-list
               check-safe-block
               check-safe-block-option
               check-safe-swcase
               check-safe-swcase-list
               check-safe-fundef
               statement-unique-vars
               statement-list-unique-vars
               block-unique-vars
               block-option-unique-vars
               swcase-unique-vars
               swcase-list-unique-vars
               fundef-unique-vars
               set::subset-transitive
               identifier-setp-when-identifier-set-resultp-and-not-resulterrp
               check-safe-variable-single
               check-safe-variable-multi
               add-var-to-set-insert
               add-vars-to-set-list-insert
               var-unique-vars-to-set-insert
               var-list-unique-vars-to-set-list-insert)
       :expand (check-safe-statement stmt varset funtab)))))

  (defrule check-safe-statement-subset-unique-vars-statement
    (b* ((allvars1 (statement-unique-vars stmt allvars))
         (varsmodes (check-safe-statement stmt varset funtab))
         (varset1 (vars+modes->vars varsmodes)))
      (implies (and (identifier-setp varset)
                    (identifier-setp allvars)
                    (set::subset varset allvars)
                    (not (resulterrp allvars1))
                    (not (resulterrp varsmodes)))
               (set::subset varset1 allvars1))))

  (defrule check-safe-statement-list-subset-unique-vars-statement-list
    (b* ((allvars1 (statement-list-unique-vars stmts allvars))
         (varsmodes (check-safe-statement-list stmts varset funtab))
         (varset1 (vars+modes->vars varsmodes)))
      (implies (and (identifier-setp varset)
                    (identifier-setp allvars)
                    (set::subset varset allvars)
                    (not (resulterrp allvars1))
                    (not (resulterrp varsmodes)))
               (set::subset varset1 allvars1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection theorems-about-function-tables-and-variable-renaming
  :short "Theorems about function tables and related concepts
          for code related by variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "If two function definitions are related by variable renaming,
     their correpsonding function types are the same,
     because they do not depend on variables.")
   (xdoc::p
    "Consequently, if two lists of function definitions
     are related by variable renaming,
     their corresponding function tables are the same.")
   (xdoc::p
    "That implies that @(tsee add-funtypes) yields the same result,
     starting with the same function table,
     for lists of function definitions related by variable renaming."))

  (defruled same-funtype-for-fundef-when-fundef-renamevar
    (implies (not (resulterrp (fundef-renamevar old new)))
             (equal (funtype-for-fundef new)
                    (funtype-for-fundef old)))
    :expand (fundef-renamevar old new)
    :enable (fundef-renamevar
             funtype-for-fundef
             same-len-when-add-vars-to-var-renaming))

  (defruled same-funtable-for-fundefs-when-fundef-list-renamevar
    (implies (and (not (resulterrp (fundef-list-renamevar old new)))
                  (not (resulterrp (funtable-for-fundefs old))))
             (equal (funtable-for-fundefs new)
                    (funtable-for-fundefs old)))
    :enable (fundef-list-renamevar
             funtable-for-fundefs
             same-funtype-for-fundef-when-fundef-renamevar
             same-fundef->name-when-fundef-renamevar))

  (defruled same-add-funtypes-when-fundef-list-renamevar
    (implies (and (not (resulterrp (fundef-list-renamevar old new)))
                  (not (resulterrp (add-funtypes old funtab))))
             (equal (add-funtypes new funtab)
                    (add-funtypes old funtab)))
    :enable (add-funtypes
             same-funtable-for-fundefs-when-fundef-list-renamevar)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection disambiguator-variables-statements/blocks/cases/fundefs-safety
  :short "Proof that variable disambiguation preserves the safety of
          statements, blocks, and related entities."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved via a custom induction schema
     that takes into account the recursive structure of
     the renaming functions,
     the safety checking functions,
     and the variable uniqueness checking functions.")
   (xdoc::p
    "The form of the theorems is as explained in
     @(see disambiguator-variables-safety)."))

  (local
   (defines induction

     (define statement-induct ((old statementp)
                               (new statementp)
                               (ren identifier-identifier-mapp)
                               (funtab funtablep)
                               (allvars identifier-setp))
       (statement-case
        old
        :block (if (statement-case new :block)
                   (b* ((new.get (statement-block->get new)))
                     (block-induct old.get new.get ren funtab allvars))
                 nil)
        :variable-single nil
        :variable-multi nil
        :assign-single nil
        :assign-multi nil
        :funcall nil
        :if (if (statement-case new :if)
                (b* ((new.body (statement-if->body new)))
                  (block-induct old.body new.body ren funtab allvars))
              nil)
        :for (b* (((unless (statement-case new :for)) nil)
                  (new.init (statement-for->init new))
                  (new.update (statement-for->update new))
                  (new.body (statement-for->body new))
                  (old-stmts (block->statements old.init))
                  (new-stmts (block->statements new.init))
                  ((ok funtab) (add-funtypes (statements-to-fundefs old-stmts)
                                             funtab))
                  ((ok ren1) (statement-list-renamevar old-stmts new-stmts ren))
                  ((ok allvars1) (statement-list-unique-vars new-stmts allvars))
                  ((ok allvars2) (block-unique-vars new.update allvars1)))
               (list (statement-list-induct old-stmts
                                            new-stmts
                                            ren
                                            funtab
                                            allvars)
                     (block-induct old.update new.update ren1 funtab allvars1)
                     (block-induct old.body new.body ren1 funtab allvars2)))
        :switch (b* (((unless (statement-case new :switch)) nil)
                     (new.cases (statement-switch->cases new))
                     (new.default (statement-switch->default new))
                     ((ok allvars1) (swcase-list-unique-vars new.cases
                                                             allvars)))
                  (list (swcase-list-induct old.cases
                                            new.cases
                                            ren
                                            funtab
                                            allvars)
                        (block-option-induct old.default
                                             new.default
                                             ren
                                             funtab
                                             allvars1)))
        :leave nil
        :break nil
        :continue nil
        :fundef (b* (((unless (statement-case new :fundef)) nil)
                     (new.get (statement-fundef->get new)))
                  (fundef-induct old.get new.get funtab allvars)))
       :measure (statement-count old))

     (define statement-list-induct ((old statement-listp)
                                    (new statement-listp)
                                    (ren identifier-identifier-mapp)
                                    (funtab funtablep)
                                    (allvars identifier-setp))
       (b* (((when (endp old)) nil)
            ((when (endp new)) nil)
            ((ok ren1) (statement-renamevar (car old) (car new) ren))
            ((ok allvars1) (statement-unique-vars (car new) allvars)))
         (list (statement-induct (car old) (car new) ren funtab allvars)
               (statement-list-induct (cdr old)
                                      (cdr new)
                                      ren1
                                      funtab
                                      allvars1)))
       :measure (statement-list-count old))

     (define block-induct ((old blockp)
                           (new blockp)
                           (ren identifier-identifier-mapp)
                           (funtab funtablep)
                           (allvars identifier-setp))
       (b* ((old-stmts (block->statements old))
            (new-stmts (block->statements new))
            ((ok funtab) (add-funtypes (statements-to-fundefs old-stmts)
                                       funtab)))
         (list (statement-list-induct old-stmts new-stmts ren funtab allvars)))
       :measure (block-count old))

     (define block-option-induct ((old block-optionp)
                                  (new block-optionp)
                                  (ren identifier-identifier-mapp)
                                  (funtab funtablep)
                                  (allvars identifier-setp))
       (b* (((when (block-option-case old :none)) nil)
            ((when (block-option-case new :none)) nil))
         (block-induct (block-option-some->val old)
                       (block-option-some->val new)
                       ren
                       funtab
                       allvars))
       :measure (block-option-count old))

     (define swcase-induct ((old swcasep)
                            (new swcasep)
                            (ren identifier-identifier-mapp)
                            (funtab funtablep)
                            (allvars identifier-setp))
       (block-induct (swcase->body old) (swcase->body new) ren funtab allvars)
       :measure (swcase-count old))

     (define swcase-list-induct ((old swcase-listp)
                                 (new swcase-listp)
                                 (ren identifier-identifier-mapp)
                                 (funtab funtablep)
                                 (allvars identifier-setp))
       (b* (((when (endp old)) nil)
            ((when (endp new)) nil)
            ((ok allvars1) (swcase-unique-vars (car new) allvars)))
         (list (swcase-induct (car old) (car new) ren funtab allvars)
               (swcase-list-induct (cdr old) (cdr new) ren funtab allvars1)))
       :measure (swcase-list-count old))

     (define fundef-induct ((old fundefp)
                            (new fundefp)
                            (funtab funtablep)
                            (allvars identifier-setp))
       (b* (((fundef old) old)
            ((fundef new) new)
            ((ok ren) (add-vars-to-var-renaming old.inputs new.inputs nil))
            ((ok ren) (add-vars-to-var-renaming old.outputs new.outputs ren))
            ((ok allvars) (var-list-unique-vars (append new.inputs new.outputs)
                                                allvars)))
         (block-induct old.body new.body ren funtab allvars))
       :measure (fundef-count old))

     :flag-local nil))

  (defrulel block-lemma
    (implies (and (not (resulterrp (statement-list-renamevar old new ren)))
                  (not (resulterrp
                        (add-funtypes (statements-to-fundefs old) funtab))))
             (equal (add-funtypes (statements-to-fundefs new) funtab)
                    (add-funtypes (statements-to-fundefs old) funtab)))
    :use (:instance same-add-funtypes-when-fundef-list-renamevar
          (old (statements-to-fundefs old))
          (new (statements-to-fundefs new))))

  (defrulel statement-for-lemma
    (implies (and (identifier-setp varset)
                  (identifier-setp allvars)
                  (not (resulterrp (block-unique-vars block allvars)))
                  (set::subset varset
                               allvars))
             (set::subset varset
                          (block-unique-vars block allvars)))
    :expand (block-unique-vars block allvars)
    :enable set::subset-transitive)

  (local
   (defthm-induction-flag

     (defthm theorem-for-statement-induct
       (b* ((ren1 (statement-renamevar old new ren))
            (allvars1 (statement-unique-vars new allvars))
            (varsmodes-old (check-safe-statement old (varset-old ren) funtab))
            (varsmodes-new (check-safe-statement new (varset-new ren) funtab)))
         (implies (and (identifier-setp allvars)
                       (set::subset (varset-new ren) allvars)
                       (not (resulterrp ren1))
                       (not (resulterrp allvars1))
                       (not (resulterrp varsmodes-old)))
                  (and (not (resulterrp varsmodes-new))
                       (equal (vars+modes->vars varsmodes-old)
                              (varset-old ren1))
                       (equal (vars+modes->vars varsmodes-new)
                              (varset-new ren1))
                       (equal (vars+modes->modes varsmodes-old)
                              (vars+modes->modes varsmodes-new)))))
       :flag statement-induct)

     (defthm theorem-for-statement-list-induct
       (b* ((ren1 (statement-list-renamevar old new ren))
            (allvars1 (statement-list-unique-vars new allvars))
            (varsmodes-old (check-safe-statement-list old
                                                      (varset-old ren)
                                                      funtab))
            (varsmodes-new (check-safe-statement-list new
                                                      (varset-new ren)
                                                      funtab)))
         (implies (and (identifier-setp allvars)
                       (set::subset (varset-new ren) allvars)
                       (not (resulterrp ren1))
                       (not (resulterrp allvars1))
                       (not (resulterrp varsmodes-old)))
                  (and (not (resulterrp varsmodes-new))
                       (equal (vars+modes->vars varsmodes-old)
                              (varset-old ren1))
                       (equal (vars+modes->vars varsmodes-new)
                              (varset-new ren1))
                       (equal (vars+modes->modes varsmodes-new)
                              (vars+modes->modes varsmodes-old)))))
       :flag statement-list-induct)

     (defthm theorem-for-block-induct
       (b* ((ok (block-renamevar old new ren))
            (allvars1 (block-unique-vars new allvars))
            (modes-old (check-safe-block old (varset-old ren) funtab))
            (modes-new (check-safe-block new (varset-new ren) funtab)))
         (implies (and (identifier-setp allvars)
                       (set::subset (varset-new ren) allvars)
                       (not (resulterrp ok))
                       (not (resulterrp allvars1))
                       (not (resulterrp modes-old)))
                  (and (not (resulterrp modes-new))
                       (equal modes-new modes-old))))
       :flag block-induct)

     (defthm theorem-for-block-option-induct
       (b* ((ok (block-option-renamevar old new ren))
            (allvars1 (block-option-unique-vars new allvars))
            (modes-old (check-safe-block-option old (varset-old ren) funtab))
            (modes-new (check-safe-block-option new (varset-new ren) funtab)))
         (implies (and (identifier-setp allvars)
                       (set::subset (varset-new ren) allvars)
                       (not (resulterrp ok))
                       (not (resulterrp allvars1))
                       (not (resulterrp modes-old)))
                  (and (not (resulterrp modes-new))
                       (equal modes-new modes-old))))
       :flag block-option-induct)

     (defthm theorem-for-swcase-induct
       (b* ((ok (swcase-renamevar old new ren))
            (allvars1 (swcase-unique-vars new allvars))
            (modes-old (check-safe-swcase old (varset-old ren) funtab))
            (modes-new (check-safe-swcase new (varset-new ren) funtab)))
         (implies (and (identifier-setp allvars)
                       (set::subset (varset-new ren) allvars)
                       (not (resulterrp ok))
                       (not (resulterrp allvars1))
                       (not (resulterrp modes-old)))
                  (and (not (resulterrp modes-new))
                       (equal modes-new modes-old))))
       :flag swcase-induct)

     (defthm theorem-for-swcase-list-induct
       (b* ((ok (swcase-list-renamevar old new ren))
            (allvars1 (swcase-list-unique-vars new allvars))
            (modes-old (check-safe-swcase-list old (varset-old ren) funtab))
            (modes-new (check-safe-swcase-list new (varset-new ren) funtab)))
         (implies (and (identifier-setp allvars)
                       (set::subset (varset-new ren) allvars)
                       (not (resulterrp ok))
                       (not (resulterrp allvars1))
                       (not (resulterrp modes-old)))
                  (and (not (resulterrp modes-new))
                       (equal modes-new modes-old))))
       :flag swcase-list-induct)

     (defthm theorem-for-fundef-induct
       (b* ((ok (fundef-renamevar old new))
            (allvars1 (fundef-unique-vars new allvars))
            (ok-old (check-safe-fundef old funtab))
            (ok-new (check-safe-fundef new funtab)))
         (implies (and (identifier-setp allvars)
                       (not (resulterrp ok))
                       (not (resulterrp allvars1))
                       (not (resulterrp ok-old)))
                  (not (resulterrp ok-new))))
       :flag fundef-induct)

     :hints (("Goal"
              :expand ((check-safe-fundef old funtab)
                       (check-safe-block new (varset-new ren) funtab)
                       (statement-unique-vars new allvars))
              :in-theory
              (enable
               check-safe-statement
               check-safe-statement-list
               check-safe-block
               check-safe-block-option
               check-safe-swcase
               check-safe-swcase-list
               check-safe-fundef
               check-safe-variable-single
               check-safe-variable-multi
               check-safe-assign-single
               check-safe-assign-multi
               statement-renamevar
               statement-list-renamevar
               block-renamevar
               block-option-renamevar
               swcase-renamevar
               swcase-list-renamevar
               fundef-renamevar
               expression-option-renamevar
               funcall-option-renamevar
               statement-unique-vars
               statement-list-unique-vars
               block-unique-vars
               block-option-unique-vars
               swcase-unique-vars
               swcase-list-unique-vars
               fundef-unique-vars
               add-var-to-set-insert
               add-vars-to-set-list-insert
               var-list-unique-vars-to-set-list-insert
               check-safe-path-when-path-renamevar
               check-safe-path-list-when-path-list-renamevar
               expression-option-some->val
               funcall-option-some->val
               add-var-not-error-when-var-unique-vars-of-larger
               add-vars-not-error-when-var-list-unique-vars-of-larger
               same-len-when-path-list-renamevar
               same-len-when-add-vars-to-var-renaming
               same-swcase-list->value-list-when-swcase-list-renamevar
               not-resulterrp-when-identifier-setp
               identifier-setp-when-identifier-set-resultp-and-not-resulterrp
               set::subset-transitive)))))

  (defrule check-safe-statement-when-renamevar
    (b* ((ren1 (statement-renamevar old new ren))
         (allvars1 (statement-unique-vars new allvars))
         (varsmodes-old (check-safe-statement old (varset-old ren) funtab))
         (varsmodes-new (check-safe-statement new (varset-new ren) funtab)))
      (implies (and (identifier-setp allvars)
                    (set::subset (varset-new ren) allvars)
                    (not (resulterrp ren1))
                    (not (resulterrp allvars1))
                    (not (resulterrp varsmodes-old)))
               (and (not (resulterrp varsmodes-new))
                    (equal (vars+modes->vars varsmodes-old)
                           (varset-old ren1))
                    (equal (vars+modes->vars varsmodes-new)
                           (varset-new ren1))
                    (equal (vars+modes->modes varsmodes-old)
                           (vars+modes->modes varsmodes-new))))))

  (defrule check-safe-statement-list-when-renamevar
    (b* ((ren1 (statement-list-renamevar old new ren))
         (allvars1 (statement-list-unique-vars new allvars))
         (varsmodes-old (check-safe-statement-list old
                                                   (varset-old ren)
                                                   funtab))
         (varsmodes-new (check-safe-statement-list new
                                                   (varset-new ren)
                                                   funtab)))
      (implies (and (identifier-setp allvars)
                    (set::subset (varset-new ren) allvars)
                    (not (resulterrp ren1))
                    (not (resulterrp allvars1))
                    (not (resulterrp varsmodes-old)))
               (and (not (resulterrp varsmodes-new))
                    (equal (vars+modes->vars varsmodes-old)
                           (varset-old ren1))
                    (equal (vars+modes->vars varsmodes-new)
                           (varset-new ren1))
                    (equal (vars+modes->modes varsmodes-new)
                           (vars+modes->modes varsmodes-old))))))

  (defrule check-safe-block-when-renamevar
    (b* ((ok (block-renamevar old new ren))
         (allvars1 (block-unique-vars new allvars))
         (modes-old (check-safe-block old (varset-old ren) funtab))
         (modes-new (check-safe-block new (varset-new ren) funtab)))
      (implies (and (identifier-setp allvars)
                    (set::subset (varset-new ren) allvars)
                    (not (resulterrp ok))
                    (not (resulterrp allvars1))
                    (not (resulterrp modes-old)))
               (and (not (resulterrp modes-new))
                    (equal modes-new modes-old)))))

  (defrule check-safe-block-option-when-renamevar
    (b* ((ok (block-option-renamevar old new ren))
         (allvars1 (block-option-unique-vars new allvars))
         (modes-old (check-safe-block-option old (varset-old ren) funtab))
         (modes-new (check-safe-block-option new (varset-new ren) funtab)))
      (implies (and (identifier-setp allvars)
                    (set::subset (varset-new ren) allvars)
                    (not (resulterrp ok))
                    (not (resulterrp allvars1))
                    (not (resulterrp modes-old)))
               (and (not (resulterrp modes-new))
                    (equal modes-new modes-old)))))

  (defrule check-safe-swcase-when-renamevar
    (b* ((ok (swcase-renamevar old new ren))
         (allvars1 (swcase-unique-vars new allvars))
         (modes-old (check-safe-swcase old (varset-old ren) funtab))
         (modes-new (check-safe-swcase new (varset-new ren) funtab)))
      (implies (and (identifier-setp allvars)
                    (set::subset (varset-new ren) allvars)
                    (not (resulterrp ok))
                    (not (resulterrp allvars1))
                    (not (resulterrp modes-old)))
               (and (not (resulterrp modes-new))
                    (equal modes-new modes-old)))))

  (defrule check-swcase-list-when-renamevar
    (b* ((ok (swcase-list-renamevar old new ren))
         (allvars1 (swcase-list-unique-vars new allvars))
         (modes-old (check-safe-swcase-list old (varset-old ren) funtab))
         (modes-new (check-safe-swcase-list new (varset-new ren) funtab)))
      (implies (and (identifier-setp allvars)
                    (set::subset (varset-new ren) allvars)
                    (not (resulterrp ok))
                    (not (resulterrp allvars1))
                    (not (resulterrp modes-old)))
               (and (not (resulterrp modes-new))
                    (equal modes-new modes-old)))))

  (defrule check-safe-fundef-when-renamevar
    (b* ((ok (fundef-renamevar old new))
         (allvars1 (fundef-unique-vars new allvars))
         (ok-old (check-safe-fundef old funtab))
         (ok-new (check-safe-fundef new funtab)))
      (implies (and (identifier-setp allvars)
                    (not (resulterrp ok))
                    (not (resulterrp allvars1))
                    (not (resulterrp ok-old)))
               (not (resulterrp ok-new))))))
