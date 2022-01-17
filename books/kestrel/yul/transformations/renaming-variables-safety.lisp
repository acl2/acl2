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

(include-book "../language/static-safety-checking")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ renaming-variables-safety
  :parents (renaming-variables)
  :short "Proof that variable renaming preserves the static safety checks."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in @(see renaming-variables),
     the renaming list/alist consists of
     the variables in scope for the old code (the keys of the alist) and
     the variables in scope for the new code (the values of the alist).
     Thus, we prove theorems saying that
     if two pieces of code are related by variable renaming,
     and the old code is safe with respect to
     the variables that are the keys of the renaming alist,
     then the new code is safe with respect to
     the variables that are the values of the renaming alist;
     furthermore, if the renaming list is updated,
     the updated variables in scope are still the keys and values,
     for the old and new code;
     furthermore, if the static safety checks
     return information other than updated variables in scope
     (e.g. modes, or numbers of values),
     that information is the same for old and new code.")
   (xdoc::p
    "The above is just a sketch.
     Things are explained in more detail below."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define varset-old ((ren renamingp))
  :returns (varset identifier-setp)
  :short "Variables in scope for the old code in variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "This explicates the fact that, as mentioned in @(see renaming-variables),
     the keys of a renaming alist are
     the variables in scope for the old code.")
   (xdoc::p
    "Also see @(tsee varset-new)."))
  (mergesort (strip-cars (renaming->list ren)))
  :guard-hints
  (("Goal"
    :in-theory
    (enable identifier-listp-of-strip-cars-when-identifier-identifier-alistp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define varset-new ((ren renamingp))
  :returns (varset identifier-setp)
  :short "Variables in scope for the new code in variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "This explicates the fact that, as mentioned in @(see renaming-variables),
     the values of a renaming alist are
     the variables in scope for the old code.")
   (xdoc::p
    "Also see @(tsee varset-old)."))
  (mergesort (strip-cdrs (renaming->list ren)))
  :guard-hints
  (("Goal"
    :in-theory
    (enable identifier-listp-of-strip-cdrs-when-identifier-identifier-alistp)))
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
             varset-old
             mergesort))

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
             varset-new
             mergesort))

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
           identifier-listp-of-strip-cdrs-when-identifier-identifier-alistp)
  :prep-lemmas
  ((defrule lemma
     (implies (member-equal (cons a b) alist)
              (member-equal b (strip-cdrs alist))))))

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

(defsection add-var/vars-not-error-when-add-var/vars-to-var-renaming
  :short "If variables can be added to a variable renaming,
          then the new variables can be added to the ones in the new scope."

  (defruled add-var-new-not-error-when-add-var-to-var-renaming
    (implies (not (resulterrp (add-var-to-var-renaming old new ren)))
             (not (resulterrp (add-var new (varset-new ren)))))
    :enable (add-var-to-var-renaming
             add-var
             varset-new
             identifier-listp-of-strip-cdrs-when-identifier-identifier-alistp
             not-resulterrp-when-identifier-setp))

  (defruled add-vars-new-not-error-when-add-vars-to-var-renaming
    (implies (not (resulterrp (add-vars-to-var-renaming old new ren)))
             (not (resulterrp (add-vars new (varset-new ren)))))
    :enable (add-vars-to-var-renaming
             add-vars
             add-var-to-set-insert
             not-resulterrp-when-identifier-setp
             add-var-new-not-error-when-add-var-to-var-renaming)))

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

(defsection renaming-variables-statements/blocks/cases/fundefs-safety
  :short "Proof that variable renaming preserves the safety of
          statements, blocks, and related entities."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved via a custom induction schema
     that takes into account the recursive structure of
     the renaming functions and the safety checking functions.")
   (xdoc::p
    "The form of the theorems is as explained in
     @(see renaming-variables-safety)."))

  (local
   (defines induction

     (define statement-induct ((old statementp)
                               (new statementp)
                               (ren renamingp)
                               (funtab funtablep))
       (statement-case
        old
        :block (if (statement-case new :block)
                   (b* ((new.get (statement-block->get new)))
                     (block-induct old.get new.get ren funtab))
                 nil)
        :variable-single nil
        :variable-multi nil
        :assign-single nil
        :assign-multi nil
        :funcall nil
        :if (if (statement-case new :if)
                (b* ((new.body (statement-if->body new)))
                  (block-induct old.body new.body ren funtab))
              nil)
        :for (b* (((unless (statement-case new :for)) nil)
                  (new.init (statement-for->init new))
                  (new.update (statement-for->update new))
                  (new.body (statement-for->body new))
                  (old-stmts (block->statements old.init))
                  (new-stmts (block->statements new.init))
                  ((ok funtab) (add-funtypes (statements-to-fundefs old-stmts)
                                             funtab))
                  ((ok ren1) (statement-list-renamevar old-stmts new-stmts ren)))
               (list (statement-list-induct old-stmts
                                            new-stmts
                                            ren
                                            funtab)
                     (block-induct old.update new.update ren1 funtab)
                     (block-induct old.body new.body ren1 funtab)))
        :switch (b* (((unless (statement-case new :switch)) nil)
                     (new.cases (statement-switch->cases new))
                     (new.default (statement-switch->default new)))
                  (list (swcase-list-induct old.cases
                                            new.cases
                                            ren
                                            funtab)
                        (block-option-induct old.default
                                             new.default
                                             ren
                                             funtab)))
        :leave nil
        :break nil
        :continue nil
        :fundef (b* (((unless (statement-case new :fundef)) nil)
                     (new.get (statement-fundef->get new)))
                  (fundef-induct old.get new.get funtab)))
       :measure (statement-count old))

     (define statement-list-induct ((old statement-listp)
                                    (new statement-listp)
                                    (ren renamingp)
                                    (funtab funtablep))
       (b* (((when (endp old)) nil)
            ((when (endp new)) nil)
            ((ok ren1) (statement-renamevar (car old) (car new) ren)))
         (list (statement-induct (car old) (car new) ren funtab)
               (statement-list-induct (cdr old)
                                      (cdr new)
                                      ren1
                                      funtab)))
       :measure (statement-list-count old))

     (define block-induct ((old blockp)
                           (new blockp)
                           (ren renamingp)
                           (funtab funtablep))
       (b* ((old-stmts (block->statements old))
            (new-stmts (block->statements new))
            ((ok funtab) (add-funtypes (statements-to-fundefs old-stmts)
                                       funtab)))
         (list (statement-list-induct old-stmts new-stmts ren funtab)))
       :measure (block-count old))

     (define block-option-induct ((old block-optionp)
                                  (new block-optionp)
                                  (ren renamingp)
                                  (funtab funtablep))
       (b* (((when (block-option-case old :none)) nil)
            ((when (block-option-case new :none)) nil))
         (block-induct (block-option-some->val old)
                       (block-option-some->val new)
                       ren
                       funtab))
       :measure (block-option-count old))

     (define swcase-induct ((old swcasep)
                            (new swcasep)
                            (ren renamingp)
                            (funtab funtablep))
       (block-induct (swcase->body old) (swcase->body new) ren funtab)
       :measure (swcase-count old))

     (define swcase-list-induct ((old swcase-listp)
                                 (new swcase-listp)
                                 (ren renamingp)
                                 (funtab funtablep))
       (b* (((when (endp old)) nil)
            ((when (endp new)) nil))
         (list (swcase-induct (car old) (car new) ren funtab)
               (swcase-list-induct (cdr old) (cdr new) ren funtab)))
       :measure (swcase-list-count old))

     (define fundef-induct ((old fundefp)
                            (new fundefp)
                            (funtab funtablep))
       (b* (((fundef old) old)
            ((fundef new) new)
            ((ok ren) (add-vars-to-var-renaming old.inputs
                                                new.inputs
                                                (renaming nil)))
            ((ok ren) (add-vars-to-var-renaming old.outputs new.outputs ren)))
         (block-induct old.body new.body ren funtab))
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

  (defrulel fun-inputs-lemma
    (implies (not (resulterrp (add-vars-to-var-renaming old-inputs
                                                        new-inputs
                                                        '((list)))))
             (not (resulterrp (add-vars new-inputs nil))))
    :use (:instance add-vars-new-not-error-when-add-vars-to-var-renaming
          (old old-inputs)
          (new new-inputs)
          (ren (renaming nil))))

  (defrulel fun-outputs-lemma
    (implies
     (and
      (identifier-listp new-inputs)
      (not (resulterrp (add-vars-to-var-renaming old-inputs
                                                 new-inputs
                                                 '((list)))))
      (not
       (resulterrp
        (add-vars-to-var-renaming old-outputs
                                  new-outputs
                                  (add-vars-to-var-renaming old-inputs
                                                            new-inputs
                                                            '((list)))))))
     (not (resulterrp (add-vars new-outputs
                                (set::list-insert new-inputs
                                                  nil)))))
    :use (:instance add-vars-new-not-error-when-add-vars-to-var-renaming
          (old old-outputs)
          (new new-outputs)
          (ren (add-vars-to-var-renaming old-inputs
                                         new-inputs
                                         '((list))))))

  (local
   (defthm-induction-flag

     (defthm theorem-for-statement-induct
       (b* ((ren1 (statement-renamevar old new ren))
            (varsmodes-old (check-safe-statement old (varset-old ren) funtab))
            (varsmodes-new (check-safe-statement new (varset-new ren) funtab)))
         (implies (and (not (resulterrp ren1))
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
            (varsmodes-old (check-safe-statement-list old
                                                      (varset-old ren)
                                                      funtab))
            (varsmodes-new (check-safe-statement-list new
                                                      (varset-new ren)
                                                      funtab)))
         (implies (and (not (resulterrp ren1))
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
            (modes-old (check-safe-block old (varset-old ren) funtab))
            (modes-new (check-safe-block new (varset-new ren) funtab)))
         (implies (and (not (resulterrp ok))
                       (not (resulterrp modes-old)))
                  (and (not (resulterrp modes-new))
                       (equal modes-new modes-old))))
       :flag block-induct)

     (defthm theorem-for-block-option-induct
       (b* ((ok (block-option-renamevar old new ren))
            (modes-old (check-safe-block-option old (varset-old ren) funtab))
            (modes-new (check-safe-block-option new (varset-new ren) funtab)))
         (implies (and (not (resulterrp ok))
                       (not (resulterrp modes-old)))
                  (and (not (resulterrp modes-new))
                       (equal modes-new modes-old))))
       :flag block-option-induct)

     (defthm theorem-for-swcase-induct
       (b* ((ok (swcase-renamevar old new ren))
            (modes-old (check-safe-swcase old (varset-old ren) funtab))
            (modes-new (check-safe-swcase new (varset-new ren) funtab)))
         (implies (and (not (resulterrp ok))
                       (not (resulterrp modes-old)))
                  (and (not (resulterrp modes-new))
                       (equal modes-new modes-old))))
       :flag swcase-induct)

     (defthm theorem-for-swcase-list-induct
       (b* ((ok (swcase-list-renamevar old new ren))
            (modes-old (check-safe-swcase-list old (varset-old ren) funtab))
            (modes-new (check-safe-swcase-list new (varset-new ren) funtab)))
         (implies (and (not (resulterrp ok))
                       (not (resulterrp modes-old)))
                  (and (not (resulterrp modes-new))
                       (equal modes-new modes-old))))
       :flag swcase-list-induct)

     (defthm theorem-for-fundef-induct
       (b* ((ok (fundef-renamevar old new))
            (ok-old (check-safe-fundef old funtab))
            (ok-new (check-safe-fundef new funtab)))
         (implies (and (not (resulterrp ok))
                       (not (resulterrp ok-old)))
                  (not (resulterrp ok-new))))
       :flag fundef-induct)

     :hints
     (("Goal"
       :expand ((check-safe-fundef old funtab)
                (check-safe-fundef new funtab)
                (check-safe-block new (varset-new ren) funtab))
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
        add-var-to-set-insert
        add-vars-to-set-list-insert
        check-safe-path-when-path-renamevar
        check-safe-path-list-when-path-list-renamevar
        expression-option-some->val
        funcall-option-some->val
        add-var-new-not-error-when-add-var-to-var-renaming
        add-vars-new-not-error-when-add-vars-to-var-renaming
        same-len-when-path-list-renamevar
        same-len-when-add-vars-to-var-renaming
        same-swcase-list->value-list-when-swcase-list-renamevar
        not-resulterrp-when-identifier-setp
        identifier-setp-when-identifier-set-resultp-and-not-resulterrp)))))

  (defrule check-safe-statement-when-renamevar
    (b* ((ren1 (statement-renamevar old new ren))
         (varsmodes-old (check-safe-statement old (varset-old ren) funtab))
         (varsmodes-new (check-safe-statement new (varset-new ren) funtab)))
      (implies (and (not (resulterrp ren1))
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
         (varsmodes-old (check-safe-statement-list old
                                                   (varset-old ren)
                                                   funtab))
         (varsmodes-new (check-safe-statement-list new
                                                   (varset-new ren)
                                                   funtab)))
      (implies (and (not (resulterrp ren1))
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
         (modes-old (check-safe-block old (varset-old ren) funtab))
         (modes-new (check-safe-block new (varset-new ren) funtab)))
      (implies (and (not (resulterrp ok))
                    (not (resulterrp modes-old)))
               (and (not (resulterrp modes-new))
                    (equal modes-new modes-old)))))

  (defrule check-safe-block-option-when-renamevar
    (b* ((ok (block-option-renamevar old new ren))
         (modes-old (check-safe-block-option old (varset-old ren) funtab))
         (modes-new (check-safe-block-option new (varset-new ren) funtab)))
      (implies (and (not (resulterrp ok))
                    (not (resulterrp modes-old)))
               (and (not (resulterrp modes-new))
                    (equal modes-new modes-old)))))

  (defrule check-safe-swcase-when-renamevar
    (b* ((ok (swcase-renamevar old new ren))
         (modes-old (check-safe-swcase old (varset-old ren) funtab))
         (modes-new (check-safe-swcase new (varset-new ren) funtab)))
      (implies (and (not (resulterrp ok))
                    (not (resulterrp modes-old)))
               (and (not (resulterrp modes-new))
                    (equal modes-new modes-old)))))

  (defrule check-swcase-list-when-renamevar
    (b* ((ok (swcase-list-renamevar old new ren))
         (modes-old (check-safe-swcase-list old (varset-old ren) funtab))
         (modes-new (check-safe-swcase-list new (varset-new ren) funtab)))
      (implies (and (not (resulterrp ok))
                    (not (resulterrp modes-old)))
               (and (not (resulterrp modes-new))
                    (equal modes-new modes-old)))))

  (defrule check-safe-fundef-when-renamevar
    (b* ((ok (fundef-renamevar old new))
         (ok-old (check-safe-fundef old funtab))
         (ok-new (check-safe-fundef new funtab)))
      (implies (and (not (resulterrp ok))
                    (not (resulterrp ok-old)))
               (not (resulterrp ok-new))))))
