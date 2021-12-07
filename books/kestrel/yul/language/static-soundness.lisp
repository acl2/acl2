; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "static-safety-checking")
(include-book "dynamic-semantics")

(include-book "../library-extensions/osets")

(local (include-book "../library-extensions/lists"))
(local (include-book "../library-extensions/omaps"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-soundness
  :short "Proof of static soundness of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that if the safety checks in the static semantics are satisfied,
     no dynamic semantics errors can occur during execution,
     except for running out of the artificial limit counter.
     This is a soundness property,
     because the safety checks in the static semantics
     are designed exactly to prevent the occurrence of those errors,
     which the dynamic semantics defensively checks."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define resulterr-limitp (x)
  :returns (yes/no booleanp)
  :short "Recognize limit errors."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in the "
    (xdoc::seetopic "dynamic-semantics" "dynamic semantics")
    ", the ACL2 execution functions of Yul code
     take an artificial limit counter as input,
     and return an error when that limit is exhausted.
     In formulating the Yul static soundness theorem,
     we need to exclude limit errors
     from the dynamic errors rules out by the static semantic checks:
     the static semantic checks rule out all dynamic errors
     except for limit errors,
     because of course there are no termination checks.")
   (xdoc::p
    "Here we define a predicate that recognized limit errors,
     i.e. values of type @(tsee resulterr)
     whose information starts with the keyword @(':limit').
     The adequacy of this predicate definition depends on
     the definition of the execution functions,
     in particular the fact that they return error limits of this form.
     This predicate must be adapted if that form changes;
     the static soundness proof will fail in that case."))
  (and (resulterrp x)
       (b* ((info (fty::resulterr->info x)))
         (and (consp info)
              (eq (car info) :limit)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; modes

(defruled mode-continue-lemma
  (implies (modep mode)
           (equal (equal (mode-kind mode) :continue)
                  (equal mode (mode-continue)))))

(defruled mode-break-lemma
  (implies (modep mode)
           (equal (equal (mode-kind mode) :break)
                  (equal mode (mode-break)))))

(defruled mode-regular-lemma
  (implies (modep mode)
           (equal (equal (mode-kind mode) :regular)
                  (equal mode (mode-regular)))))

(defruled mode-leave-lemma
  (implies (modep mode)
           (equal (equal (mode-kind mode) :leave)
                  (equal mode (mode-leave)))))

(defrule mode-regular-not-continue
  (not (equal (mode-regular)
              (mode-continue))))

(defrule mode-regular-not-break
  (not (equal (mode-regular)
              (mode-break))))

(defrule mode-leave-not-continue
  (not (equal (mode-leave)
              (mode-continue))))

(defrule mode-leave-not-break
  (not (equal (mode-leave)
              (mode-break))))

(defruled mode-leave-if-not-regular/continue/break
  (implies (and (modep mode)
                (not (equal mode (mode-regular)))
                (not (equal mode (mode-continue)))
                (not (equal mode (mode-break))))
           (equal (equal mode (mode-leave))
                  t)))

(defruled mode-possibilities
  (implies (modep x)
           (or (equal x (mode-regular))
               (equal x (mode-leave))
               (equal x (mode-break))
               (equal x (mode-continue)))))

(defruled mode-lemma
  (implies (and (set::in (soutcome->mode outcome) modes)
                (not (equal (soutcome->mode outcome) (mode-break)))
                (not (equal (soutcome->mode outcome) (mode-continue)))
                (not (set::in (mode-leave) modes)))
           (equal (soutcome->mode outcome) (mode-regular)))
  :use (:instance mode-possibilities (x (soutcome->mode outcome)))
  :disable (equal-of-mode-leave
            equal-of-mode-continue
            equal-of-mode-break
            equal-of-mode-regular))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; extension of static safety checks to lists of function definitions

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; extension of check-var to lists

(define check-var-list ((vars identifier-listp) (vartab vartablep))
  :returns (yes/no booleanp)
  (or (endp vars)
      (and (check-var (car vars) vartab)
           (check-var-list (cdr vars) vartab)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; function tables

(define funinfo-to-funtype ((funinfo funinfop))
  :returns (ftype funtypep)
  (b* (((funinfo funinfo) funinfo))
    (make-funtype :in (len funinfo.inputs) :out (len funinfo.outputs)))
  :hooks (:fix))

(define funscope-to-funtable ((funscope funscopep))
  :returns (funtab funtablep)
  (b* ((funscope (funscope-fix funscope))
       ((when (omap::empty funscope)) nil)
       ((mv name funinfo) (omap::head funscope))
       (funtab (funscope-to-funtable (omap::tail funscope))))
    (omap::update name (funinfo-to-funtype funinfo) funtab))
  :verify-guards :after-returns
  :hooks (:fix)
  ///

  (defrule in-funscope-to-funtable-iff-in-funscope
    (equal (consp (omap::in fun (funscope-to-funtable funscope)))
           (consp (omap::in fun (funscope-fix funscope)))))

  (defruled funscope-to-funtable-of-update
    (implies (and (identifierp fun)
                  (funinfop info)
                  (funscopep funscope))
             (equal (funscope-to-funtable (omap::update fun info funscope))
                    (omap::update fun
                                  (funinfo-to-funtype info)
                                  (funscope-to-funtable funscope))))
    :enable (funscopep
             omap::update
             omap::head
             omap::tail
             omap::mapp)
    :disable (omap::weak-update-induction
              omap::use-weak-update-induction)
    :expand ((funscope-to-funtable (cons (car funscope)
                                         (omap::update fun
                                                       info
                                                       (cdr funscope))))))

  (defrule keys-of-funscope-to-funtable
    (equal (omap::keys (funscope-to-funtable funscope))
           (omap::keys (funscope-fix funscope)))))

(define funenv-to-funtable ((funenv funenvp))
  :returns (funtab funtablep)
  (b* (((when (endp funenv)) nil)
       (funtab-cdr (funenv-to-funtable (cdr funenv)))
       (funtab-car (funscope-to-funtable (car funenv))))
    (omap::update* funtab-car funtab-cdr))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; function addition

(defrule funinfo-to-funtype-of-funinfo-for-fundef
  (equal (funinfo-to-funtype (funinfo-for-fundef fundef))
         (funtype-for-fundef fundef))
  :enable (funinfo-to-funtype
           funinfo-for-fundef
           funtype-for-fundef))

(defruled in-funscope-for-fundefs-iff-in-funtable-for-fundefs
  (implies (and (not (resulterrp (funscope-for-fundefs fundefs)))
                (not (resulterrp (funtable-for-fundefs fundefs))))
           (equal (consp (omap::in fun (funscope-for-fundefs fundefs)))
                  (consp (omap::in fun (funtable-for-fundefs fundefs)))))
  :enable (funscope-for-fundefs
           funtable-for-fundefs))

(defruled error-funscope-for-fundefs-iff-error-funtable-for-fundefs
  (equal (resulterrp (funscope-for-fundefs fundefs))
         (resulterrp (funtable-for-fundefs fundefs)))
  :enable (funscope-for-fundefs
           funtable-for-fundefs
           funtablep-when-funtable-resultp-and-not-resulterrp
           not-resulterrp-when-funtablep
           in-funscope-for-fundefs-iff-in-funtable-for-fundefs))

(defrule funscope-to-funtable-of-funscope-for-fundefs
  (implies (not (resulterrp (funscope-for-fundefs fundefs)))
           (equal (funscope-to-funtable (funscope-for-fundefs fundefs))
                  (funtable-for-fundefs fundefs)))
  :enable (funscope-to-funtable
           funscope-for-fundefs
           funtable-for-fundefs
           error-funscope-for-fundefs-iff-error-funtable-for-fundefs
           funscopep-when-funscope-resultp-and-not-resulterrp
           funscope-to-funtable-of-update
           in-funscope-for-fundefs-iff-in-funtable-for-fundefs))

(defruled keys-of-funscope-for-fundefs-is-keys-of-funtable-for-fundefs
  (implies (and (not (resulterrp (funscope-for-fundefs fundefs)))
                (not (resulterrp (funtable-for-fundefs fundefs))))
           (equal (omap::keys (funscope-for-fundefs fundefs))
                  (omap::keys (funtable-for-fundefs fundefs))))
  :enable (funscope-for-fundefs
           funtable-for-fundefs))

(defrule funenv-to-funtable-of-add-funs
  (implies (not (resulterrp (add-funs fundefs funenv)))
           (equal (funenv-to-funtable (add-funs fundefs funenv))
                  (add-funtypes fundefs (funenv-to-funtable funenv))))
  :enable (add-funs
           add-funtypes
           funenv-to-funtable
           error-funscope-for-fundefs-iff-error-funtable-for-fundefs
           ensure-funscope-disjoint
           not-resulterrp-when-funenvp
           funscopep-when-funscope-resultp-and-not-resulterrp
           keys-of-funscope-for-fundefs-is-keys-of-funtable-for-fundefs
           set::intersect-of-union))

(defruled error-add-funs-iff-error-add-funtypes
  (equal (resulterrp (add-funs fundefs funenv))
         (resulterrp (add-funtypes fundefs (funenv-to-funtable funenv))))
  :enable (add-funs
           add-funtypes
           funenv-to-funtable
           error-funscope-for-fundefs-iff-error-funtable-for-fundefs
           ensure-funscope-disjoint
           not-resulterrp-when-funenvp
           funscopep-when-funscope-resultp-and-not-resulterrp
           keys-of-funscope-for-fundefs-is-keys-of-funtable-for-fundefs
           set::intersect-of-union
           funtablep-when-funtable-resultp-and-not-resulterrp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; variable tables

(defruled vartablep-to-identifier-setp
  (equal (vartablep x)
         (identifier-setp x))
  :enable (vartablep identifier-setp))

(defrule vartable-fix-when-identifier-setp
  (implies (identifier-setp x)
           (equal (vartable-fix x)
                  x))
  :enable vartablep-to-identifier-setp)

(define cstate-to-vartable ((cstate cstatep))
  :returns (vartab vartablep)
  (omap::keys (cstate->local cstate))
  :hooks (:fix)
  :prepwork ((local (in-theory (enable vartablep-to-identifier-setp)))))

(defruled cstate-to-vartable-fold-def
  (equal (omap::keys (cstate->local cstate))
         (cstate-to-vartable cstate))
  :enable cstate-to-vartable)

(defrule identifier-set-fix-of-cstate-to-vartable
  (equal (identifier-set-fix (cstate-to-vartable cstate))
         (cstate-to-vartable cstate))
  :use (:instance vartablep-to-identifier-setp (x (cstate-to-vartable cstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; soundness of literal execution

(defruled exec-literal-when-check-safe-literal
  (implies (not (resulterrp (check-safe-literal lit)))
           (b* ((outcome (exec-literal lit cstate)))
             (and (not (resulterrp outcome))
                  (equal (eoutcome->cstate outcome)
                         (cstate-fix cstate))
                  (equal (len (eoutcome->values outcome))
                         1))))
  :enable (check-safe-literal
           exec-literal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; soundness of variable execution

(defruled read-var-value-when-check-var
  (implies (check-var var (cstate-to-vartable cstate))
           (not (resulterrp (read-var-value var cstate))))
  :enable (check-var
           read-var-value
           not-resulterrp-when-valuep
           cstate-to-vartable
           vartablep-to-identifier-setp
           omap::consp-of-omap-in-to-set-in-of-omap-keys))

(defruled exec-path-when-check-safe-path
  (implies (not (resulterrp (check-safe-path path (cstate-to-vartable cstate))))
           (b* ((outcome (exec-path path cstate)))
             (and (not (resulterrp outcome))
                  (equal (eoutcome->cstate outcome)
                         (cstate-fix cstate))
                  (equal (len (eoutcome->values outcome))
                         1))))
  :enable (check-safe-path
           exec-path
           path-to-var
           not-resulterrp-when-valuep
           not-resulterrp-when-identifierp
           read-var-value-when-check-var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; variable table extension by static semantics

(defrule subset-of-add-var
  (implies (vartablep vartab)
           (b* ((vartab1 (add-var var vartab)))
             (implies (not (resulterrp vartab1))
                      (set::subset vartab vartab1))))
  :enable add-var)

(defrule subset-of-add-vars
  (implies (vartablep vartab)
           (b* ((vartab1 (add-vars vars vartab)))
             (implies (not (resulterrp vartab1))
                      (set::subset vartab vartab1))))
  :enable (add-vars
           set::subset-transitive))

(defrule check-safe-variable-single-extends-vartable
  (implies (vartablep vartab)
           (b* ((vartab1 (check-safe-variable-single name init vartab funtab)))
             (implies (not (resulterrp vartab1))
                      (set::subset vartab vartab1))))
  :enable check-safe-variable-single)

(defrule check-safe-variable-multi-extends-vartable
  (implies (vartablep vartab)
           (b* ((vartab1 (check-safe-variable-multi name init vartab funtab)))
             (implies (not (resulterrp vartab1))
                      (set::subset vartab vartab1))))
  :enable check-safe-variable-multi)

(defthm-check-safe-statements/blocks/cases/fundefs-flag

  (defthm check-safe-statement-extends-vartable
    (implies
     (vartablep vartab)
     (b* ((vartab-modes (check-safe-statement stmt vartab funtab)))
       (implies (not (resulterrp vartab-modes))
                (set::subset vartab
                             (vartable-modes->variables vartab-modes)))))
    :flag check-safe-statement)

  (defthm check-safe-statement-list-extends-vartable
    (implies
     (vartablep vartab)
     (b* ((vartab-modes (check-safe-statement-list stmts vartab funtab)))
       (implies (not (resulterrp vartab-modes))
                (set::subset vartab
                             (vartable-modes->variables vartab-modes)))))
    :flag check-safe-statement-list)

  (defthm check-safe-block-extends-vartable
    t
    :rule-classes nil
    :flag check-safe-block)

  (defthm check-safe-block-option-extends-vartable
    t
    :rule-classes nil
    :flag check-safe-block-option)

  (defthm check-safe-swcase-extends-vartable
    t
    :rule-classes nil
    :flag check-safe-swcase)

  (defthm check-safe-swcase-list-extends-vartable
    t
    :rule-classes nil
    :flag check-safe-swcase-list)

  (defthm check-safe-fundef-extends-vartable
    t
    :rule-classes nil
    :flag check-safe-fundef)

  :hints (("Goal"
           :in-theory
           (enable check-safe-statement
                   check-safe-statement-list
                   set::subset-transitive
                   vartablep-when-vartable-resultp-and-not-resulterrp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; variable restriction on variable table

(defrule cstate-to-vartable-of-restrict-vars
  (equal (cstate-to-vartable (restrict-vars vars cstate))
         (set::intersect (identifier-set-fix vars)
                         (cstate-to-vartable cstate)))
  :enable (cstate-to-vartable
           restrict-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; variable writing on variable table

(defrule cstate-to-vartable-of-write-var-value
  (b* ((cstate1 (write-var-value var val cstate)))
    (implies (not (resulterrp cstate1))
             (equal (cstate-to-vartable cstate1)
                    (cstate-to-vartable cstate))))
  :enable (write-var-value
           cstate-to-vartable
           omap::consp-of-omap-in-to-set-in-of-omap-keys))

(defrule cstate-to-vartable-of-write-vars-values
  (b* ((cstate1 (write-vars-values vars vals cstate)))
    (implies (not (resulterrp cstate1))
             (equal (cstate-to-vartable cstate1)
                    (cstate-to-vartable cstate))))
  :enable write-vars-values)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; variable addition on variable table

(defrule cstate-to-vartable-of-add-var-value
  (b* ((cstate1 (add-var-value var val cstate)))
    (implies (not (resulterrp cstate1))
             (equal (cstate-to-vartable cstate1)
                    (set::insert (identifier-fix var)
                                 (cstate-to-vartable cstate)))))
  :enable (add-var-value
           cstate-to-vartable))

(defrule cstate-to-vartable-of-add-vars-values
  (b* ((cstate1 (add-vars-values vars vals cstate)))
    (implies (not (resulterrp cstate1))
             (equal (cstate-to-vartable cstate1)
                    (set::list-insert (identifier-list-fix vars)
                                      (cstate-to-vartable cstate)))))
  :enable (add-vars-values
           set::list-insert))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; variable table manipulation by dynamic semantics

(defrule cstate-to-vartable-of-exec-literal
  (b* ((outcome (exec-literal lit cstate)))
    (implies (not (resulterrp outcome))
             (equal (cstate-to-vartable (eoutcome->cstate outcome))
                    (cstate-to-vartable cstate))))
  :enable exec-literal)

(defrule cstate-to-vartable-of-exec-path
  (b* ((outcome (exec-path path cstate)))
    (implies (not (resulterrp outcome))
             (equal (cstate-to-vartable (eoutcome->cstate outcome))
                    (cstate-to-vartable cstate))))
  :enable exec-path)

(defthm-exec-flag

  (defthm cstate-to-vartable-of-exec-expression
    (b* ((outcome (exec-expression expr cstate funenv limit)))
      (implies (not (resulterrp outcome))
               (equal (cstate-to-vartable (eoutcome->cstate outcome))
                      (cstate-to-vartable cstate))))
    :flag exec-expression)

  (defthm cstate-to-vartable-of-exec-expression-list
    (b* ((outcome (exec-expression-list exprs cstate funenv limit)))
      (implies (not (resulterrp outcome))
               (equal (cstate-to-vartable (eoutcome->cstate outcome))
                      (cstate-to-vartable cstate))))
    :flag exec-expression-list)

  (defthm cstate-to-vartable-of-exec-funcall
    (b* ((outcome (exec-funcall call cstate funenv limit)))
      (implies (not (resulterrp outcome))
               (equal (cstate-to-vartable (eoutcome->cstate outcome))
                      (cstate-to-vartable cstate))))
    :flag exec-funcall)

  (defthm cstate-to-vartable-of-exec-function
    (b* ((outcome (exec-function fun args cstate funenv limit)))
      (implies (not (resulterrp outcome))
               (equal (cstate-to-vartable (eoutcome->cstate outcome))
                      (cstate-to-vartable cstate))))
    :flag exec-function)

  (defthm cstate-to-vartable-of-exec-statement
    (b* ((outcome (exec-statement stmt cstate funenv limit)))
      (implies (not (resulterrp outcome))
               (set::subset (cstate-to-vartable cstate)
                            (cstate-to-vartable
                             (soutcome->cstate outcome)))))
    :flag exec-statement)

  (defthm cstate-to-vartable-of-exec-statement-list
    (b* ((outcome (exec-statement-list stmts cstate funenv limit)))
      (implies (not (resulterrp outcome))
               (set::subset (cstate-to-vartable cstate)
                            (cstate-to-vartable
                             (soutcome->cstate outcome)))))
    :flag exec-statement-list)

  (defthm cstate-to-vartable-of-exec-block
    (b* ((outcome (exec-block block cstate funenv limit)))
      (implies (not (resulterrp outcome))
               (equal (cstate-to-vartable (soutcome->cstate outcome))
                      (cstate-to-vartable cstate))))
    :flag exec-block)

  (defthm cstate-to-vartable-of-exec-for-iterations
    (b* ((outcome (exec-for-iterations test update body cstate funenv limit)))
      (implies (not (resulterrp outcome))
               (equal (cstate-to-vartable (soutcome->cstate outcome))
                      (cstate-to-vartable cstate))))
    :flag exec-for-iterations)

  (defthm cstate-to-vartable-of-exec-switch-rest
    (b* ((outcome (exec-switch-rest cases default target cstate funenv limit)))
      (implies (not (resulterrp outcome))
               (equal (cstate-to-vartable (soutcome->cstate outcome))
                      (cstate-to-vartable cstate))))
    :flag exec-switch-rest)

  :hints (("Goal" :in-theory (enable exec-expression
                                     exec-expression-list
                                     exec-funcall
                                     exec-function
                                     exec-statement
                                     exec-statement-list
                                     exec-block
                                     exec-for-iterations
                                     exec-switch-rest
                                     set::subset-transitive
                                     cstate-to-vartable-fold-def
                                     set::intersect-with-subset-left))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; soundness of variable addition

(defrule add-var-value-when-add-var
  (b* ((vartab1 (add-var var (cstate-to-vartable cstate)))
       (cstate1 (add-var-value var val cstate)))
    (implies (not (resulterrp vartab1))
             (and (not (resulterrp cstate1))
                  (equal (cstate-to-vartable cstate1)
                         vartab1))))
  :enable (add-var
           add-var-value
           cstate-to-vartable
           vartablep-to-identifier-setp
           omap::consp-of-omap-in-to-set-in-of-omap-keys))

(defrule add-vars-values-when-add-vars
  (b* ((vartab1 (add-vars vars (cstate-to-vartable cstate)))
       (cstate1 (add-vars-values vars vals cstate)))
    (implies (and (not (resulterrp vartab1))
                  (equal (len vals) (len vars)))
             (and (not (resulterrp cstate1))
                  (equal (cstate-to-vartable cstate1)
                         vartab1))))
  :induct (add-vars-values vars vals cstate)
  :enable (add-vars
           add-vars-values
           add-var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; soundness of variable writing

(defrule path-to-var-when-check-safe-path
  (implies (not (resulterrp (check-safe-path path vartab)))
           (not (resulterrp (path-to-var path))))
  :enable (check-safe-path
           path-to-var
           not-resulterrp-when-identifierp))

(defrule check-var-when-check-safe-path
  (implies (not (resulterrp (check-safe-path path vartab)))
           (check-var (path-to-var path) vartab))
  :enable (check-safe-path
           path-to-var))

(defrule paths-to-vars-when-check-safe-path-list
  (implies (not (resulterrp (check-safe-path-list paths vartab)))
           (not (resulterrp (paths-to-vars paths))))
  :enable (check-safe-path-list
           paths-to-vars)
  :expand (resulterrp (cons (path-to-var (car paths))
                            (paths-to-vars (cdr paths)))))

(defrule check-var-list-when-check-safe-path-list
  (implies (not (resulterrp (check-safe-path-list paths vartab)))
           (check-var-list (paths-to-vars paths) vartab))
  :enable (check-safe-path-list
           check-var-list
           paths-to-vars))

(defrule write-var-value-when-check-var
  (implies (check-var var (cstate-to-vartable cstate))
           (not (resulterrp (write-var-value var val cstate))))
  :enable (write-var-value
           check-var
           cstate-to-vartable
           vartablep-to-identifier-setp
           omap::consp-of-omap-in-to-set-in-of-omap-keys))

(defrule write-var-value-when-check-safe-path
  (implies (not (resulterrp
                 (check-safe-path path (cstate-to-vartable cstate))))
           (not (resulterrp
                 (write-var-value (path-to-var path) val cstate)))))

(defrule write-vars-values-when-check-var-list
  (implies (and (check-var-list vars (cstate-to-vartable cstate))
                (equal (len vals) (len vars)))
           (not (resulterrp (write-vars-values vars vals cstate))))
  :enable (check-var-list
           write-vars-values))

(defrule write-vars-values-when-check-safe-path-list
  (implies (and (not (resulterrp
                      (check-safe-path-list paths (cstate-to-vartable cstate))))
                (equal (len vals) (len paths)))
           (not (resulterrp
                 (write-vars-values (paths-to-vars paths) vals cstate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; safety of function environments

(define funinfo-safep ((funinfo funinfop) (funtab funtablep))
  :returns (yes/no booleanp)
  (b* (((funinfo funinfo) funinfo)
       (vartab (add-vars (append funinfo.inputs funinfo.outputs) nil))
       ((when (resulterrp vartab)) nil)
       (modes (check-safe-block funinfo.body vartab funtab))
       ((when (resulterrp modes)) nil)
       ((when (set::in (mode-break) modes)) nil)
       ((when (set::in (mode-continue) modes)) nil))
    t)
  :hooks (:fix))

(define funscope-safep ((funscope funscopep) (funtab funtablep))
  :returns (yes/no booleanp)
  (b* (((when (or (not (mbt (funscopep funscope)))
                  (omap::empty funscope)))
        t)
       ((mv & info) (omap::head funscope)))
    (and (funinfo-safep info funtab)
         (funscope-safep (omap::tail funscope) funtab)))
  :hooks (:fix)
  ///

  (defrule funscope-safep-of-update
    (implies (and (identifierp fun)
                  (funinfop funinfo)
                  (funscopep funscope)
                  (funinfo-safep funinfo funtab)
                  (funscope-safep funscope funtab))
             (funscope-safep (omap::update fun funinfo funscope) funtab))
    :enable (funscopep
             omap::update
             omap::head
             omap::tail)))

(define funenv-safep ((funenv funenvp))
  :returns (yes/no booleanp)
  (or (endp funenv)
      (and (funscope-safep (car funenv) (funenv-to-funtable funenv))
           (funenv-safep (cdr funenv))))
  :hooks (:fix))

(defruled check-safe-block-when-funscope-safep
  (implies (and (identifierp fun)
                (funscopep funscope)
                (funscope-safep funscope funtab)
                (consp (omap::in fun funscope)))
           (b* ((funinfo (cdr (omap::in fun funscope)))
                (vartab (add-vars
                         (append (funinfo->inputs funinfo)
                                 (funinfo->outputs funinfo))
                         nil))
                (modes (check-safe-block (funinfo->body funinfo)
                                         vartab
                                         funtab)))
             (and (not (resulterrp vartab))
                  (not (resulterrp modes))
                  (not (set::in (mode-break) modes))
                  (not (set::in (mode-continue) modes)))))
  :enable (funscope-safep
           funinfo-safep))

(defruled check-safe-block-when-funenv-safep
  (b* ((funinfoenv (find-fun fun funenv)))
    (implies (and (funenv-safep funenv)
                  (not (resulterrp funinfoenv)))
             (b* ((funinfo (funinfo+funenv->info funinfoenv))
                  (funenv1 (funinfo+funenv->env funinfoenv))
                  (vartab (add-vars
                           (append (funinfo->inputs funinfo)
                                   (funinfo->outputs funinfo))
                           nil))
                  (modes (check-safe-block (funinfo->body funinfo)
                                           vartab
                                           (funenv-to-funtable funenv1))))
               (and (not (resulterrp vartab))
                    (not (resulterrp modes))
                    (not (set::in (mode-break) modes))
                    (not (set::in (mode-continue) modes))
                    (funenv-safep funenv1)))))
  :enable (find-fun
           funenv-safep)
  :hints ('(:use (:instance check-safe-block-when-funscope-safep
            (fun (identifier-fix fun))
            (funscope (funscope-fix (car funenv)))
            (funtab (funenv-to-funtable funenv))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; treatment of init-local

(defruled add-var-to-insert
  (b* ((vartab1 (add-var var vartab)))
    (implies (not (resulterrp vartab1))
             (equal vartab1
                    (set::insert (identifier-fix var)
                                 (vartable-fix vartab)))))
  :enable add-var)

(defruled add-vars-to-list-insert
  (b* ((vartab1 (add-vars vars vartab)))
    (implies (not (resulterrp vartab1))
             (equal vartab1
                    (set::list-insert (identifier-list-fix vars)
                                      (vartable-fix vartab)))))
  :enable (add-vars
           set::list-insert
           add-var-to-insert))

(defruled add-vars-of-append
  (implies (and (not (resulterrp (add-vars vars1 vartab)))
                (not (resulterrp (add-vars vars2 (add-vars vars1 vartab)))))
           (equal (add-vars (append vars1 vars2) vartab)
                  (add-vars vars2 (add-vars vars1 vartab))))
  :enable (add-vars))

(defruled error-add-var-value-iff-error-add-var
  (equal (resulterrp (add-var-value var val cstate))
         (resulterrp (add-var var (cstate-to-vartable cstate))))
  :enable (add-var
           add-var-value
           cstate-to-vartable
           omap::consp-of-omap-in-to-set-in-of-omap-keys
           not-resulterrp-when-cstatep
           not-resulterrp-when-vartablep
           vartablep-to-identifier-setp))

(defruled error-add-vars-values-iff-error-add-vars
  (implies (equal (len vals) (len vars))
           (equal (resulterrp (add-vars-values vars vals cstate))
                  (resulterrp (add-vars vars (cstate-to-vartable cstate)))))
  :enable (add-vars-values
           add-vars
           error-add-var-value-iff-error-add-var
           not-resulterrp-when-vartablep))

(defrule cstate-to-vartable-of-init-local
  (implies (and (equal (len in-vals)
                       (len in-vars))
                (not (resulterrp (init-local in-vars in-vals out-vars cstate))))
           (equal (cstate-to-vartable
                   (init-local in-vars in-vals out-vars cstate))
                  (add-vars (append in-vars out-vars) nil)))
  :enable (init-local
           add-vars-of-append
           error-add-vars-values-iff-error-add-vars))

(defruled same-len-when-add-vars-values-not-error
  (implies (not (resulterrp (add-vars-values vars vals cstate)))
           (equal (len vals) (len vars)))
  :enable add-vars-values)

(defrule same-len-when-init-local-not-error
  (implies (not (resulterrp (init-local in-vars in-vals out-vars cstate)))
           (equal (len in-vals) (len in-vars)))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((resulterrp
                    (init-local in-vars in-vals out-vars cstate)))))
  :enable init-local
  :use (:instance same-len-when-add-vars-values-not-error
        (vals in-vals)
        (vars in-vars)
        (cstate (cstate nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; theorems about add-funs

(defrule car-of-add-funs
  (implies (not (resulterrp (add-funs fundefs funenv)))
           (equal (car (add-funs fundefs funenv))
                  (funscope-for-fundefs fundefs)))
  :enable add-funs)

(defrule cdr-of-add-funs
  (implies (not (resulterrp (add-funs fundefs funenv)))
           (equal (cdr (add-funs fundefs funenv))
                  (funenv-fix funenv)))
  :enable add-funs)

(defruled not-error-funscope-for-fundefs-when-not-error-add-funs
  (implies (not (resulterrp (add-funs fundefs funenv)))
           (not (resulterrp (funscope-for-fundefs fundefs))))
  :enable add-funs)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; function environment safety under safety checking

(defrule funinfo-safep-of-funinfo-for-fundef
  (implies (not (resulterrp (check-safe-fundef fundef funtab)))
           (funinfo-safep (funinfo-for-fundef fundef) funtab))
  :enable (funinfo-safep
           check-safe-fundef
           funinfo-for-fundef))

(defrule funscope-safep-of-funscope-for-fundefs
  (implies (and (not (resulterrp (check-safe-fundef-list fundefs funtab)))
                (not (resulterrp (funscope-for-fundefs fundefs))))
           (funscope-safep (funscope-for-fundefs fundefs) funtab))
  :enable (funscope-safep
           funscope-for-fundefs
           check-safe-fundef-list
           funscopep-when-funscope-resultp-and-not-resulterrp))

(defrule funenv-safep-of-add-funs
  (implies (and (funenv-safep funenv)
                (not (resulterrp (add-funs fundefs funenv)))
                (not (resulterrp
                      (check-safe-fundef-list
                       fundefs
                       (add-funtypes fundefs (funenv-to-funtable funenv))))))
           (funenv-safep (add-funs fundefs funenv)))
  :expand (funenv-safep (add-funs fundefs funenv))
  :enable (not-error-funscope-for-fundefs-when-not-error-add-funs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; function finding

(defruled len-of-funinfo->inputs
  (equal (len (funinfo->inputs funinfo))
         (funtype->in (funinfo-to-funtype funinfo)))
  :enable funinfo-to-funtype)

(defruled len-of-funinfo->outputs
  (equal (len (funinfo->outputs funinfo))
         (funtype->out (funinfo-to-funtype funinfo)))
  :enable funinfo-to-funtype)

(defrule funinfo-to-fun-type-of-cdr-of-in
  (implies (and (funscopep funscope)
                (consp (omap::in fun funscope)))
           (equal (funinfo-to-funtype (cdr (omap::in fun funscope)))
                  (cdr (omap::in fun (funscope-to-funtable funscope)))))
  :enable funscope-to-funtable)

(defrule funinfo-to-funtype-of-find-fun-info
  (b* ((funinfoenv (find-fun fun funenv))
       (funtype (get-funtype fun (funenv-to-funtable funenv))))
    (implies (not (resulterrp funinfoenv))
             (b* ((funinfo (funinfo+funenv->info funinfoenv)))
               (and (not (resulterrp funtype))
                    (equal (funinfo-to-funtype funinfo)
                           funtype)))))
  :expand (funenv-to-funtable funenv)
  :enable (find-fun
           funenv-to-funtable
           get-funtype
           not-resulterrp-when-funtypep
           funtypep-when-funtype-resultp-and-not-resulterrp)
  :prep-lemmas
  ((defrule lemma
     (implies (and (funtablep funtab)
                   (consp (omap::in fun funtab)))
              (funtypep (cdr (omap::in fun funtab)))))))

(defrule in-of-funscope-to-funtable
  (iff (omap::in fun (funscope-to-funtable funscope))
       (omap::in fun (funscope-fix funscope)))
  :enable funscope-to-funtable)

(defruled resulterrp-of-find-fun
  (equal (resulterrp (find-fun fun funenv))
         (resulterrp (get-funtype fun (funenv-to-funtable funenv))))
  :enable (funenv-to-funtable
           find-fun
           get-funtype
           not-resulterrp-when-funinfo+funenv-p
           not-resulterrp-when-funtypep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lemmas for the exec-function case

(defruled read-vars-values-when-check-var-list
  (implies (check-var-list vars (cstate-to-vartable cstate))
           (not (resulterrp (read-vars-values vars cstate))))
  :enable (check-var-list
           read-vars-values
           valuep-when-value-resultp-and-not-resulterrp
           not-resulterrp-when-value-listp
           value-listp-when-value-list-resultp-and-not-resulterrp))

(defruled add-vars-to-set-list-insert
  (implies (and (identifier-listp vars)
                (vartablep vartab)
                (not (resulterrp (add-vars vars vartab))))
           (equal (add-vars vars vartab)
                  (set::list-insert vars vartab)))
  :enable (add-vars
           add-var
           set::list-insert))

(defruled check-var-list-to-set-list-in
  (implies (and (identifier-listp vars)
                (vartablep vartab))
           (equal (check-var-list vars vartab)
                  (set::list-in vars vartab)))
  :enable (check-var-list
           check-var
           set::list-in))

(defrule identifier-setp-of-list-insert
  (implies (and (identifier-listp list)
                (identifier-setp set))
           (identifier-setp (set::list-insert list set)))
  :enable set::list-insert)

(defruled check-var-list-of-add-vars-of-append-not-error
  (implies (and (identifier-listp vars)
                (identifier-listp vars1)
                (vartablep vartab)
                (not (resulterrp (add-vars (append vars1 vars) vartab))))
           (check-var-list vars (add-vars (append vars1 vars) vartab)))
  :enable (add-vars-to-set-list-insert
           check-var-list-to-set-list-in
           vartablep-to-identifier-setp))

(defruled add-vars-of-append-not-error-when-init-local-not-error
  (implies (and (not (resulterrp
                      (init-local in-vars in-vals out-vars cstate))))
           (not (resulterrp (add-vars (append in-vars out-vars) nil))))
  :enable not-resulterrp-when-vartablep
  :disable cstate-to-vartable-of-init-local
  :use cstate-to-vartable-of-init-local)

(defruled resulterrp-of-add-vars-of-append
  (implies (resulterrp (add-vars vars vartab))
           (resulterrp (add-vars (append vars vars1) vartab)))
  :enable add-vars)

(defruled add-vars-of-append-2 ; see add-vars-of-append
  (implies (not (resulterrp (add-vars (append vars1 vars2) vartab)))
           (equal (add-vars (append vars1 vars2) vartab)
                  (add-vars vars2 (add-vars vars1 vartab))))
  :enable add-vars)

(defruled init-local-not-error-when-add-vars-of-append-not-error
  (implies (and (equal (len in-vals) (len in-vars))
                (not (resulterrp (add-vars (append in-vars out-vars) nil))))
           (not (resulterrp (init-local in-vars in-vals out-vars cstate))))
  :enable (init-local
           resulterrp-of-add-vars-of-append
           error-add-vars-values-iff-error-add-vars)
  :use (:instance add-vars-of-append-2
        (vars1 in-vars)
        (vars2 out-vars)
        (vartab nil)))

(defruled resulterrp-of-init-local
  (equal (resulterrp (init-local in-vars in-vals out-vars cstate))
         (or (resulterrp (add-vars (append in-vars out-vars) nil))
             (not (equal (len in-vals) (len in-vars)))))
  :use (add-vars-of-append-not-error-when-init-local-not-error
        init-local-not-error-when-add-vars-of-append-not-error))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; for funcall

(defrule resulterrp-of-check-safe-expression-list-of-append
  (equal (resulterrp (check-safe-expression-list (append es es1) vartab funtab))
         (or (resulterrp (check-safe-expression-list es vartab funtab))
             (resulterrp (check-safe-expression-list es1 vartab funtab))))
  :enable check-safe-expression-list)

(defrule resulterrp-of-check-safe-expression-list-of-rev
  (equal (resulterrp (check-safe-expression-list (rev es) vartab funtab))
         (resulterrp (check-safe-expression-list es vartab funtab)))
  :enable (check-safe-expression-list rev))

(defruled check-safe-expression-list-to-len
  (implies (not (resulterrp (check-safe-expression-list es vartab funtab)))
           (equal (check-safe-expression-list es vartab funtab) (len es)))
  :enable check-safe-expression-list)

; not ideal
(defruled check-safe-expression-list-not-error-when-rev
  (implies (not (resulterrp (check-safe-expression-list (rev es) vartab funtab)))
           (not (resulterrp (check-safe-expression-list es vartab funtab)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; for subgoal 77 (exec-block)
; (consider using subset here instead)
(defruled exec-statement-list-cstate-to-vartable-lemma
  (implies (and (not (resulterrp (add-funs (statements-to-fundefs stmts)
                                           funenv)))
                (not (resulterrp (exec-statement-list
                                  stmts
                                  cstate
                                  (add-funs (statements-to-fundefs stmts)
                                            funenv)
                                  limit))))
           (equal (intersect
                   (cstate-to-vartable cstate)
                   (cstate-to-vartable
                    (soutcome->cstate
                     (exec-statement-list stmts
                                          cstate
                                          (add-funs (statements-to-fundefs stmts)
                                                    funenv)
                                          limit))))
                  (cstate-to-vartable cstate)))
  :use (:instance cstate-to-vartable-of-exec-statement-list
        (cstate (add-funs (statements-to-fundefs stmts) funenv)))
  :enable set::intersect-with-subset-left)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm-exec-flag

  (defthm exec-expression-static-soundness
    (b* ((results (check-safe-expression expr
                                         (cstate-to-vartable cstate)
                                         (funenv-to-funtable funenv)))
         (outcome (exec-expression expr cstate funenv limit)))
      (implies (and (funenv-safep funenv)
                    (not (resulterrp results))
                    (not (resulterr-limitp outcome)))
               (and (not (resulterrp outcome))
                    (equal (cstate-to-vartable (eoutcome->cstate outcome))
                           (cstate-to-vartable cstate))
                    (equal (len (eoutcome->values outcome))
                           results))))
    :flag exec-expression)

  (defthm exec-expression-list-static-soundness
    (b* ((results (check-safe-expression-list exprs
                                              (cstate-to-vartable cstate)
                                              (funenv-to-funtable funenv)))
         (outcome (exec-expression-list exprs cstate funenv limit)))
      (implies (and (funenv-safep funenv)
                    (not (resulterrp results))
                    (not (resulterr-limitp outcome)))
               (and (not (resulterrp outcome))
                    (equal (cstate-to-vartable (eoutcome->cstate outcome))
                           (cstate-to-vartable cstate))
                    (equal (len (eoutcome->values outcome))
                           results))))
    :flag exec-expression-list)

  (defthm exec-funcall-static-soundness
    (b* ((results (check-safe-funcall call
                                      (cstate-to-vartable cstate)
                                      (funenv-to-funtable funenv)))
         (outcome (exec-funcall call cstate funenv limit)))
      (implies (and (funenv-safep funenv)
                    (not (resulterrp results))
                    (not (resulterr-limitp outcome)))
               (and (not (resulterrp outcome))
                    (equal (cstate-to-vartable (eoutcome->cstate outcome))
                           (cstate-to-vartable cstate))
                    (equal (len (eoutcome->values outcome))
                           results))))
    :flag exec-funcall)

  (defthm exec-function-static-soundness
    (b* ((ftype (get-funtype fun (funenv-to-funtable funenv)))
         (outcome (exec-function fun args cstate funenv limit)))
      (implies (and (funenv-safep funenv)
                    (not (resulterrp ftype))
                    (equal (len args)
                           (funtype->in ftype))
                    (not (resulterr-limitp outcome)))
               (and (not (resulterrp outcome))
                    (equal (cstate-to-vartable (eoutcome->cstate outcome))
                           (cstate-to-vartable cstate))
                    (equal (len (eoutcome->values outcome))
                           (funtype->out ftype)))))
    :flag exec-function)

  (defthm exec-statement-static-soundness
    (b* ((vartab-modes (check-safe-statement stmt
                                             (cstate-to-vartable cstate)
                                             (funenv-to-funtable funenv)))
         (outcome (exec-statement stmt cstate funenv limit)))
      (implies (and (funenv-safep funenv)
                    (not (resulterrp vartab-modes))
                    (not (resulterr-limitp outcome)))
               (and (not (resulterrp outcome))
                    (equal (cstate-to-vartable (soutcome->cstate outcome))
                           (vartable-modes->variables vartab-modes))
                    (set::in (soutcome->mode outcome)
                             (vartable-modes->modes vartab-modes)))))
    :flag exec-statement)

  (defthm exec-statement-list-static-soundness
    (b* ((vartab-modes (check-safe-statement-list stmts
                                                  (cstate-to-vartable cstate)
                                                  (funenv-to-funtable funenv)))
         (outcome (exec-statement-list stmts cstate funenv limit)))
      (implies (and (funenv-safep funenv)
                    (not (resulterrp vartab-modes))
                    (not (resulterr-limitp outcome)))
               (and (not (resulterrp outcome))
                    (if (equal (soutcome->mode outcome)
                               (mode-regular))
                        (equal (cstate-to-vartable (soutcome->cstate outcome))
                               (vartable-modes->variables vartab-modes))
                      (set::subset (cstate-to-vartable (soutcome->cstate outcome))
                                   (vartable-modes->variables vartab-modes)))
                    (set::in (soutcome->mode outcome)
                             (vartable-modes->modes vartab-modes)))))
    :flag exec-statement-list)

  (defthm exec-block-static-soundness
    (b* ((modes (check-safe-block block
                                  (cstate-to-vartable cstate)
                                  (funenv-to-funtable funenv)))
         (outcome (exec-block block cstate funenv limit)))
      (implies (and (funenv-safep funenv)
                    (not (resulterrp modes))
                    (not (resulterr-limitp outcome)))
               (and (not (resulterrp outcome))
                    (equal (cstate-to-vartable (soutcome->cstate outcome))
                           (cstate-to-vartable cstate))
                    (set::in (soutcome->mode outcome)
                             modes))))
    :flag exec-block)

  (defthm exec-for-iterations-static-soundness
    (b* ((test-results (check-safe-expression test
                                              (cstate-to-vartable cstate)
                                              (funenv-to-funtable funenv)))
         (update-modes (check-safe-block update
                                         (cstate-to-vartable cstate)
                                         (funenv-to-funtable funenv)))
         (body-modes (check-safe-block body
                                       (cstate-to-vartable cstate)
                                       (funenv-to-funtable funenv)))
         (outcome (exec-for-iterations test update body cstate funenv limit)))
      (implies (and (funenv-safep funenv)
                    (not (resulterrp test-results))
                    (equal test-results 1)
                    (not (resulterrp update-modes))
                    (not (set::in (mode-break) update-modes))
                    (not (set::in (mode-continue) update-modes))
                    (not (resulterrp body-modes))
                    (not (resulterr-limitp outcome)))
               (and (not (resulterrp outcome))
                    (equal (cstate-to-vartable (soutcome->cstate outcome))
                           (cstate-to-vartable cstate))
                    (set::in (soutcome->mode outcome)
                             (set::difference
                              (set::insert (mode-regular)
                                           (set::union body-modes update-modes))
                              (set::insert (mode-break)
                                           (set::insert (mode-continue)
                                                        nil)))))))
    :flag exec-for-iterations)

  (defthm exec-switch-rest-static-soundness
    (b* ((cases-modes (check-safe-swcase-list cases
                                              (cstate-to-vartable cstate)
                                              (funenv-to-funtable funenv)))
         (default-modes (check-safe-block-option default
                                                 (cstate-to-vartable cstate)
                                                 (funenv-to-funtable funenv)))
         (outcome (exec-switch-rest cases default target cstate funenv limit)))
      (implies (and (funenv-safep funenv)
                    (not (resulterrp cases-modes))
                    (not (resulterrp default-modes))
                    (not (resulterr-limitp outcome)))
               (and (not (resulterrp outcome))
                    (equal (cstate-to-vartable (soutcome->cstate outcome))
                           (cstate-to-vartable cstate))
                    (set::in (soutcome->mode outcome)
                             (set::union cases-modes default-modes)))))
    :flag exec-switch-rest)

  :hints (("Goal"
           :in-theory (e/d
                       (
                        exec-expression
                        exec-expression-list
                        exec-funcall
                        exec-function
                        exec-statement
                        exec-statement-list
                        exec-block
                        exec-for-iterations
                        exec-switch-rest

                        check-safe-expression
                        check-safe-expression-list
                        check-safe-funcall
                        check-safe-statement
                        check-safe-variable-single
                        check-safe-variable-multi
                        check-safe-assign-single
                        check-safe-assign-multi
                        check-safe-statement-list
                        check-safe-block
                        check-safe-block-option
                        check-safe-swcase
                        check-safe-swcase-list
                        check-safe-literal

                        exec-literal-when-check-safe-literal
                        exec-path-when-check-safe-path

                        resulterr-limitp

                        ;; for subgoal 86:
                        mode-continue-lemma
                        mode-break-lemma
                        mode-regular-lemma
                        mode-leave-lemma

                        ;; for subgoal 77:
                        cstate-to-vartable-fold-def ; works with next
                        exec-statement-list-cstate-to-vartable-lemma
                        error-add-funs-iff-error-add-funtypes
                        check-safe-fundef-list-of-statements-to-fundefs

                        ;; for subgoal 75:
                        error-add-funs-iff-error-add-funtypes

                        ;; for subgoal 63:
                        mode-setp-when-mode-set-resultp-and-not-resulterrp

                        ;; for subgoal 61:
                        mode-leave-if-not-regular/continue/break
                        mode-lemma

                        ;; for subgoal 35:
                        vartablep-when-vartable-resultp-and-not-resulterrp
                        funcall-option-some->val

                        ;; for subgoal 29:
                        expression-option-some->val

                        ;; for subgoal 21:
                        check-safe-block-when-funenv-safep
                        len-of-funinfo->inputs
                        len-of-funinfo->outputs

                        ;; for subgoal 20:
                        read-vars-values-when-check-var-list
                        check-var-list-of-add-vars-of-append-not-error

                        resulterrp-of-init-local ; replaces:
                        ;; add-vars-of-append-not-error-when-init-local-not-error

                        ;; for subgoal 15:
                        resulterrp-of-find-fun

                        ;; for subgoal 13:
                        check-safe-expression-list-to-len
                        check-safe-expression-list-not-error-when-rev
                        )
                       (
                        equal-of-mode-continue
                        equal-of-mode-break
                        equal-of-mode-regular
                        equal-of-mode-leave
                        ))
           :expand (
                    ;; for subgoal 68:
                    (check-safe-statement stmt
                                          (cstate-to-vartable cstate)
                                          (funenv-to-funtable funenv))
                    ))))
