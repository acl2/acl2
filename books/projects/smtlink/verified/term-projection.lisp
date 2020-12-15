;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (Feb 13th 2020)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/generalize" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "../utils/fresh-vars")
(include-book "basics")
;; (include-book "alist")
(include-book "hint-please")
(include-book "typed-term-fns")
(include-book "judgement-fns")
(include-book "type-options")

;; This clause-processor projections a term that uses alists into a term that
;; uses arrays. Supposedly other isomorphic projectionations can also be made in
;; a similar way.

(set-state-ok t)

;; ---------------------------------------------------------------
(encapsulate ()
  (local (in-theory (disable symbol-listp
                             acl2::pseudo-termp-opener
                             pseudo-term-listp-of-symbol-listp
                             consp-of-pseudo-lambdap
                             rational-listp
                             integer-listp)))

  ;; find the alist-array-equiv of term from projection
  ;; projection should be a conjunction of equivalence terms
  (define find-projection ((term pseudo-termp) (projection pseudo-termp))
    :returns (the-proj pseudo-termp)
    :measure (acl2-count (pseudo-term-fix projection))
    (b* ((term (pseudo-term-fix term))
         (projection (pseudo-term-fix projection))
         ((mv ok proj)
          (case-match projection
            (('alist-array-equiv !term &) (mv t projection))
            (& (mv nil nil))))
         ((if ok) proj)
         ((unless (is-conjunct? projection))
          (er hard? 'term-projection=>find-projection
              "Projection is not a conjunction: ~q0" projection))
         ((if (equal projection ''t)) nil)
         ((list & proj-hd proj-tl &) projection)
         (hd-res (find-projection term proj-hd))
         ((if hd-res) hd-res))
      (find-projection term proj-tl)))
  )

;; ---------------------------------------------------------------

(encapsulate ()
  (local
   (in-theory (disable assoc-equal symbol-listp lambda-of-pseudo-lambdap
                       consp-of-pseudo-lambdap
                       pseudo-lambdap-of-fn-call-of-pseudo-termp
                       consp-of-is-conjunct? default-cdr
                       acl2::true-listp-of-car-when-true-list-listp
                       true-list-listp true-listp)))

  ;; example: alist-term = (integer-integer-alistp x)
  ;; fresh-var = y
  ;; 1. Generate constraint: y = (alist-to-array-fn x)
  ;; 2. Use the theorem to establish (alist-array-equiv x y):
  ;; thm: (implies (and (integer-integer-alistp a)
  ;;                    (equal b (integer-integer-alist-to-array a)))
  ;;               (alist-array-equiv a b))
  (define new-projection ((alist-term pseudo-termp)
                          (fresh-var symbolp)
                          (options type-options-p)
                          state)
    :returns (new-proj pseudo-termp)
    :guard (and (consp alist-term)
                (symbolp (car alist-term))
                (not (equal (car alist-term) 'quote))
                (not (null (is-alist? (car alist-term) options))))
    (b* (((unless (mbt (and (pseudo-termp alist-term)
                            (symbolp fresh-var)
                            (type-options-p options)
                            (consp alist-term)
                            (symbolp (car alist-term))
                            (not (equal (car alist-term) 'quote))
                            (not (null (is-alist? (car alist-term) options))))))
          nil)
         ((type-options to) options)
         ((cons fn actuals) alist-term)
         (var (car actuals))
         (yes? (assoc-equal fn to.alist))
         ((unless yes?)
          (er hard? 'term-projection=>new-projection
              "An alist-info item is required for alist type: ~q0" fn))
         ((a2a-info a) (cdr yes?))
         (new-constraint `(alist-array-equiv ,fresh-var (,a.a2a-fn ,var)))
         (equiv-thm
          (acl2::meta-extract-formula-w a.thm (w state)))
         ((unless (pseudo-termp equiv-thm))
          (er hard? 'term-projection=>new-projection
              "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
              a.thm equiv-thm))
         ((mv ok proj)
          (case-match equiv-thm
            (('implies hypo ('alist-array-equiv !a.formals))
             (b* ((substed-hypo
                   (term-substitution hypo
                                      (pairlis$ a.formals
                                                `(,var ,fresh-var))
                                      t))
                  (yes? (path-test-list `(if ,alist-term ,new-constraint 'nil)
                                        substed-hypo state))
                  ((unless yes?) (mv nil nil)))
               (mv t `(alist-array-equiv ,var ,fresh-var))))
            (& (mv nil nil))))
         ((unless ok)
          (er hard? 'term-projection=>new-projection
              "Can't match the theorem: ~q0" equiv-thm)))
      proj))
  )

(encapsulate ()
  (local (in-theory (disable pseudo-termp consp-of-is-conjunct?
                             symbol-listp
                             equal-fixed-and-x-of-pseudo-termp
                             pseudo-term-listp-of-symbol-listp
                             lambda-of-pseudo-lambdap
                             acl2::symbol-listp-of-cdr-when-symbol-listp
                             acl2::pseudo-termp-cadr-from-pseudo-term-listp
                             acl2::symbol-listp-when-not-consp
                             pseudo-lambdap-of-fn-call-of-pseudo-termp)))

  (define generate-fncall-proj-cases ((fn symbolp)
                                      (tta typed-term-list-p)
                                      (ntta typed-term-list-p)
                                      (actuals-proj pseudo-termp)
                                      (hypo pseudo-termp)
                                      (concl pseudo-termp)
                                      (options type-options-p)
                                      state)
    :returns (mv (new-tt (good-typed-term-p new-tt options)
                         :hints (("Goal"
                                  :in-theory (enable good-typed-quote-p))))
                 (new-proj pseudo-termp))
    :guard (and (not (equal fn 'quote))
                (not (equal fn 'if))
                (good-typed-term-list-p tta options)
                (good-typed-term-list-p ntta options))
    :verify-guards nil
    (b* (((unless (mbt (and (symbolp fn)
                            (not (equal fn 'quote))
                            (not (equal fn 'if))
                            (typed-term-list-p tta)
                            (good-typed-term-list-p tta options)
                            (typed-term-list-p ntta)
                            (good-typed-term-list-p ntta options)
                            (pseudo-termp actuals-proj)
                            (pseudo-termp hypo)
                            (pseudo-termp concl)
                            (type-options-p options))))
          (mv (make-typed-term) nil))
         (tta.term-lst (typed-term-list->term-lst tta))
         (tta.judgements (typed-term-list->judgements tta))
         (ntta.term-lst (typed-term-list->term-lst ntta))
         (ntta.judgements (typed-term-list->judgements ntta))
         (ntta.path-cond (typed-term-list->path-cond ntta))
         ((type-options to) options)
         (all-known `(if ,tta.judgements
                         (if ,ntta.judgements
                             ,actuals-proj
                           'nil)
                       'nil))
         (yes? (path-test-list all-known hypo state))
         ((unless yes?)
          (prog2$ (er hard? 'term-projection=>generate-fncall-proj-cases
                      "Can't discharge the hypotheses: ~q0" hypo)
                  (mv (make-typed-term) nil)))
         (term `(,fn ,@tta.term-lst))
         (new-proj (find-projection term concl))
         ((mv ok new-tterm)
          (case-match new-proj
            (('alist-array-equiv !term new-term)
             (case-match new-term
               ((store-fn k (cons-fn k v) ar)
                (b* (((unless (and (symbolp store-fn)
                                   (symbolp cons-fn)
                                   (not (equal store-fn 'quote))
                                   (not (equal store-fn 'if))
                                   (not (equal cons-fn 'quote))
                                   (not (equal cons-fn 'if))
                                   (equal (len ntta) 3)))
                      (mv nil (make-typed-term)))
                     (cons-term `(,cons-fn ,k ,v))
                     (judge-cons-fn
                      (look-up-path-cond cons-term concl to.supertype))
                     (cons-top (make-typed-term :term cons-term
                                                :path-cond ntta.path-cond
                                                :judgements judge-cons-fn))
                     ((unless (and (equal k (typed-term->term (car ntta)))
                                   (equal v (typed-term->term (cadr ntta)))
                                   (equal ar (typed-term->term (caddr ntta)))))
                      (mv nil nil))
                     (cons-actuals (list (car ntta) (cadr ntta)))
                     (cons-tterm
                      (make-typed-fncall cons-top cons-actuals options))
                     (store-term `(,store-fn ,k (,cons-fn ,k ,v) ,ar))
                     (judge-store-fn
                      (look-up-path-cond store-term concl to.supertype))
                     (store-top
                      (make-typed-term :term store-term
                                       :path-cond ntta.path-cond
                                       :judgements judge-store-fn))
                     ;; should be able to prove this
                     ((unless (equal (typed-term->term cons-tterm)
                                     `(,cons-fn ,k ,v)))
                      (mv nil nil))
                     (store-actuals
                      (list (car ntta) cons-tterm (caddr ntta)))
                     (store-tterm
                      (make-typed-fncall store-top store-actuals options)))
                  (mv t store-tterm)))
               ((new-fn . !ntta.term-lst) ;; assumes the same order of actuals
                (b* (((unless (and (symbolp new-fn)
                                   (not (equal new-fn 'quote))
                                   (not (equal new-fn 'if))))
                      (mv nil (make-typed-term)))
                     (judge-new-term
                      (look-up-path-cond new-term concl to.supertype))
                     (top-tt (make-typed-term :term new-term
                                              :path-cond ntta.path-cond
                                              :judgements judge-new-term))
                     (new-tt (make-typed-fncall top-tt ntta options)))
                  (mv t new-tt)))
               ;; are there other cases?
               (& (mv nil nil))))
            (& (mv nil (make-typed-term)))))
         ((unless ok)
          (prog2$
           (er hard? 'term-projection=>generate-fncall-proj-cases
               "Malformed hypotheses and conclusion: ~p0 and ~p1~%"
               hypo concl)
           (mv (make-typed-term) nil))))
      (mv new-tterm new-proj)))
  )

(encapsulate ()
(local
 (defthm good-typed-term-list-of-two
   (implies (and (type-options-p options)
                 (good-typed-term-list-p ntta options)
                 (consp ntta)
                 (consp (cdr ntta)))
            (good-typed-term-list-p (list (car ntta) (cadr ntta))
                                    options))
   :hints (("Goal"
            :in-theory (enable good-typed-term-list-p
                               typed-term-list->path-cond)))))

(local
 (defthm good-typed-term-list-of-three
   (implies (and (type-options-p options)
                 (good-typed-term-list-p ntta options)
                 (consp ntta)
                 (consp (cdr ntta))
                 (equal (+ 2 (len (cddr ntta))) 3)
                 (good-typed-term-p x options)
                 (equal (typed-term->path-cond (car ntta))
                        (typed-term->path-cond x)))
            (good-typed-term-list-p (list (car ntta) x (caddr ntta))
                                    options))
   :hints (("Goal"
            :in-theory (enable good-typed-term-list-p
                               typed-term-list->path-cond)))))

(verify-guards generate-fncall-proj-cases
  :hints (("Goal"
           :in-theory (e/d (make-typed-fncall-guard
                            typed-term-list->path-cond
                            typed-term-list->term-lst)
                           (consp-of-is-conjunct? pseudo-termp
                            symbol-listp acl2::pseudo-termp-opener
                            pseudo-term-listp-of-symbol-listp
                            pseudo-lambdap-of-fn-call-of-pseudo-termp
                            acl2::true-listp-of-car-when-true-list-listp
                            true-list-listp pseudo-term-listp
                            consp-of-cdr-of-pseudo-lambdap
                            good-typed-term-list-of-three))
           :use ((:instance good-typed-term-list-of-three
                            (x (make-typed-fncall
                                (typed-term
                                 (list
                                  (car
                                   (caddr
                                    (caddr
                                     (find-projection
                                      (cons fn (typed-term-list->term-lst tta))
                                      concl))))
                                  (typed-term->term (car ntta))
                                  (typed-term->term (cadr ntta)))
                                 (typed-term->path-cond (car ntta))
                                 (look-up-path-cond
                                  (list
                                   (car
                                    (caddr
                                     (caddr
                                      (find-projection
                                       (cons fn (typed-term-list->term-lst tta))
                                       concl))))
                                   (typed-term->term (car ntta))
                                   (typed-term->term (cadr ntta)))
                                  concl
                                  (type-options->supertype options)))
                                (list (car ntta) (cadr ntta))
                                options)))))))
)

(encapsulate ()
  (local (in-theory (disable pseudo-termp assoc-equal
                             consp-of-pseudo-lambdap
                             pseudo-lambdap-of-fn-call-of-pseudo-termp
                             symbol-listp)))

  (local
   (defthm append-of-pseudo-term-listp
     (implies (and (pseudo-term-listp x)
                   (pseudo-term-listp y))
              (pseudo-term-listp (append x y)))))

  (local
   (defthm append-of-symbol-listp
     (implies (and (symbol-listp x)
                   (symbol-listp y))
              (symbol-listp (append x y)))))

  (local
   (defthm pseudo-term-alist-of-pairlis$
     (implies (and (pseudo-term-listp x)
                   (symbol-listp y))
              (pseudo-term-alistp (pairlis$ x y)))))

  (define generate-fncall-proj ((fn symbolp)
                                (actuals-tterm typed-term-list-p)
                                (new-actuals-tterm typed-term-list-p)
                                (actuals-proj pseudo-termp)
                                (options type-options-p)
                                state)
    :returns (mv (new-tt (good-typed-term-p new-tt options)
                         :hints (("Goal"
                                  :in-theory (enable good-typed-quote-p))))
                 (new-proj pseudo-termp))
    :guard (and (not (equal fn 'quote))
                (not (equal fn 'if))
                (good-typed-term-list-p actuals-tterm options)
                (good-typed-term-list-p new-actuals-tterm options))
    :verify-guards nil
    (b* (((unless (mbt (and (symbolp fn)
                            (not (equal fn 'quote))
                            (not (equal fn 'if))
                            (typed-term-list-p actuals-tterm)
                            (good-typed-term-list-p actuals-tterm options)
                            (typed-term-list-p new-actuals-tterm)
                            (good-typed-term-list-p new-actuals-tterm options)
                            (pseudo-termp actuals-proj)
                            (type-options-p options))))
          (mv (make-typed-term) nil))
         (att.term-lst (typed-term-list->term-lst actuals-tterm))
         (natt.term-lst (typed-term-list->term-lst new-actuals-tterm))
         ((type-options to) options)
         (exist? (assoc-equal fn to.aa-map))
         ((unless exist?)
          (prog2$ (er hard? 'term-projection=>generate-fncall-proj
                      "There isn't an alist-array-map item for function ~p0.~%" fn)
                  (mv (make-typed-term) nil)))
         ((equiv eq) (cdr exist?))
         (equiv-thm (acl2::meta-extract-formula-w eq.thm (w state)))
         ((unless (pseudo-termp equiv-thm))
          (prog2$ (er hard? 'term-projection=>generate-fncall-proj
                      "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
                      eq.thm equiv-thm)
                  (mv (make-typed-term) nil)))
         (fn-formals (strip-cars eq.formal-map))
         (fn-equiv-formals (strip-cdrs eq.formal-map))
         (both-actuals (append att.term-lst natt.term-lst))
         (both-formals (append fn-formals fn-equiv-formals))
         (substed-thm
          (term-substitution equiv-thm (pairlis$ both-actuals both-formals) t))
         ((mv ok new-tt new-proj)
          (case-match substed-thm
            (('implies hypo concl)
             (b* (((mv new-tt new-proj)
                   (generate-fncall-proj-cases fn actuals-tterm
                                               new-actuals-tterm
                                               actuals-proj hypo
                                               concl to state)))
               (mv t new-tt new-proj)))
            (& (mv nil (make-typed-term) nil))))
         ((unless ok)
          (prog2$ (er hard? 'term-projection=>generate-fncall-proj
                      "Equivalence theorem is malformed: ~q0" substed-thm)
                  (mv (make-typed-term) nil))))
      (mv new-tt new-proj)))
  )

(verify-guards generate-fncall-proj)

(encapsulate ()
  (local (in-theory (disable symbol-listp
                             acl2::pseudo-termp-opener
                             pseudo-term-listp-of-symbol-listp
                             acl2::symbol-listp-when-not-consp
                             consp-of-is-conjunct?)))

  (define generate-if-proj ((term pseudo-termp)
                            (cond-tterm typed-term-p)
                            (then pseudo-termp)
                            (then-tterm typed-term-p)
                            (then-proj pseudo-termp)
                            (else pseudo-termp)
                            (else-tterm typed-term-p)
                            (else-proj pseudo-termp)
                            state)
    :returns (mv (new-t pseudo-termp)
                 (new-proj pseudo-termp))
    (b* ((term (pseudo-term-fix term))
         ((typed-term ctt) (typed-term-fix cond-tterm))
         (then (pseudo-term-fix then))
         ((typed-term ttt) (typed-term-fix then-tterm))
         (then-proj (pseudo-term-fix then-proj))
         (else (pseudo-term-fix else))
         ((typed-term ett) (typed-term-fix else-tterm))
         (else-proj (pseudo-term-fix else-proj))
         (new-term `(if ,ctt.term ,ttt.term ,ett.term)))
      (cond ((and (path-test then-proj `(alist-array-equiv ,then ,ttt.term) state)
                  (path-test else-proj `(alist-array-equiv ,else ,ett.term) state))
             (mv new-term `(alist-array-equiv ,term ,new-term)))
            (t (mv (er hard? 'term-projection=>generate-if-proj
                       "Inconsistent if projections.~%then: ~p0~% ~
                      else: ~p1~%" then-proj else-proj)
                   nil)))))
  )

(define generate-lambda-proj ((term pseudo-termp)
                              (new-formals symbol-listp)
                              (actuals-tterm typed-term-list-p)
                              (body pseudo-termp)
                              (body-tterm typed-term-p)
                              (body-proj pseudo-termp)
                              state)
  :returns (mv (new-term pseudo-termp)
               (new-proj pseudo-termp))
  :guard (equal (len new-formals)
                (len (typed-term-list->term-lst actuals-tterm)))
  (b* ((term (pseudo-term-fix term))
       (new-formals (symbol-list-fix new-formals))
       (att.term-lst (typed-term-list->term-lst actuals-tterm))
       ((unless (mbt (equal (len new-formals) (len att.term-lst))))
        (mv nil nil))
       (body (pseudo-term-fix body))
       ((typed-term btt) (typed-term-fix body-tterm))
       (body-proj (pseudo-term-fix body-proj))
       (new-term `((lambda ,new-formals ,btt.term) ,@att.term-lst)))
    (cond ((path-test body-proj `(alist-array-equiv ,body ,btt.term) state)
           (mv new-term `(alist-array-equiv ,term ,new-term)))
          (t (mv (er hard? 'term-projection=>lambda-projection
                     "Inconsistent lambda projections.~%body projection: ~p0~%"
                     body-proj)
                 nil)))))

;; For a variable, if its judgement says it's an alist, the projection should
;; contain:
;;   (alist-array-equiv the-var new-var)
;; If so, generate new term using new-var, and new judgement by substituting in
;; the new term.
(define variable-projection ((tterm typed-term-p)
                             (path-cond pseudo-termp)
                             (projection pseudo-termp)
                             (names symbol-listp)
                             (options type-options-p))
  :returns (mv (new-tt (good-typed-term-p new-tt options)
                       :hints (("Goal"
                                :in-theory (enable good-typed-quote-p
                                                   good-typed-variable-p))))
               (new-proj pseudo-termp)
               (new-names symbol-listp))
  :guard (and (good-typed-term-p tterm options)
              (equal (typed-term->kind tterm) 'variablep))
  :guard-hints (("Goal" :in-theory (enable typed-term->kind)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (pseudo-termp path-cond)
                          (pseudo-termp projection)
                          (symbol-listp names)
                          (type-options-p options)
                          (good-typed-term-p tterm options)
                          (equal (typed-term->kind tterm) 'variablep))))
        (mv (make-typed-term)
            (pseudo-term-fix projection)
            (symbol-list-fix names)))
       ((typed-term tt) tterm)
       ((type-options to) options)
       (the-proj (find-projection tt.term projection))
       ((unless the-proj) (mv tt ''t names))
       ((mv err new-term)
        (case-match the-proj
          (('alist-array-equiv !tt.term new-term) (mv nil new-term))
          (& (mv t nil))))
       ((if err) (mv (make-typed-term) ''t names))
       (judge (look-up-path-cond new-term path-cond to.supertype))
       (new-tt (make-typed-term :term new-term
                                :path-cond path-cond
                                :judgements judge))
       ((unless (equal (typed-term->kind new-tt) 'variablep))
        (prog2$ (er hard? 'term-projection=>variable-projection
                    "Projecting a variable into a non-variable: ~p0 and ~p1~%"
                    tt.term new-term)
                (mv (make-typed-term) ''t names))))
    (mv new-tt the-proj names)))

;; Defining it so that the returns theorem for the below defines is easy
(define quote-projection ((tterm typed-term-p)
                          (path-cond pseudo-termp)
                          (names symbol-listp)
                          (options type-options-p))
  :returns (mv (new-tt (good-typed-term-p new-tt options)
                       :hints (("Goal"
                                :in-theory (enable good-typed-quote-p))))
               (new-proj pseudo-termp)
               (new-names symbol-listp))
  :guard (and (good-typed-term-p tterm options)
              (equal (typed-term->kind tterm) 'quotep))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (pseudo-termp path-cond)
                          (good-typed-term-p tterm options)
                          (equal (typed-term->kind tterm) 'quotep)
                          (symbol-listp names))))
        (mv (make-typed-term) nil nil))
       ((typed-term tt) tterm))
    (mv (make-typed-term :term tt.term
                         :path-cond path-cond
                         :judgements tt.judgements)
        `(alist-array-equiv ,tt.term ,tt.term) names)))

(local (in-theory (disable (:executable-counterpart typed-term))))

(local
 (defthm pseudo-termp-of-lambda
   (implies (and (symbol-listp formals)
                 (pseudo-termp body-judgements)
                 (pseudo-term-listp actuals)
                 (equal (len formals) (len actuals)))
            (pseudo-termp `((lambda ,formals
                              ,body-judgements)
                            ,@actuals))))
 )

(defines term-projection
  :well-founded-relation l<
  :verify-guards nil
  :returns-hints (("Goal"
                   :in-theory (disable consp-of-is-conjunct?
                                       pseudo-term-listp-of-symbol-listp
                                       acl2::car-of-append
                                       pseudo-termp symbol-listp
                                       acl2::pseudo-termp-opener
                                       binary-append pairlis$
                                       lambda-of-pseudo-lambdap
                                       consp-of-pseudo-lambdap
                                       acl2::symbol-listp-when-not-consp)))

  (define lambda-projection ((tterm typed-term-p)
                             (path-cond pseudo-termp)
                             (projection pseudo-termp)
                             (names symbol-listp)
                             (options type-options-p)
                             state)
    :returns (mv (new-tt (good-typed-term-p new-tt options))
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'lambdap))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (type-options-p options)
                            (symbol-listp names)
                            (pseudo-termp projection)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'lambdap))))
          (mv (make-typed-term)
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((typed-term tt) tterm)
         (formals (lambda-formals (car tt.term)))
         (tta (typed-term-lambda->actuals tterm options))
         (tta.term-lst (typed-term-list->term-lst tta))
         ;; TODO: is it possible to change the code to make this provable?
         ((unless (equal (len (cdr tt.term)) (len tta)))
          (prog2$ (er hard? 'term-projection=>lambda-projection
                      "Length of formals and actuals should be the same for ~
                       pseudo-lambda: ~p0 and ~p1.~%" formals tta.term-lst)
                  (mv (make-typed-term)
                      nil nil)))
         ((typed-term ttb) (typed-term-lambda->body tterm options))
         ((typed-term ttt) (typed-term->top tt options))
         ((mv ptta proja namesa)
          (term-list-projection tta path-cond projection names options state))
         (ptta.term-lst (typed-term-list->term-lst ptta))
         (ptta.judgements (typed-term-list->judgements ptta))
         (new-formals (new-fresh-vars (len formals) (append formals namesa)))
         (namesf (append new-formals namesa))
         (both-actuals (append tta.term-lst ptta.term-lst))
         (both-formals (append formals new-formals))
         (shadowed-path-cond (shadow-path-cond new-formals path-cond))
         (substed-actuals-judgements
          (term-substitution ptta.judgements
                             (pairlis$ ptta.term-lst new-formals) t))
         (shadowed-proj (shadow-path-cond new-formals projection))
         (substed-proja
          (term-substitution proja (pairlis$ both-actuals both-formals) t))
         ((mv pttb projb namesb)
          (term-projection ttb
                           `(if ,shadowed-path-cond
                                ,substed-actuals-judgements 'nil)
                           `(if ,shadowed-proj ,substed-proja 'nil)
                           namesf options state))
         ((typed-term pttb) pttb)
         ((unless (mbt (equal (len new-formals) (len ptta))))
          (mv (make-typed-term) nil nil))
         ((mv new-term new-proj)
          (generate-lambda-proj tt.term new-formals ptta ttb.term pttb
                                projb state))
         (new-judge `((lambda ,new-formals
                        ,pttb.judgements)
                      ,@ptta.term-lst))
         (new-top (make-typed-term :term new-term
                                   :path-cond path-cond
                                   :judgements new-judge)))
      (mv (make-typed-lambda new-top pttb ptta options) new-proj namesb)))

  (define if-projection ((tterm typed-term-p)
                         (path-cond pseudo-termp)
                         (projection pseudo-termp)
                         (names symbol-listp)
                         (options type-options-p)
                         state)
    :returns (mv (new-tt (good-typed-term-p new-tt options))
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'ifp))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (type-options-p options)
                            (symbol-listp names)
                            (pseudo-termp projection)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'ifp))))
          (mv (make-typed-term)
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((typed-term tt) tterm)
         ((typed-term ttc) (typed-term-if->cond tt options))
         ((typed-term ttt) (typed-term-if->then tt options))
         ((typed-term tte) (typed-term-if->else tt options))
         ((typed-term tttop) (typed-term->top tt options))
         ((mv pttc projc namesc)
          (term-projection ttc path-cond projection names options state))
         ((mv pttt projt namest)
          (term-projection ttt
                           `(if ,(simple-transformer ttc.term)
                                ,path-cond 'nil)
                           `(if ,projc ,projection 'nil)
                           namesc options state))
         ((typed-term pttt) pttt)
         ((mv ptte proje namese)
          (term-projection tte
                           `(if ,(simple-transformer `(not ,ttc.term))
                                ,path-cond 'nil)
                           projection namest options state))
         ((typed-term ptte) ptte)
         ((mv new-term new-proj)
          (generate-if-proj tt.term pttc ttt.term pttt projt tte.term
                            ptte proje state))
         (new-judge (intersect-judgements pttt.judgements ptte.judgements state))
         (new-top (make-typed-term :term new-term
                                   :path-cond path-cond
                                   :judgements new-judge)))
      (mv (make-typed-if new-top pttc pttt ptte options)
          new-proj namese)))

  (define fncall-projection ((tterm typed-term-p)
                             (path-cond pseudo-termp)
                             (projection pseudo-termp)
                             (names symbol-listp)
                             (options type-options-p)
                             state)
    :returns (mv (new-tt (good-typed-term-p new-tt options))
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'fncallp))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (pseudo-termp projection)
                            (symbol-listp names)
                            (type-options-p options)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'fncallp))))
          (mv (make-typed-term)
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((type-options to) options)
         ((typed-term tt) tterm)
         (tta (typed-term-fncall->actuals tterm to))
         ((typed-term ttt) (typed-term->top tterm to))
         ((cons fn actuals) tt.term)
         ((mv ptta proja namesa)
          (term-list-projection tta path-cond projection names options state))
         ((if (is-alist? fn options))
          (b* (((unless (and (equal (len actuals) 1)
                             (symbolp (car actuals))))
                (prog2$
                 (er hard? 'term-projection=>fncall-projection
                     "We found a alist type recognizer, but its argument is not ~
                     a single variable: ~q0" tt.term)
                 (mv tt projection names)))
               (fresh-var (new-fresh-var namesa))
               (new-var-proj (new-projection tt.term fresh-var to state))
               (new-names (cons fresh-var namesa))
               ((mv new-tt new-proj)
                (generate-fncall-proj fn tta ptta new-var-proj to state)))
            ;; adding array-p info into projection
            (mv new-tt new-proj new-names)))
         ((mv new-tt new-proj)
          (generate-fncall-proj fn tta ptta proja to state)))
      (mv new-tt new-proj namesa)))

  (define term-projection ((tterm typed-term-p)
                           (path-cond pseudo-termp)
                           (projection pseudo-termp)
                           (names symbol-listp)
                           (options type-options-p)
                           state)
    :guard (good-typed-term-p tterm options)
    :returns (mv (new-tt (good-typed-term-p new-tt options))
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :measure (list (acl2-count (typed-term->term tterm)) 1)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (pseudo-termp projection)
                            (symbol-listp names)
                            (type-options-p options)
                            (good-typed-term-p tterm options))))
          (mv (make-typed-term) nil nil))
         ((if (equal (typed-term->kind tterm) 'variablep))
          (variable-projection tterm path-cond projection names options))
         ((if (equal (typed-term->kind tterm) 'quotep))
          (quote-projection tterm path-cond names options))
         ((if (equal (typed-term->kind tterm) 'lambdap))
          (lambda-projection tterm path-cond projection names options state))
         ((if (equal (typed-term->kind tterm) 'ifp))
          (if-projection tterm path-cond projection names options state)))
      (fncall-projection tterm path-cond projection names options state)))

  (define term-list-projection ((tterm-lst typed-term-list-p)
                                (path-cond pseudo-termp)
                                (projection pseudo-termp)
                                (names symbol-listp)
                                (options type-options-p)
                                state)
    :guard (good-typed-term-list-p tterm-lst options)
    :returns (mv (new-ttl (good-typed-term-list-p new-ttl options))
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :measure (list (acl2-count (typed-term-list->term-lst tterm-lst))
                   1)
    (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                            (pseudo-termp path-cond)
                            (pseudo-termp projection)
                            (symbol-listp names)
                            (type-options-p options)
                            (good-typed-term-list-p tterm-lst options))))
          (mv nil
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((unless (consp tterm-lst))
          (mv nil ''t names))
         ((mv tt-car proj-car names-car)
          (term-projection (car tterm-lst) path-cond projection names options
                           state))
         ((mv ttl-cdr proj-cdr names-cdr)
          (term-list-projection (cdr tterm-lst) path-cond projection names-car
                                options state))
         ((unless (equal (typed-term->path-cond tt-car)
                         (typed-term-list->path-cond ttl-cdr)))
          (mv tterm-lst projection names)))
      (mv (cons tt-car ttl-cdr)
          `(if ,proj-car ,proj-cdr 'nil)
          names-cdr)))
  ///
  (defthm typed-term-of-lambda-projection
    (typed-term-p
     (mv-nth 0 (lambda-projection tterm path-cond projection
                                  names options state)))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (mv-nth 0 (lambda-projection tterm path-cond
                                                            projection
                                                            names options
                                                            state)))
                              (options options))))))
  (defthm typed-term-of-fncall-projection
    (typed-term-p
     (mv-nth 0 (fncall-projection tterm path-cond projection
                                  names options state)))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (mv-nth 0 (fncall-projection tterm path-cond
                                                            projection
                                                            names options
                                                            state)))
                              (options options))))))
  (defthm typed-term-of-if-projection
    (typed-term-p
     (mv-nth 0 (if-projection tterm path-cond projection names options state)))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (mv-nth 0 (if-projection tterm path-cond
                                                        projection names
                                                        options state)))
                              (options options))))))
  (defthm typed-term-of-term-projection
    (typed-term-p
     (mv-nth 0 (term-projection tterm path-cond projection names
                                options state)))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (mv-nth 0 (term-projection tterm path-cond
                                                          projection names
                                                          options state)))
                              (options options))))))
  (defthm typed-term-list-of-term-list-projection
    (typed-term-list-p
     (mv-nth 0 (term-list-projection tterm path-cond projection
                                     names options state)))
    :hints (("Goal"
             :in-theory (disable good-typed-term-list-implies-typed-term-list)
             :use ((:instance good-typed-term-list-implies-typed-term-list
                              (tterm-lst
                               (mv-nth 0 (term-list-projection tterm path-cond
                                                               projection
                                                               names options
                                                               state)))
                              (options options))))))

  (defthm term-list-projection-maintains-length-nil
    (implies (and (pseudo-termp path-cond)
                  (pseudo-termp projection)
                  (symbol-listp names)
                  (type-options-p options))
             (equal (len
                     (mv-nth 0
                             (term-list-projection nil path-cond projection
                                                   names options state)))
                    0))
    :hints (("Goal"
             :in-theory (e/d ()
                             (pseudo-termp symbol-listp)))))
  )

(define cdr-induct-term-list-projection ((tterm-lst)
                                         (path-cond)
                                         (projection)
                                         (names)
                                         (options)
                                         state)
  :irrelevant-formals-ok t
  :verify-guards nil
  (b* (((if (atom tterm-lst)) nil)
       ((mv & & new-names) (term-projection (car tterm-lst)
                                            path-cond
                                            projection names options state)))
    (cdr-induct-term-list-projection
     (cdr tterm-lst) path-cond projection new-names options state)))

(defthm term-list-projection-maintains-length
  (implies (and (typed-term-list-p tterm-lst)
                (pseudo-termp path-cond)
                (pseudo-termp projection)
                (symbol-listp names)
                (type-options-p options)
                (good-typed-term-list-p tterm-lst options))
           (equal (len
                   (mv-nth 0
                           (term-list-projection tterm-lst path-cond projection
                                                 names options state)))
                  (len tterm-lst)))
  :hints (("Goal"
           :in-theory (e/d (term-list-projection
                            cdr-induct-term-list-projection)
                           (pseudo-termp symbol-listp))
           :induct (cdr-induct-term-list-projection tterm-lst path-cond
                                                    projection names options
                                                    state))))

(verify-guards term-projection
  :hints (("Goal"
           :in-theory (disable pseudo-termp symbol-listp))))
