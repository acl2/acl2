;; Copyright (C) 2019, University of British Columbia
;; Written by Yan Peng (Dec 12th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)

(include-book "evaluator")
(include-book "typed-term")
(include-book "judgement-fns")
(include-book "returns-judgement")

(set-state-ok t)

(local (in-theory (disable (:executable-counterpart typed-term)
                           (:executable-counterpart typed-term-list)
                           symbol-listp
                           symbol-list-listp
                           pseudo-lambdap-of-fn-call-of-pseudo-termp
                           symbol-listp-of-car-when-symbol-list-listp)))

(define rectify ((fn symbolp)
                 (actuals pseudo-term-listp)
                 (actual-judges pseudo-termp)
                 (return returns-p)
                 (options type-options-p)
                 state)
  :returns (new-fn symbolp)
  :guard (not (equal fn 'quote))
  :ignore-ok t
  (b* (((unless (mbt (and (symbolp fn)
                          (pseudo-term-listp actuals)
                          (pseudo-termp actual-judges)
                          (returns-p return)
                          (type-options-p options))))
        nil)
       (replace-thm (returns->replace-thm return))
       (formals (returns->formals return))
       ((mv err new-fn)
        (case-match replace-thm
          (('equal (!fn . !formals) (new-fn . !formals))
           (if (or (not (symbolp new-fn)) (equal new-fn 'quote))
               (mv t nil)
             (mv nil new-fn)))
          (('equal (new-fn . !formals) (!fn . !formals))
           (if (or (not (symbolp new-fn)) (equal new-fn 'quote))
               (mv t nil)
             (mv nil new-fn)))
          (('implies hypo ('equal (!fn . !formals) (new-fn . !formals)))
           (b* (((if (equal new-fn 'quote)) (mv t nil))
                ((unless (symbolp new-fn)) (mv t nil))
                (substed
                 (term-substitution hypo (pairlis$ formals actuals) t))
                (yes? (path-test-list actual-judges substed state))
                ((if yes?) (mv nil new-fn)))
             (mv t nil)))
          (('implies hypo ('equal (new-fn . !formals) (!fn . !formals)))
           (b* (((if (equal new-fn 'quote)) (mv t nil))
                ((unless (symbolp new-fn)) (mv t nil))
                (substed
                 (term-substitution hypo (pairlis$ formals actuals) t))
                (yes? (path-test-list actual-judges substed state))
                ((if yes?) (mv nil new-fn)))
             (mv t nil)))
          (''t (mv nil nil))
          (& (mv t nil))))
       ((if err)
        (er hard? 'term-rectify=>rectify
            "The replace theorem is malformed: ~q0" replace-thm)))
    new-fn)
  ///
  (more-returns
   (new-fn (not (equal new-fn 'quote))
           :name not-quote-of-rectify)))

(define rectify-list ((fn symbolp)
                      (actuals pseudo-term-listp)
                      (actual-judges pseudo-termp)
                      (returns returns-list-p)
                      (options type-options-p)
                      state)
  :returns (new-fn symbolp)
  :measure (len returns)
  :guard (not (equal fn 'quote))
  (b* ((returns (returns-list-fix returns))
       ((unless (mbt (and (symbolp fn) (not (equal fn 'quote)))))
        nil)
       ((unless returns) fn)
       ((cons returns-hd returns-tl) returns)
       (rectify-hd (rectify fn actuals actual-judges returns-hd options state))
       ((if rectify-hd) rectify-hd))
    (rectify-list fn actuals actual-judges returns-tl options state))
  ///
  (more-returns
   (new-fn (not (equal new-fn 'quote))
           :name not-quote-of-rectify-list)))

(defines term-rectify
  :well-founded-relation l<
  :verify-guards nil
  :hints (("Goal"
           :in-theory (disable acl2-count implies-of-fncall-kind)))

  (define lambda-rectify ((tterm typed-term-p)
                          (options type-options-p)
                          state)
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'lambdap))
    :returns (new-tt (and (typed-term-p new-tt)
                          (good-typed-term-p new-tt options)))
    :measure (list (acl2-count (typed-term->term tterm))
                   0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'lambdap))))
          (make-typed-term))
         ((typed-term tt) tterm)
         (formals (lambda-formals (car tt.term)))
         (tta (typed-term-lambda->actuals tterm options))
         (ttb (typed-term-lambda->body tterm options))
         ((typed-term ttt) (typed-term->top tt options))
         ((typed-term-list rtta) (term-list-rectify tta options state))
         ((typed-term rttb) (term-rectify ttb options state))
         (new-term `((lambda ,formals ,rttb.term) ,@rtta.term-lst))
         (new-top-judge (term-substitution ttt.judgements `((,ttt.term . ,new-term)) t))
         (new-top (make-typed-term :term new-term
                                   :path-cond ttt.path-cond
                                   :judgements new-top-judge)))
      (make-typed-lambda new-top rttb rtta options)))

  (define if-rectify ((tterm typed-term-p)
                      (options type-options-p)
                      state)
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'ifp))
    :returns (new-tt (and (typed-term-p new-tt)
                          (good-typed-term-p new-tt options)))
    :measure (list (acl2-count (typed-term->term tterm))
                   0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'ifp))))
          (make-typed-term))
         ((typed-term tt) tterm)
         (ttc (typed-term-if->cond tt options))
         (ttt (typed-term-if->then tt options))
         (tte (typed-term-if->else tt options))
         ((typed-term tttop) (typed-term->top tt options))
         ((typed-term rttc) (term-rectify ttc options state))
         ((typed-term rttt) (term-rectify ttt options state))
         ((typed-term rtte) (term-rectify tte options state))
         (new-term `(if ,rttc.term ,rttt.term ,rtte.term))
         (new-top-judge (term-substitution tttop.judgements `((,tttop.term . ,new-term)) t))
         (new-top (make-typed-term :term new-term
                                   :path-cond tttop.path-cond
                                   :judgements new-top-judge)))
      (make-typed-if new-top rttc rttt rtte options)))

  (define fncall-rectify ((tterm typed-term-p)
                          (options type-options-p)
                          state)
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'fncallp))
    :returns (new-tt (and (typed-term-p new-tt)
                          (good-typed-term-p new-tt options)))
    :measure (list (acl2-count (typed-term->term tterm))
                   0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'fncallp))))
          (make-typed-term))
         ((type-options to) options)
         ((typed-term tt) tterm)
         ((typed-term-list tta) (typed-term-fncall->actuals tterm to))
         ((typed-term-list rtta) (term-list-rectify tta to state))
         ((typed-term ttt) (typed-term->top tterm to))
         ((cons fn &) tt.term)
         (conspair (assoc-equal fn to.functions))
         ((unless conspair)
          (prog2$
           (er hard? 'term-rectify=>fncall-rectify
               "There exists no function description for function ~p0. ~%" fn)
           tterm))
         (fn-description (cdr conspair))
         ((mv & returns)
          (returns-judgement fn rtta.term-lst rtta.term-lst rtta.judgements
                             rtta.judgements fn-description rtta.path-cond
                             to.supertype ''t nil state))
         (new-fn
          (rectify-list fn rtta.term-lst rtta.judgements returns options
                        state))
         (new-term `(,new-fn ,@rtta.term-lst))
         (new-judge
          (term-substitution ttt.judgements `((,ttt.term . ,new-term)) t))
         (new-top (make-typed-term :term new-term
                                   :path-cond ttt.path-cond
                                   :judgements new-judge)))
      (make-typed-fncall new-top rtta to)))

(define term-rectify ((tterm typed-term-p)
                      (options type-options-p)
                      state)
  :guard (good-typed-term-p tterm options)
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options)))
  :measure (list (acl2-count (typed-term->term tterm)) 1)
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((if (or (equal (typed-term->kind tterm) 'variablep)
                (equal (typed-term->kind tterm) 'quotep)))
        tterm)
       ((if (equal (typed-term->kind tterm) 'lambdap))
        (lambda-rectify tterm options state))
       ((if (equal (typed-term->kind tterm) 'ifp))
        (if-rectify tterm options state)))
    (fncall-rectify tterm options state)))

(define term-list-rectify ((tterm-lst typed-term-list-p)
                           (options type-options-p)
                           state)
  :guard (good-typed-term-list-p tterm-lst options)
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl options)))
  :measure (list (acl2-count (typed-term-list->term-lst tterm-lst)) 1)
  (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                          (type-options-p options)
                          (good-typed-term-list-p tterm-lst options))))
        (make-typed-term-list))
       ((unless (typed-term-list-consp tterm-lst)) tterm-lst)
       ((typed-term tt-car)
        (term-rectify
         (typed-term-list->car tterm-lst options)
         options state))
       ((typed-term-list tt-cdr)
        (term-list-rectify
         (typed-term-list->cdr tterm-lst options)
         options state))
       ((unless (mbt (equal tt-car.path-cond tt-cdr.path-cond)))
        tterm-lst))
    (typed-term-list->cons tt-car tt-cdr options)))
///
(defthm term-list-rectify-maintains-len-nil
  (implies (and (typed-term-list-p tterm-lst)
                (type-options-p options)
                (good-typed-term-list-p tterm-lst options)
                (not (typed-term-list-consp tterm-lst)))
           (equal (len (typed-term-list->term-lst
                        (term-list-rectify tterm-lst options state)))
                  (len (typed-term-list->term-lst tterm-lst))))
  :hints (("Goal"
           :in-theory (enable term-list-rectify)
           :expand (term-list-rectify tterm-lst options state))))

(defthm term-list-rectify-maintains-len
  (implies (and (typed-term-list-p tterm-lst)
                (type-options-p options)
                (good-typed-term-list-p tterm-lst options))
           (equal (len (typed-term-list->term-lst
                        (term-list-rectify tterm-lst options state)))
                  (len (typed-term-list->term-lst tterm-lst))))
  :hints (("Goal"
           :in-theory (e/d (term-list-rectify
                            (:induction typed-term-list->cdr-induct))
                           (term-rectify))
           :expand (term-list-rectify tterm-lst options state)
           :induct (typed-term-list->cdr-induct tterm-lst options))))
)

(defthm if-rectify-maintains-path-cond
  (implies (and (good-typed-term-p tterm options)
                (type-options-p options)
                (typed-term-p tterm)
                (equal (typed-term->kind tterm) 'ifp))
           (equal (typed-term->path-cond
                   (if-rectify tterm options state))
                  (typed-term->path-cond tterm)))
  :hints (("Goal"
           :expand (if-rectify tterm options state))))

(defthm lambda-rectify-maintains-path-cond
  (implies (and (good-typed-term-p tterm options)
                (type-options-p options)
                (typed-term-p tterm)
                (equal (typed-term->kind tterm) 'lambdap))
           (equal (typed-term->path-cond
                   (lambda-rectify tterm options state))
                  (typed-term->path-cond tterm)))
  :hints (("Goal"
           :expand (lambda-rectify tterm options state))))

(defthm fncall-rectify-maintains-path-cond
  (implies (and (good-typed-term-p tterm options)
                (type-options-p options)
                (typed-term-p tterm)
                (equal (typed-term->kind tterm) 'fncallp))
           (equal (typed-term->path-cond
                   (fncall-rectify tterm options state))
                  (typed-term->path-cond tterm)))
  :hints (("Goal"
           :expand (fncall-rectify tterm options state))))

(defthm term-rectify-maintains-path-cond
  (implies (and (good-typed-term-p tterm options)
                (type-options-p options)
                (typed-term-p tterm))
           (equal (typed-term->path-cond
                   (term-rectify tterm options state))
                  (typed-term->path-cond tterm)))
  :hints (("Goal"
           :expand (term-rectify tterm options state))))

(defthm term-list-rectify-maintains-path-cond
  (implies (and (good-typed-term-list-p tterm-lst options)
                (type-options-p options)
                (typed-term-list-p tterm-lst))
           (equal (typed-term-list->path-cond
                   (term-list-rectify tterm-lst options state))
                  (typed-term-list->path-cond tterm-lst)))
  :hints (("Goal"
           :expand (term-list-rectify tterm-lst options state))))

(verify-guards term-rectify)

(define term-rectify-fn ((cl pseudo-term-listp)
                         (options t)
                         state)
  :returns (subgoal-lst pseudo-term-list-listp)
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (type-options-p options))
        (list cl))
       ((mv ok goal judgements)
        (case-match cl
          ((('implies judgements goal))
           (mv t goal judgements))
          (& (mv nil nil nil))))
       ((unless ok)
        (er hard? 'term-rectify=>term-rectify-fn
            "Malformed clauses: ~q0" cl))
       (typed-term (make-typed-term :term goal :path-cond ''t
                                    :judgements judgements))
       ((unless (good-typed-term-p typed-term options))
        (er hard? 'term-rectify=>term-rectify-fn
            "Not a good-typed-term-p: ~q0" typed-term))
       (rectified-typed-term (term-rectify typed-term options state))
       ((typed-term tt) rectified-typed-term)
       (new-cl `((implies ,tt.judgements ,tt.term))))
    (list new-cl)))

(define term-rectify-cp ((cl pseudo-term-listp)
                         (hints t)
                         state)
  (b* ((new-clause (term-rectify-fn cl hints state)))
    (value new-clause)))

;; (skip-proofs
;;  (defthm correctness-of-term-rectify-cp
;;    (implies (and (ev-smtcp-meta-extract-global-facts)
;;                  (pseudo-term-listp cl)
;;                  (alistp a)
;;                  (ev-smtcp
;;                   (conjoin-clauses
;;                    (acl2::clauses-result
;;                     (term-rectify-cp cl hint state)))
;;                   a))
;;             (ev-smtcp (disjoin cl) a))
;;    :rule-classes :clause-processor)
;;  )

