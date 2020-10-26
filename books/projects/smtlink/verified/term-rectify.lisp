;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (Dec 12th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)

(include-book "hint-please")
(include-book "basics")
(include-book "evaluator")
(include-book "typed-term-fns")
(include-book "judgement-fns")
(include-book "returns-judgement")

(set-state-ok t)

(local (in-theory (disable (:executable-counterpart typed-term))))

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
               (mv t nil) (mv nil new-fn)))
          (('equal (new-fn . !formals) (!fn . !formals))
           (if (or (not (symbolp new-fn)) (equal new-fn 'quote))
               (mv t nil) (mv nil new-fn)))
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

(define find-nil-fn ((tterm typed-term-p)
                     (path-cond pseudo-termp)
                     (nil-alst symbol-symbol-alistp)
                     (options type-options-p)
                     state)
  :returns (new-tt (good-typed-term-p new-tt options))
  :guard (and (good-typed-term-p tterm options)
              (equal (typed-term->term tterm) ''nil))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (pseudo-termp path-cond)
                          (good-typed-term-p tterm options)
                          (equal (typed-term->term tterm) ''nil)
                          (symbol-symbol-alistp nil-alst)
                          (type-options-p options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((unless (consp nil-alst))
        (prog2$ (er hard? 'term-rectify=>find-nil-fn
                    "Don't know how to dispatch nil.~%")
                (make-typed-term)))
       ((cons (cons type nil-fn) nil-tl) nil-alst)
       ((if (or (equal nil-fn 'quote)
                (equal nil-fn 'if)))
        (prog2$ (er hard? 'term-rectify=>find-nil-fn
                    "nil-fn is 'quote or 'if.~%")
                (make-typed-term)))
       (yes? (path-test tt.judgements `(,type 'nil) state))
       ((unless yes?) (find-nil-fn tterm path-cond nil-tl options state))
       ((unless (acl2::logicp nil-fn (w state)))
        (prog2$ (er hard? 'term-rectify=>find-nil-fn
                    "~p0 is a program-mode function: ~q0" nil-fn)
                (make-typed-term)))
       ((mv err val) (magic-ev-fncall nil-fn '() state t nil))
       ((if (or err val))
        (prog2$
         (er hard? 'term-rectify=>find-nil-fn
             "Cannot estabilish ~p0 is a nil function.~%"
             nil-fn)
         (make-typed-term)))
       (new-term `(,nil-fn))
       (substed-judge
        (term-substitution tt.judgements `((,tt.term . ,new-term)) t))
       (new-judge `(if ,substed-judge 't 'nil)))
    (make-typed-term
     :term new-term
     :path-cond path-cond
     :judgements new-judge))
  ///
  (more-returns
   (new-tt (typed-term-p new-tt)
           :name typed-term-of-find-nil-fn)))

;; Dispatching nil
(define quote-rectify ((tterm typed-term-p)
                       (path-cond pseudo-termp)
                       (options type-options-p)
                       state)
  :returns (new-tt (good-typed-term-p new-tt options)
                   :hints (("Goal"
                            :in-theory (enable good-typed-quote-p))))
  :guard (and (good-typed-term-p tterm options)
              (equal (typed-term->kind tterm) 'quotep))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (pseudo-termp path-cond)
                          (good-typed-term-p tterm options)
                          (equal (typed-term->kind tterm) 'quotep)
                          (type-options-p options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((type-options to) options)
       ((unless (equal tt.term ''nil))
        (change-typed-term tterm :path-cond path-cond)))
    (find-nil-fn tt path-cond to.nil-alst options state))
  ///
  (more-returns
   (new-tt (typed-term-p new-tt)
           :name typed-term-of-quote-rectify)))

(defines term-rectify
  :well-founded-relation l<
  :verify-guards nil
  :hints (("Goal"
           :in-theory (e/d ()
                           (acl2-count implies-of-fncall-kind))))
  :returns-hints (("Goal"
                   :in-theory (enable good-typed-variable-p)))

  (define lambda-rectify ((tterm typed-term-p)
                          (path-cond pseudo-termp)
                          (options type-options-p)
                          state)
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'lambdap))
    :returns (new-tt (good-typed-term-p new-tt options))
    :measure (list (acl2-count (typed-term->term tterm))
                   0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (type-options-p options)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'lambdap))))
          (make-typed-term))
         ((typed-term tt) tterm)
         (formals (lambda-formals (car tt.term)))
         (tta (typed-term-lambda->actuals tterm options))
         (ttb (typed-term-lambda->body tterm options))
         ((typed-term ttt) (typed-term->top tt options))
         (rtta (term-list-rectify tta path-cond options state))
         (rtta.term-lst (typed-term-list->term-lst rtta))
         (rtta.judgements (typed-term-list->judgements rtta))
         (shadowed-path-cond (shadow-path-cond formals path-cond))
         (substed-actuals-judgements
          (term-substitution rtta.judgements
                             (pairlis$ rtta.term-lst formals) t))
         ((typed-term rttb)
          (term-rectify ttb `(if ,shadowed-path-cond
                                 ,substed-actuals-judgements
                               'nil)
                        options state))
         (- (cw "rttb: ~q0" rttb))
         ;; TODO: is it possible to change the code to make this provable?
         ((unless (equal (len formals) (len rtta.term-lst)))
          (prog2$ (er hard? 'term-rectify=>lambda-rectify
                      "Length of formals and actuals should be the same for ~
                       pseudo-lambda: ~p0 and ~p1.~%" formals rtta.term-lst)
                  (make-typed-term)))
         (new-term `((lambda ,formals ,rttb.term) ,@rtta.term-lst))
         (new-top-judge
          (term-substitution ttt.judgements `((,ttt.term . ,new-term)) t))
         (new-top (make-typed-term :term new-term
                                   :path-cond path-cond
                                   :judgements new-top-judge)))
      (make-typed-lambda new-top rttb rtta options)))

  (define if-rectify ((tterm typed-term-p)
                      (path-cond pseudo-termp)
                      (options type-options-p)
                      state)
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'ifp))
    :returns (new-tt (good-typed-term-p new-tt options))
    :measure (list (acl2-count (typed-term->term tterm))
                   0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (type-options-p options)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'ifp))))
          (make-typed-term))
         ((typed-term tt) tterm)
         (ttc (typed-term-if->cond tt options))
         (ttt (typed-term-if->then tt options))
         (tte (typed-term-if->else tt options))
         ((typed-term tttop) (typed-term->top tt options))
         ((typed-term rttc) (term-rectify ttc path-cond options state))
         ((typed-term rttt)
          (term-rectify ttt
                        `(if ,(simple-transformer rttc.term) ,path-cond 'nil)
                        options state))
         ((typed-term rtte)
          (term-rectify tte
                        `(if ,(simple-transformer `(not ,rttc.term)) ,path-cond
                           'nil)
                        options state))
         (new-term `(if ,rttc.term ,rttt.term ,rtte.term))
         (new-top-judge
          (term-substitution tttop.judgements `((,tttop.term . ,new-term)) t))
         (new-top (make-typed-term :term new-term
                                   :path-cond path-cond
                                   :judgements new-top-judge)))
      (make-typed-if new-top rttc rttt rtte options)))

  (define fncall-rectify ((tterm typed-term-p)
                          (path-cond pseudo-termp)
                          (options type-options-p)
                          state)
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'fncallp))
    :returns (new-tt (good-typed-term-p new-tt options))
    :measure (list (acl2-count (typed-term->term tterm))
                   0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (type-options-p options)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'fncallp))))
          (make-typed-term))
         ((type-options to) options)
         ((typed-term tt) tterm)
         (tta (typed-term-fncall->actuals tterm to))
         (rtta (term-list-rectify tta path-cond to state))
         (rtta.term-lst (typed-term-list->term-lst rtta))
         (rtta.path-cond (typed-term-list->path-cond rtta))
         (rtta.judgements (typed-term-list->judgements rtta))
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
                                   :path-cond path-cond
                                   :judgements new-judge))
         ;; in order to satisfy the guards of make-typed-fncall
         ((unless (and (not (equal new-fn 'if))
                       (equal path-cond rtta.path-cond)))
          tt))
      (make-typed-fncall new-top rtta to)))

  (define term-rectify ((tterm typed-term-p)
                        (path-cond pseudo-termp)
                        (options type-options-p)
                        state)
  :guard (good-typed-term-p tterm options)
  :returns (new-tt (good-typed-term-p new-tt options))
  :measure (list (acl2-count (typed-term->term tterm)) 1)
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (pseudo-termp path-cond)
                          (type-options-p options)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((if (equal (typed-term->kind tterm) 'variablep))
        (change-typed-term tterm :path-cond path-cond))
       ((if (equal (typed-term->kind tterm) 'quotep))
        (quote-rectify tterm path-cond options state))
       ((if (equal (typed-term->kind tterm) 'lambdap))
        (lambda-rectify tterm path-cond options state))
       ((if (equal (typed-term->kind tterm) 'ifp))
        (if-rectify tterm path-cond options state)))
    (fncall-rectify tterm path-cond options state)))

(define term-list-rectify ((tterm-lst typed-term-list-p)
                           (path-cond pseudo-termp)
                           (options type-options-p)
                           state)
  :guard (good-typed-term-list-p tterm-lst options)
  :returns (new-ttl (good-typed-term-list-p new-ttl options))
  :measure (list (acl2-count (typed-term-list->term-lst tterm-lst)) 1)
  (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                          (pseudo-termp path-cond)
                          (type-options-p options)
                          (good-typed-term-list-p tterm-lst options))))
        nil)
       ((unless (consp tterm-lst)) nil)
       ((cons tterm-hd tterm-tl) tterm-lst)
       (tt-car (term-rectify tterm-hd path-cond options state))
       (tt-cdr (term-list-rectify tterm-tl path-cond options state))
       ((unless (equal (typed-term->path-cond tt-car)
                       (typed-term-list->path-cond tt-cdr)))
        tterm-lst))
    (cons tt-car tt-cdr)))
///
(defthm typed-term-of-fncall-rectify
  (typed-term-p (fncall-rectify tterm path-cond options state))
  :hints (("Goal"
           :in-theory (disable good-typed-term-implies-typed-term)
           :use ((:instance good-typed-term-implies-typed-term
                            (tterm
                             (fncall-rectify tterm path-cond options state))
                            (options options))))))
(defthm typed-term-of-lambda-rectify
  (typed-term-p (lambda-rectify tterm path-cond options state))
  :hints (("Goal"
           :in-theory (disable good-typed-term-implies-typed-term)
           :use ((:instance good-typed-term-implies-typed-term
                            (tterm
                             (lambda-rectify tterm path-cond options state))
                            (options options))))))
(defthm typed-term-of-if-rectify
  (typed-term-p (if-rectify tterm path-cond options state))
  :hints (("Goal"
           :in-theory (disable good-typed-term-implies-typed-term)
           :use ((:instance good-typed-term-implies-typed-term
                            (tterm
                             (if-rectify tterm path-cond options state))
                            (options options))))))
(defthm typed-term-of-term-rectify
  (typed-term-p (term-rectify tterm path-cond options state))
  :hints (("Goal"
           :in-theory (disable good-typed-term-implies-typed-term)
           :use ((:instance good-typed-term-implies-typed-term
                            (tterm
                             (term-rectify tterm path-cond options state))
                            (options options))))))
(defthm typed-term-list-of-term-list-rectify
  (typed-term-list-p (term-list-rectify tterm-lst path-cond options state))
  :hints (("Goal"
           :in-theory (disable good-typed-term-list-implies-typed-term-list)
           :use ((:instance good-typed-term-list-implies-typed-term-list
                            (tterm-lst
                             (term-list-rectify tterm-lst path-cond options state))
                            (options options))))))

;; (defthm term-list-rectify-maintains-len-nil
;;   (implies (and (typed-term-list-p tterm-lst)
;;                 (type-options-p options)
;;                 (pseudo-termp path-cond)
;;                 (good-typed-term-list-p tterm-lst options)
;;                 (not (consp tterm-lst)))
;;            (equal (len (typed-term-list->term-lst
;;                         (term-list-rectify tterm-lst path-cond options state)))
;;                   (len (typed-term-list->term-lst tterm-lst))))
;;   :hints (("Goal"
;;            :in-theory (enable term-list-rectify)
;;            :expand (term-list-rectify tterm-lst path-cond options state))))

;; (defthm term-list-rectify-maintains-len
;;   (implies (and (typed-term-list-p tterm-lst)
;;                 (type-options-p options)
;;                 (pseudo-termp path-cond)
;;                 (good-typed-term-list-p tterm-lst options))
;;            (equal (len (typed-term-list->term-lst
;;                         (term-list-rectify tterm-lst path-cond options state)))
;;                   (len (typed-term-list->term-lst tterm-lst))))
;;   :hints (("Goal"
;;            :in-theory (e/d (term-list-rectify typed-term-list->term-lst)
;;                            (term-rectify pseudo-termp))
;;            :expand (term-list-rectify tterm-lst path-cond options state))))
)

(verify-guards term-rectify
  :hints (("Goal"
           :in-theory (enable make-typed-fncall-guard))))

(define term-rectify-fn ((cl pseudo-term-listp)
                         (smtlink-hint t)
                         state)
  :returns (subgoal-lst pseudo-term-list-listp)
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint))
        (list cl))
       ((smtlink-hint h) smtlink-hint)
       (goal (disjoin cl))
       ((mv err judges original-goal)
        (case-match goal
          (('implies judges original-goal)
           (mv nil judges original-goal))
          (& (mv nil nil nil))))
       ((if err)
        (er hard? 'term-rectify=>term-rectify-fn
            "Theorem should be a implies from a judgement to a goal.~%"))
       (options (construct-type-options smtlink-hint))
       (tt (make-typed-term :term original-goal
                            :path-cond ''t
                            :judgements judges))
       ((unless (good-typed-term-p tt options))
        (er hard? 'term-rectify=>term-rectify-fn
            "Expected a good-typed-term-p.~%"))
       (rectified-tterm (term-rectify tt ''t options state))
       (new-cl (typed-term->term rectified-tterm))
       (next-cp (cdr (assoc-equal 'term-rectify *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',h state)))
       (hinted-goal `((hint-please ',the-hint) ,new-cl)))
    (list hinted-goal)))

(define term-rectify-cp ((cl pseudo-term-listp)
                          (hints t)
                          state)
  (b* ((decorated-clause (term-rectify-fn cl hints state)))
    (value decorated-clause)))

(local (in-theory (enable term-rectify-cp term-rectify-fn)))

(skip-proofs
(defthm correctness-of-term-rectify-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (term-rectify-cp cl hint state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :rule-classes :clause-processor)
)
