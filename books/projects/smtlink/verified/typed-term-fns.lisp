;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
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
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "../utils/pseudo-term")
(include-book "path-cond")
(include-book "term-substitution")
(include-book "typed-term")
(include-book "evaluator")

;; reduce not's in term
(define simple-transformer ((term pseudo-termp))
  :returns (new-term pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (new-term
        (case-match term
          (('not ('not term1)) term1)
          (& term))))
    new-term))

(defthm correctness-of-simple-transformer
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp term)
                (alistp a))
           (iff (ev-smtcp (simple-transformer term) a)
                (ev-smtcp term a)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable simple-transformer))))

;; ---------------------------------------------
;;       Recognizers

(local
 (defthm type-of-0-input-fn
   (implies (and (symbolp fn)
                 (not (equal fn 'quote)))
            (and (not (pseudo-lambdap `(,fn)))
                 (pseudo-termp `(,fn))))
   :hints (("Goal"
            :in-theory (enable pseudo-lambdap)))))

(define typed-term->kind ((tterm t))
  :returns (kind symbolp)
  (b* (((unless (typed-term-p tterm)) nil)
       ((typed-term tt) tterm)
       ((if (acl2::variablep tt.term)) 'variablep)
       ((if (acl2::quotep tt.term)) 'quotep)
       ((cons fn &) tt.term)
       ((if (pseudo-lambdap fn))
        ;;'lambdap
        (er hard? 'typed-term-fns=>typed-term->kind
            "Found lambda in term.~%"))
       ((if (equal fn 'if)) 'ifp))
    'fncallp)
  ///
  (more-returns
   (kind (member-equal kind '(variablep quotep ;; lambdap
                                        ifp fncallp nil))
         :name range-of-typed-term->kind)
   (kind (implies (and (typed-term-p tterm)
                       kind
                       (not (equal kind 'variablep))
                       (not (equal kind 'quotep))
                       ;; (not (equal kind 'lambdap))
                       (not (equal kind 'ifp)))
                  (equal kind 'fncallp))
         :name cases-of-typed-term->kind)
   (kind (implies (equal kind 'variablep)
                  (acl2::variablep (typed-term->term tterm)))
         :name implies-of-variable-kind)
   (kind (implies (equal kind 'quotep)
                  (acl2::quotep (typed-term->term tterm)))
         :name implies-of-quote-kind)
   ;; (kind (implies (equal kind 'lambdap)
   ;;                (and (consp (typed-term->term tterm))
   ;;                     (pseudo-lambdap (car (typed-term->term tterm)))))
   ;;       :name implies-of-lambda-kind)
   (kind (implies (equal kind 'ifp)
                  (and (consp (typed-term->term tterm))
                       (equal (car (typed-term->term tterm)) 'if)))
         :name implies-of-if-kind)
   (kind (implies (equal kind 'fncallp)
                  (and (consp (typed-term->term tterm))
                       (not (equal (car (typed-term->term tterm)) 'quote))
                       (symbolp (car (typed-term->term tterm)))
                       (pseudo-term-listp (cdr (typed-term->term tterm)))))
         :name implies-of-fncall-kind)
   (kind (implies (equal kind 'fncallp)
                  (and (not (equal (car (typed-term->term tterm)) 'quote))
                       (not (equal (car (typed-term->term tterm)) 'if))))
         :name fncall-is-not-if)
   (kind (implies (and (typed-term-p tterm)
                       (equal kind x))
                  (equal (typed-term->kind
                          (typed-term (typed-term->term tterm) a b))
                         x))
         :name kind-preserved)
   (kind (implies (and (typed-term-p tterm)
                       (not (equal kind x)))
                  (not (equal (typed-term->kind
                               (typed-term (typed-term->term tterm) a b))
                              x)))
         :name not-kind-preserved))
  (defthm good-typed-fncall-of-0-input-fn
    (implies (and (symbolp fn)
                  (not (equal fn 'quote))
                  (not (equal fn 'if))
                  (pseudo-termp path-cond)
                  (pseudo-termp judges))
             (equal (typed-term->kind
                     (typed-term `(,fn) path-cond `(if ,judges 't 'nil)))
                    'fncallp))))

(define good-typed-variable-p ((tterm t)
                               (options type-options-p))
  :returns (ok booleanp)
  :guard (equal (typed-term->kind tterm) 'variablep)
  (b* (((unless (typed-term-p tterm)) nil)
       ((unless (mbt (equal (typed-term->kind tterm) 'variablep))))
       (options (type-options-fix options))
       ((typed-term tt) tterm)
       ((type-options to) options))
    ;; (if (is-conjunct-list? tt.judgements tt.term to.supertype) t nil)
    t)
  ///
  (defthm kind-of-good-typed-variable
    (implies (good-typed-variable-p tterm options)
             (equal (typed-term->kind tterm) 'variablep))))

(defthm good-typed-variable-implies-typed-term
  (implies (good-typed-variable-p tterm options)
           (typed-term-p tterm))
  :hints (("Goal"
           :in-theory (enable good-typed-variable-p))))

#|
(good-typed-variable-p (typed-term 'x
                                   ''t
                                   '(if (if (booleanp (rational-integer-alistp x))
                                            't
                                          'nil)
                                        (if (if 't 't 'nil) 't 'nil)
                                      'nil)))
|#

(define good-typed-quote-p ((tterm t)
                            (options type-options-p))
  :returns (ok booleanp)
  :guard (equal (typed-term->kind tterm) 'quotep)
  (b* (((unless (typed-term-p tterm)) nil)
       ((unless (mbt (equal (typed-term->kind tterm) 'quotep))))
       (options (type-options-fix options))
       ((typed-term tt) tterm)
       ((type-options to) options))
    ;; (if (is-conjunct-list? tt.judgements tt.term to.supertype) t nil)
    t)
  ///
  (defthm kind-of-good-typed-quote
    (implies (good-typed-quote-p tterm options)
             (equal (typed-term->kind tterm) 'quotep))))

(defthm good-typed-quote-implies-typed-term
  (implies (good-typed-quote-p tterm options)
           (typed-term-p tterm))
  :hints (("Goal"
           :in-theory (enable good-typed-quote-p)))
  ;; :rule-classes :forward-chaining
  )

#|
(good-typed-quote-p (typed-term ''t
                                ''t
                                '(if (if (symbolp 't)
                                         (if (booleanp 't) 't 'nil)
                                       'nil)
                                     't
                                   'nil)))
|#

;; mrg: I added the test
;;   (make-typed-term-list-guard actuals tt.path-cond actuals-judge)
;; to good-typed-lambda-p and good-typed-fncall-p.
;; This probably creates a verification obligation for the code that
;; creates judgements for lambdas and function calls.
(defines good-typed-term
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil
  :hints (("Goal"
           :in-theory (e/d ()
                           (pseudo-termp
                            pseudo-term-listp
                            equal-fixed-and-x-of-pseudo-termp
                            symbol-listp
                            acl2::pseudo-termp-cadr-from-pseudo-term-listp))))

  ;; (define good-typed-lambda-p ((tterm t)
  ;;                              (options type-options-p))
  ;;   :returns (ok booleanp)
  ;;   :guard (equal (typed-term->kind tterm) 'lambdap)
  ;;   :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
  ;;                  0)
  ;;   :ignore-ok t
  ;;   (b* (((unless (typed-term-p tterm)) nil)
  ;;        (options (type-options-fix options))
  ;;        ((typed-term tt) tterm)
  ;;        ((type-options to) options)
  ;;        ((unless (mbt (equal (typed-term->kind tterm) 'lambdap)))
  ;;         nil)
  ;;        ((cons fn actuals) tt.term)
  ;;        (formals (lambda-formals fn))
  ;;        (body (lambda-body fn))
  ;;        ((unless (consp tt.judgements)) nil)
  ;;        (match?
  ;;         (case-match tt.judgements
  ;;           (('if return-judge
  ;;                ('if (('lambda !formals body-judge) . !actuals)
  ;;                    actuals-judge
  ;;                  ''nil)
  ;;              ''nil)
  ;;            (and ;; (is-conjunct-list? return-judge tt.term to.supertype)
  ;;             (make-typed-term-list-guard actuals tt.path-cond actuals-judge) ;; added by mrg
  ;;                 (good-typed-term-list-p
  ;;                  (make-typed-term-list actuals tt.path-cond actuals-judge)
  ;;                  to)
  ;;                 (b* ((shadowed-path-cond
  ;;                       (shadow-path-cond formals tt.path-cond))
  ;;                      (substed-actuals-judgements
  ;;                       (term-substitution actuals-judge
  ;;                                          (pairlis$ actuals formals)
  ;;                                          t)))
  ;;                   (good-typed-term-p
  ;;                    (make-typed-term :term body
  ;;                                     :path-cond `(if ,shadowed-path-cond
  ;;                                                     ,substed-actuals-judgements
  ;;                                                   'nil)
  ;;                                     :judgements body-judge)
  ;;                    to))))
  ;;           (& nil))))
  ;;     (if match? t nil)))

  (define good-typed-if-p ((tterm t)
                           (options type-options-p))
    :returns (ok booleanp)
    :guard (equal (typed-term->kind tterm) 'ifp)
    :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                   0)
    :ignore-ok t
    (b* (((unless (typed-term-p tterm)) nil)
         (options (type-options-fix options))
         ((typed-term tt) tterm)
         ((type-options to) options)
         ((unless (mbt (equal (typed-term->kind tterm) 'ifp)))
          nil)
         ((unless (equal (len (cdr tt.term)) 3))
          (er hard? 'typed-term=>good-typed-if-p
              "Malformed if term: ~q0" tt.term))
         ((list & cond then else) tt.term)
         ((unless (consp tt.judgements)) nil)
         (match?
          (case-match tt.judgements
            (('if judge-if-top
                 ('if judge-cond
                     ('if !cond judge-then judge-else)
                   ''nil)
               ''nil)
             (and ;; (is-conjunct-list? judge-if-top tt.term to.supertype)
                    (good-typed-term-p
                     (make-typed-term :term cond
                                      :path-cond tt.path-cond
                                      :judgements judge-cond)
                     to)
                    (good-typed-term-p
                     (make-typed-term :term then
                                      :path-cond
                                      `(if ,(simple-transformer cond)
                                           ,tt.path-cond 'nil)
                                      :judgements judge-then)
                     to)
                    (good-typed-term-p
                     (make-typed-term :term else
                                      :path-cond
                                      `(if ,(simple-transformer `(not ,cond))
                                           ,tt.path-cond 'nil)
                                      :judgements judge-else)
                     to)))
            (& nil))))
      (if match? t nil)))

  (define good-typed-fncall-p ((tterm t)
                               (options type-options-p))
    :returns (ok booleanp)
    :guard (equal (typed-term->kind tterm) 'fncallp)
    :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                   0)
    :ignore-ok t
    (b* (((unless (typed-term-p tterm)) nil)
         (options (type-options-fix options))
         ((typed-term tt) tterm)
         ((type-options to) options)
         ((unless (mbt (equal (typed-term->kind tterm) 'fncallp))) nil)
         ((cons & actuals) tt.term)
         ((unless (consp tt.judgements)) nil)
         (match?
          (case-match tt.judgements
            (('if return-judge actuals-judge ''nil)
             (and ;; (is-conjunct-list? return-judge tt.term to.supertype)
              (make-typed-term-list-guard actuals tt.path-cond actuals-judge) ;; added by mrg
              (good-typed-term-list-p
               (make-typed-term-list actuals tt.path-cond actuals-judge)
               options)))
            (& nil))))
      (if match? t nil)))

  (define good-typed-term-p ((tterm t)
                             (options type-options-p))
    :returns (ok booleanp)
    :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                   1)
    (b* (((unless (typed-term-p tterm)) nil)
         ((typed-term tt) tterm)
         ((if (null (typed-term->kind tt)))
          (er hard? 'typed-term-fns=>good-typed-term-p
              "Found lambda in the term.~%"))
         ((if (equal (typed-term->kind tt) 'variablep))
          (good-typed-variable-p tt options))
         ((if (equal (typed-term->kind tt) 'quotep))
          (good-typed-quote-p tt options))
         ((if (equal (typed-term->kind tt) 'ifp))
          (good-typed-if-p tt options)))
      (good-typed-fncall-p tt options)))

  (define good-typed-term-list-p ((tterm-lst typed-term-list-p)
                                  (options type-options-p))
    :returns (ok booleanp)
    :measure (list (acl2-count
                    (typed-term-list->term-lst
                     (typed-term-list-fix tterm-lst)))
                   1)
    :hints (("Goal"
             :in-theory (enable typed-term-list->term-lst)))
    (b* (((unless (typed-term-list-p tterm-lst)) nil)
         ((unless (consp tterm-lst)) t)
         ((cons tterm-hd tterm-tl) tterm-lst))
      (and (good-typed-term-p tterm-hd options)
           (good-typed-term-list-p tterm-tl options)
           (if tterm-tl ;; added by mrg -- ensures good-typed-term-list-p => uniform-path-cond?
               (equal (typed-term->path-cond tterm-hd)
                      (typed-term-list->path-cond tterm-tl))
             t))))
  ///
   (defthm good-typed-variable-p-of-good-term
     (implies (equal (typed-term->kind tterm) 'variablep)
              (iff (good-typed-term-p tterm options)
                   (good-typed-variable-p tterm options))))
   (defthm good-typed-quote-p-of-good-term
     (implies (equal (typed-term->kind tterm) 'quotep)
              (iff (good-typed-term-p tterm options)
                   (good-typed-quote-p tterm options))))
   ;; (defthm good-typed-lambda-p-of-good-term
   ;;   (implies (equal (typed-term->kind tterm) 'lambdap)
   ;;            (iff (good-typed-term-p tterm options)
   ;;                 (good-typed-lambda-p tterm options))))
   (defthm good-typed-if-p-of-good-term
     (implies (equal (typed-term->kind tterm) 'ifp)
              (iff (good-typed-term-p tterm options)
                   (good-typed-if-p tterm options))))
   (defthm good-typed-fncall-p-of-good-term
     (implies (equal (typed-term->kind tterm) 'fncallp)
              (iff (good-typed-term-p tterm options)
                   (good-typed-fncall-p tterm options))))
   (defthm kind-of-good-typed-if
     (implies (good-typed-if-p tterm options)
              (equal (typed-term->kind tterm) 'ifp)))
   ;; (defthm kind-of-good-typed-lambda
   ;;   (implies (good-typed-lambda-p tterm options)
   ;;            (equal (typed-term->kind tterm) 'lambdap)))
   (defthm kind-of-good-typed-fncall
     (implies (good-typed-fncall-p tterm options)
              (equal (typed-term->kind tterm) 'fncallp)))
   (defthm good-typed-fncall-p-of-exclusion
     (implies (and (good-typed-term-p tterm options)
                   (not (equal (typed-term->kind tterm)
                               'variablep))
                   (not (equal (typed-term->kind tterm)
                               'quotep))
                   ;; (not (equal (typed-term->kind tterm)
                   ;;             'lambdap))
                   (not (equal (typed-term->kind tterm) 'ifp)))
              (good-typed-fncall-p tterm options)))
   (defthm good-typed-term-list-of-nil
     (good-typed-term-list-p nil options)))

(local (in-theory (disable pseudo-termp
                           symbol-listp
                           acl2::pseudo-termp-opener
                           pseudo-term-listp-of-symbol-listp)))

(verify-guards good-typed-term-p)

(defthm good-typed-term-implies-typed-term
  (implies (good-typed-term-p tterm options)
           (typed-term-p tterm))
  :hints (("Goal"
           :in-theory (enable good-typed-term-p))))

(defthm good-typed-term-list-implies-typed-term-list
  (implies (good-typed-term-list-p tterm-lst options)
           (typed-term-list-p tterm-lst))
  :hints (("Goal"
           :in-theory (enable good-typed-term-list-p))))

;; mrg: I added uniform-path-help-when-good-typed-term-list-p and
;;   uniform-path-cond?-when-good-typed-term-list-p.  These are really
;;   more-returns theorems of good-typed-term-listp, but when I try to
;;   state them as such, the proofs take much longer and then fail.
;;   I'm guessing that ACL2 gets lost when pseudo-termp is enabled.
;;   Rather figuring out the various theory hints that would make it
;;   work, I'm just stating the theorems here.
;;     Note that uniform-path-help-when-good-typed-term-list-p conjures up
;;   path-cond as a free variable that just happens to be equal to
;;     (typed-term-list->path-cond tterm-lst).  I suspect this will make it
;;   hard to apply the rule automatically, but it still may be useful in
;;   subsequent arguments about good-typed-term-list-p and
;;   uniform-path-cond?.  Thus, I'm admitting it as a disabled theorem.
(defthmd uniform-path-help-when-good-typed-term-list-p
  (implies (and (good-typed-term-list-p tterm-lst options)
                (equal (typed-term-list->path-cond tterm-lst) path-cond))
           (uniform-path-help tterm-lst path-cond))
  :hints(("Goal"
          :in-theory (enable good-typed-term-list-p uniform-path-help typed-term-list->path-cond))))

(defthm uniform-path-cond?-when-good-typed-term-list-p
  (implies (good-typed-term-list-p tterm-lst options)
           (uniform-path-cond? tterm-lst))
  :hints(("Goal"
          :in-theory (enable uniform-path-cond?)
          :use((:instance uniform-path-help-when-good-typed-term-list-p
                          (path-cond (typed-term-list->path-cond tterm-lst)))))))

;; mrg:  I added the hypothesis
;;         (equal (typed-term->path-cond tterm)
;;                (typed-term-list->path-cond tterm-lst))
;;  which is required to ensure uniform-path-cond?
(defthm good-typed-term-list-of-cons
  (implies (and (type-options-p options)
                (good-typed-term-p tterm options)
                (good-typed-term-list-p tterm-lst options)
                (equal (typed-term->path-cond tterm)
                       (typed-term-list->path-cond tterm-lst)))
           (good-typed-term-list-p (cons tterm tterm-lst) options))
  :hints (("Goal"
           :in-theory (enable good-typed-term-list-p)
           :expand (good-typed-term-list-p (cons tterm tterm-lst) options))))

(defthm good-typed-term-of-car
  (implies (and (type-options-p options)
                (good-typed-term-list-p tterm-lst options)
                (consp tterm-lst))
           (good-typed-term-p (car tterm-lst) options))
  :hints (("Goal"
           :in-theory (enable good-typed-term-list-p)
           :expand (good-typed-term-list-p tterm-lst options))))

(defthm good-typed-term-list-of-cdr
  (implies (and (type-options-p options)
                (good-typed-term-list-p tterm-lst options)
                (consp tterm-lst))
           (good-typed-term-list-p (cdr tterm-lst) options))
  :hints (("Goal"
           :in-theory (enable good-typed-term-list-p)
           :expand (good-typed-term-list-p tterm-lst options))))

(defthm good-typed-term-list-of-make-typed-term-list
  (implies (and (type-options-p options)
                (good-typed-term-list-p tterm-lst options))
           (good-typed-term-list-p
            (make-typed-term-list (typed-term-list->term-lst tterm-lst)
                                  (typed-term-list->path-cond tterm-lst)
                                  (typed-term-list->judgements tterm-lst))
            options)))

(defthm good-typed-term-of-make-typed-term
  (good-typed-term-p (make-typed-term) options)
  :hints (("Goal" :in-theory (enable good-typed-term-p
                                     good-typed-quote-p
                                     is-conjunct-list?
                                     judgement-of-term))))

(defthm good-typed-term-of-make-typed-term-list-with-path-cond
  (good-typed-term-list-p (make-typed-term-list nil path-cond ''t)
                          options)
  :hints (("Goal" :in-theory (enable good-typed-term-list-p
                                     make-typed-term-list))))

(local
 (defthm crock
   (implies (pseudo-termp judges)
            (and (pseudo-termp `(if ,judges 't 'nil))
                 (consp `(if ,judges 't 'nil))
                 (consp (cdddr `(if ,judges 't 'nil))))))
 )

(defthm good-typed-term-of-0-input-fn
  (implies (and (symbolp fn)
                (not (equal fn 'quote))
                (not (equal fn 'if))
                (pseudo-termp path-cond)
                (pseudo-termp judges)
                (type-options-p options))
           (good-typed-term-p
            (typed-term `(,fn) path-cond `(if ,judges 't 'nil))
            options))
  :hints (("Goal"
           :in-theory (enable pseudo-termp good-typed-term-list-p)
           :expand (good-typed-fncall-p
                    (typed-term `(,fn) path-cond `(if ,judges 't 'nil))
                    options))))

;; -------------------------------------------------------------------
;; Theorems for destructors
;; TODO: simplify the proof

(defthm implies-of-good-typed-if
  (implies (and (type-options-p options)
                (good-typed-if-p tterm options))
           (and (consp (cdr (typed-term->term tterm)))
                (consp (cddr (typed-term->term tterm)))
                (consp (cdddr (typed-term->term tterm)))
                (consp (typed-term->judgements tterm))
                (consp (cdr (typed-term->judgements tterm)))
                (consp (cddr (typed-term->judgements tterm)))
                (consp (caddr (typed-term->judgements tterm)))
                (consp (cdddr (typed-term->judgements tterm)))
                (not (cddddr (typed-term->judgements tterm)))
                (consp (cdr (caddr (typed-term->judgements tterm))))
                (consp (cddr (caddr (typed-term->judgements tterm))))
                (consp (caddr (caddr (typed-term->judgements tterm))))
                (consp (cddr (caddr (caddr (typed-term->judgements tterm)))))
                (consp (cdr (caddr (caddr (typed-term->judgements tterm)))))
                (consp (cdddr (caddr (typed-term->judgements tterm))))
                (not (cddddr (caddr (typed-term->judgements tterm))))
                (consp (cdddr (caddr (caddr (typed-term->judgements tterm)))))
                (not (cddddr (caddr (caddr (typed-term->judgements tterm)))))
                (pseudo-termp (cadr (typed-term->judgements tterm)))
                (pseudo-termp (cadr (caddr (typed-term->judgements tterm))))
                (good-typed-term-p
                 (typed-term (cadr (typed-term->term tterm))
                             (typed-term->path-cond tterm)
                             (cadr (caddr (typed-term->judgements tterm))))
                 options)
                (good-typed-term-p
                 (typed-term (caddr (typed-term->term tterm))
                             (list* 'if
                                    (simple-transformer (cadr (typed-term->term tterm)))
                                    (typed-term->path-cond tterm)
                                    '('nil))
                             (caddr (caddr (caddr (typed-term->judgements
                                                   tterm)))))
                 options)
                (good-typed-term-p
                 (typed-term
                  (cadddr (typed-term->term tterm))
                  (list* 'if
                         (simple-transformer (list 'not
                                                   (cadr (typed-term->term tterm))))
                         (typed-term->path-cond tterm)
                         '('nil))
                  (cadddr (caddr (caddr (typed-term->judgements tterm)))))
                 options)
                (pseudo-termp (caddr (caddr (caddr (typed-term->judgements
                                                    tterm)))))
                (pseudo-termp (cadddr (caddr (caddr (typed-term->judgements
                                                     tterm)))))))
  :hints (("Goal"
           :expand (good-typed-if-p tterm options))))

(defthm implies-of-good-typed-fncall
  (implies (and (type-options-p options)
                (good-typed-fncall-p tterm options))
           (and (consp (typed-term->judgements tterm))
                (consp (cdr (typed-term->judgements tterm)))
                (consp (cddr (typed-term->judgements tterm)))
                (consp (cdddr (typed-term->judgements tterm)))
                (pseudo-termp (cadr (typed-term->judgements tterm)))
                (pseudo-termp (caddr (typed-term->judgements tterm)))
                (not (cddddr (typed-term->judgements tterm)))
                (good-typed-term-list-p
                 (make-typed-term-list (cdr (typed-term->term tterm))
                                       (typed-term->path-cond tterm)
                                       (caddr (typed-term->judgements tterm)))
                 options)))
  :hints (("Goal"
           :expand (good-typed-fncall-p tterm options))))

;; (defthm implies-of-good-typed-lambda
;;   (implies (and (type-options-p options)
;;                 (good-typed-lambda-p tterm options))
;;            (and (consp (typed-term->judgements tterm))
;;                 (consp (cdr (typed-term->judgements tterm)))
;;                 (consp (caddr (typed-term->judgements tterm)))
;;                 (consp (cddr (typed-term->judgements tterm)))
;;                 (consp (cdddr (typed-term->judgements tterm)))
;;                 (consp (cadr (caddr (typed-term->judgements tterm))))
;;                 (consp (car (cadr (caddr (typed-term->judgements tterm)))))
;;                 (consp (cdr (caddr (typed-term->judgements tterm))))
;;                 (consp (cdr (car (cadr (caddr (typed-term->judgements tterm))))))
;;                 (consp (cddr (caddr (typed-term->judgements tterm))))
;;                 (consp (cdddr (caddr (typed-term->judgements tterm))))
;;                 (consp (cddr (car (cadr (caddr (typed-term->judgements tterm))))))
;;                 (not (cddddr (typed-term->judgements tterm)))
;;                 (not (cddddr (caddr (typed-term->judgements tterm))))
;;                 (not (cdddr (car (cadr (caddr (typed-term->judgements
;;                                                tterm))))))
;;                 (pseudo-termp (cadr (typed-term->judgements tterm)))
;;                 (good-typed-term-list-p
;;                  (make-typed-term-list (cdr (typed-term->term tterm))
;;                                        (typed-term->path-cond tterm)
;;                                        (caddr (caddr (typed-term->judgements
;;                                                       tterm))))
;;                  options)
;;                 (good-typed-term-p
;;                  (typed-term (caddr (car (typed-term->term tterm)))
;;                              (list* 'if
;;                                     (shadow-path-cond (cadr (car (typed-term->term tterm)))
;;                                                       (typed-term->path-cond tterm))
;;                                     (term-substitution (caddr (caddr (typed-term->judgements tterm)))
;;                                                        (pairlis$ (cdr (typed-term->term tterm))
;;                                                                  (cadr (car (typed-term->term tterm))))
;;                                                        t)
;;                                     '('nil))
;;                              (caddr (car (cadr (caddr (typed-term->judgements tterm))))))
;;                  options)))
;;   :hints (("Goal"
;;            :expand (good-typed-lambda-p tterm options))))

;; ---------------------------------------------
;;       Destructors for typed-terms
(local (in-theory (disable (:executable-counterpart typed-term))))

;; ifp destructors
(define typed-term-if->cond ((tterm typed-term-p)
                             (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm options))
  :returns (new-tt (good-typed-term-p new-tt options))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'ifp)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       (cond-term (cadr tt.term))
       (cond-path-cond tt.path-cond)
       ((mv err cond-judgements)
        (case-match tt.judgements
          ((& & (& judge-cond . &) &)
           (mv nil judge-cond))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-if->cond
            "Malformed if judgements ~q0" tt.judgements)))
    (make-typed-term :term cond-term
                     :path-cond cond-path-cond
                     :judgements cond-judgements))
  ///
  (more-returns
   (new-tt (typed-term-p new-tt)
           :name typed-term-of-typed-term-if->cond)
   (new-tt (implies (and (type-options-p options)
                         (equal (typed-term->kind tterm) 'ifp)
                         (good-typed-term-p tterm options))
                    (< (acl2-count (typed-term->term new-tt))
                       (acl2-count (typed-term->term tterm))))
           ;; I don't know how to remove this hint
           :hints (("Goal"
                    :in-theory (disable good-typed-if-p-of-good-term)
                    :use ((:instance good-typed-if-p-of-good-term))))
           :name acl2-count-of-typed-term-if->cond))
  (defthm correctness-of-typed-term-if->cond
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (good-typed-if-p tterm options)
                  (type-options-p options)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term (typed-term-if->cond tterm options))
                       a))
    :hints (("Goal"
             :in-theory (enable correct-typed-term)
             :expand (good-typed-if-p tterm options)))))

(define typed-term-if->then ((tterm typed-term-p)
                             (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm options))
  :returns (new-tt (good-typed-term-p new-tt options))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'ifp)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((list* & cond then-term &) tt.term)
       (then-path-cond `(if ,(simple-transformer cond)
                            ,tt.path-cond 'nil))
       ((mv err then-judgements)
        (case-match tt.judgements
          ((& & (& & (& & judge-then . &) &) &)
           (mv nil judge-then))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-if->then
            "Malformed if judgements ~q0" tt.judgements)))
    (make-typed-term :term then-term
                     :path-cond then-path-cond
                     :judgements then-judgements))
  ///
  (more-returns
   (new-tt (typed-term-p new-tt)
           :name typed-term-of-typed-term-if->then)
   (new-tt (implies (and (type-options-p options)
                         (equal (typed-term->kind tterm) 'ifp)
                         (good-typed-term-p tterm options))
                    (< (acl2-count (typed-term->term new-tt))
                       (acl2-count (typed-term->term tterm))))
           ;; I don't know how to remove this hint
           :hints (("Goal"
                    :in-theory (disable good-typed-if-p-of-good-term)
                    :use ((:instance good-typed-if-p-of-good-term))))
           :name acl2-count-of-typed-term-if->then))
  (defthm correctness-of-typed-term-if->then
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (good-typed-if-p tterm options)
                  (type-options-p options)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term (typed-term-if->then tterm options))
                       a))
    :hints (("Goal"
             :in-theory (enable correct-typed-term)
             :expand (good-typed-if-p tterm options)))))

(define typed-term-if->else ((tterm typed-term-p)
                             (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm options))
  :returns (new-tt (good-typed-term-p new-tt options))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'ifp)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((list & cond & else-term) tt.term)
       (else-path-cond `(if ,(simple-transformer `(not ,cond))
                            ,tt.path-cond 'nil))
       ((mv err else-judgements)
        (case-match tt.judgements
          ((& & (& & (& & & judge-else) &) &)
           (mv nil judge-else))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-if->else
            "Malformed if judgements ~q0" tt.judgements)))
    (make-typed-term :term else-term
                     :path-cond else-path-cond
                     :judgements else-judgements))
  ///
  (more-returns
   (new-tt (typed-term-p new-tt)
           :name typed-term-of-typed-term-if->else)
   (new-tt (implies (and (type-options-p options)
                         (equal (typed-term->kind tterm) 'ifp)
                         (good-typed-term-p tterm options))
                    (< (acl2-count (typed-term->term new-tt))
                       (acl2-count (typed-term->term tterm))))
           ;; I don't know how to remove this hint
           :hints (("Goal"
                    :in-theory (disable good-typed-if-p-of-good-term)
                    :use ((:instance good-typed-if-p-of-good-term))))
           :name acl2-count-of-typed-term-if->else))
  (defthm correctness-of-typed-term-if->else
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (good-typed-if-p tterm options)
                  (type-options-p options)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term (typed-term-if->else tterm options))
                       a))
    :hints (("Goal"
             :in-theory (enable correct-typed-term)
             :expand (good-typed-if-p tterm options)))))

(define typed-term->top ((tterm typed-term-p)
                         (options type-options-p))
  :guard (and (or (equal (typed-term->kind tterm) 'ifp)
                  ;; (equal (typed-term->kind tterm) 'lambdap)
                  (equal (typed-term->kind tterm) 'fncallp))
              (good-typed-term-p tterm options))
  :returns (new-tt typed-term-p)
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (or (equal (typed-term->kind tterm) 'ifp)
                              ;; (equal (typed-term->kind tterm) 'lambdap)
                              (equal (typed-term->kind tterm) 'fncallp))
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((mv err top-judge)
        (case-match tt.judgements
          ((& top-judge & &)
           (mv nil top-judge))
          (& (mv t nil))))
       ((if err)
        (prog2$ (er hard? 'typed-term=>typed-term->top
                    "Malformed judgements ~q0" tt.judgements)
                (make-typed-term))))
    (make-typed-term :term tt.term
                     :path-cond tt.path-cond
                     :judgements top-judge))
  ///
  (defthm correctness-of-typed-term-if->top
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (and (or (equal (typed-term->kind tterm) 'ifp)
                           ;; (equal (typed-term->kind tterm) 'lambdap)
                           (equal (typed-term->kind tterm) 'fncallp))
                       (good-typed-term-p tterm options))
                  (type-options-p options)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term (typed-term->top tterm options))
                       a))
    :hints (("Goal"
             :in-theory (enable correct-typed-term)
             :expand ((good-typed-if-p tterm options)
                      (good-typed-fncall-p tterm options))))))

(defthm lemma1
  (implies (and (good-typed-fncall-p tterm options)
                (type-options-p options)
                (consp (make-typed-term-list
                        (cdr (typed-term->term tterm))
                        (typed-term->path-cond tterm)
                        (caddr (typed-term->judgements tterm)))))
           (equal (typed-term->path-cond
                   (car (make-typed-term-list
                         (cdr (typed-term->term tterm))
                         (typed-term->path-cond tterm)
                         (caddr (typed-term->judgements tterm)))))
                  (typed-term->path-cond tterm)))
  :hints (("Goal"
           :in-theory (enable make-typed-term-list)
           :expand (make-typed-term-list
                    (cdr (typed-term->term tterm))
                    (typed-term->path-cond tterm)
                    (caddr (typed-term->judgements tterm))))))

(defthm lemma2
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (good-typed-fncall-p tterm options)
                (type-options-p options)
                (alistp a)
                (ev-smtcp (typed-term->judgements tterm)
                          a))
           (ev-smtcp (caddr (typed-term->judgements tterm))
                     a))
  :hints (("Goal"
           :expand (good-typed-fncall-p tterm options))))

;; fncallp destructors
(define typed-term-fncall->actuals ((tterm typed-term-p)
                                    (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'fncallp)
              (good-typed-term-p tterm options))
  :guard-hints (("Goal"
                 :expand (good-typed-fncall-p tterm options)))
  :returns (new-ttl (good-typed-term-list-p new-ttl options))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'fncallp)
                          (good-typed-term-p tterm options))))
        nil)
       ((typed-term tt) tterm)
       ((cons & actuals) tt.term)
       ((mv err actuals-judgements)
        (case-match tt.judgements
          ((& & actuals-judge . &)
           (mv nil actuals-judge))
          (& (mv t nil))))
       ((if (or err
                (not (make-typed-term-list-guard actuals tt.path-cond
                                                 actuals-judgements))))
        (prog2$ (er hard? 'typed-term=>typed-term-fncall->actuals
                    "Malformed fncall judgements ~q0" tt.judgements)
                nil)))
    (make-typed-term-list actuals tt.path-cond actuals-judgements))
  ///
  (more-returns
   (new-ttl (typed-term-list-p new-ttl)
            :name typed-term-list-of-typed-term-fncall->actuals)
   (new-ttl (implies (and (type-options-p options)
                          (equal (typed-term->kind tterm) 'fncallp)
                          (good-typed-term-p tterm options))
                     (< (acl2-count
                         (typed-term-list->term-lst new-ttl))
                        (acl2-count (typed-term->term tterm))))
            :name acl2-count-of-make-typed-fncall))
  (defthm correctness-of-typed-term-fncall->actuals
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (good-typed-fncall-p tterm options)
                  (type-options-p options)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term-list
                        (typed-term-fncall->actuals tterm options))
                       a))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (correct-typed-term
                              correct-typed-term-list
                              typed-term-list->path-cond)
                             (make-typed-term-list-guard))
             :use ((:instance make-typed-term-list-guard-of-not-consp
                              (term-lst (cdr (typed-term->term tterm)))
                              (path-cond (typed-term->path-cond tterm))
                              (judges (caddr (typed-term->judgements tterm))))))))
  )

;; ;; lambdap destructors
;; (define typed-term-lambda->actuals ((tterm typed-term-p)
;;                                     (options type-options-p))
;;   :guard (and (equal (typed-term->kind tterm) 'lambdap)
;;               (good-typed-term-p tterm options))
;;   :guard-hints (("Goal"
;;                  :expand (good-typed-lambda-p tterm options)))
;;   :returns (new-ttl (good-typed-term-list-p new-ttl options))
;;   (b* (((unless (mbt (and (typed-term-p tterm)
;;                           (type-options-p options)
;;                           (equal (typed-term->kind tterm) 'lambdap)
;;                           (good-typed-term-p tterm options))))
;;         nil)
;;        ((typed-term tt) tterm)
;;        ((cons & actuals) tt.term)
;;        ((mv err actuals-judgements)
;;         (case-match tt.judgements
;;           ((& & (& & actuals-judge . &) &)
;;            (mv nil actuals-judge))
;;           (& (mv t nil))))
;;        ((if err)
;;         (er hard? 'typed-term=>typed-term-lambda->actuals
;;             "Malformed lambda judgements ~q0" tt.judgements)))
;;     (make-typed-term-list actuals tt.path-cond actuals-judgements))
;;   ///
;;   (more-returns
;;    (new-ttl (typed-term-list-p new-ttl)
;;             :name typed-term-list-of-typed-term-lambda->actuals)
;;    (new-ttl (implies (and (equal (typed-term->kind tterm)
;;                                  'lambdap)
;;                           (good-typed-term-p tterm options))
;;                      (< (acl2-count
;;                          (typed-term-list->term-lst new-ttl))
;;                         (acl2-count (typed-term->term tterm))))
;;             :name acl2-count-of-typed-term-lambda->actuals)
;;    ;; (new-ttl (implies (and (typed-term-p tterm)
;;    ;;                        (type-options-p options)
;;    ;;                        (equal (typed-term->kind tterm)
;;    ;;                               'lambdap)
;;    ;;                        (good-typed-term-p tterm options))
;;    ;;                   (equal (len (cdr (typed-term->term tterm)))
;;    ;;                          (len (typed-term-list->term-lst new-ttl))))
;;    ;;          :name typed-term-lambda->actuals-preserve-len
;;    ;;          :hints (("Goal"
;;    ;;                   :in-theory (enable typed-term-list->term-lst)
;;    ;;                   :expand (typed-term-lambda->actuals tterm options))))
;;    ))

;; (define typed-term-lambda->body ((tterm typed-term-p)
;;                                  (options type-options-p))
;;   :guard (and (equal (typed-term->kind tterm) 'lambdap)
;;               (good-typed-term-p tterm options))
;;   :guard-hints (("Goal"
;;                  :expand (good-typed-lambda-p tterm options)))
;;   :returns (new-tt (good-typed-term-p new-tt options))
;;   (b* (((unless (mbt (and (typed-term-p tterm)
;;                           (type-options-p options)
;;                           (equal (typed-term->kind tterm) 'lambdap)
;;                           (good-typed-term-p tterm options))))
;;         (make-typed-term))
;;        ((typed-term tt) tterm)
;;        ((cons fn actuals) tt.term)
;;        (formals (lambda-formals fn))
;;        (body (lambda-body fn))
;;        (shadowed-path-cond (shadow-path-cond formals tt.path-cond))
;;        ((mv err body-judgements actuals-judges)
;;         (case-match tt.judgements
;;           ((& & (& ((& & body-judge) . &) actuals-judges &) &)
;;            (mv nil body-judge actuals-judges))
;;           (& (mv t nil nil))))
;;        ((if err)
;;         (er hard? 'typed-term=>typed-term-lambda->body
;;             "Malformed lambda judgements ~q0" tt.judgements))
;;        (substed-actuals-judgements
;;         (term-substitution actuals-judges (pairlis$ actuals formals) t)))
;;     (make-typed-term :term body
;;                      :path-cond `(if ,shadowed-path-cond
;;                                      ,substed-actuals-judgements 'nil)
;;                      :judgements body-judgements))
;;   ///
;;   (more-returns
;;    (new-tt (typed-term-p new-tt)
;;            :name typed-term-of-typed-term-lambda->body)
;;    (new-tt (implies (and (type-options-p options)
;;                          (equal (typed-term->kind tterm)
;;                                 'lambdap)
;;                          (good-typed-term-p tterm options))
;;                     (< (acl2-count (typed-term->term new-tt))
;;                        (acl2-count (typed-term->term tterm))))
;;            ;; I don't know how to remove this hint
;;            :hints (("Goal"
;;                     :in-theory (disable good-typed-lambda-p-of-good-term)
;;                     :use ((:instance good-typed-lambda-p-of-good-term))))
;;            :name acl2-count-of-typed-term-lambda->body)))

;; --------------------------------------------------------------------
;;      Constructors

(defthm kind-of-make-typed-if
  (implies
     (and (typed-term-p tt-top)
          (good-typed-term-p tt-cond options)
          (good-typed-term-p tt-then options)
          (good-typed-term-p tt-else options))
     (equal (typed-term->kind
             (typed-term (list 'if
                               (typed-term->term tt-cond)
                               (typed-term->term tt-then)
                               (typed-term->term tt-else))
                         (typed-term->path-cond tt-top)
                         (list* 'if
                                (typed-term->judgements tt-top)
                                (list* 'if
                                       (typed-term->judgements tt-cond)
                                       (list 'if
                                             (typed-term->term tt-cond)
                                             (typed-term->judgements tt-then)
                                             (typed-term->judgements tt-else))
                                       '('nil))
                                '('nil))))
            'ifp))
  :hints (("Goal"
           :in-theory (enable typed-term->kind))))

(define make-typed-if ((tt-top typed-term-p)
                       (tt-cond typed-term-p)
                       (tt-then typed-term-p)
                       (tt-else typed-term-p)
                       (options type-options-p))
  :guard (and (good-typed-term-p tt-cond options)
              (good-typed-term-p tt-then options)
              (good-typed-term-p tt-else options))
  :returns (new-tt (good-typed-term-p new-tt options)
                   :hints (("Goal"
                            :in-theory (enable good-typed-if-p))))
  (b* (((unless (mbt (and (type-options-p options)
                          (typed-term-p tt-top)
                          (typed-term-p tt-cond)
                          (typed-term-p tt-then)
                          (typed-term-p tt-else)
                          (good-typed-term-p tt-cond options)
                          (good-typed-term-p tt-then options)
                          (good-typed-term-p tt-else options))))
        (make-typed-term))
       ((typed-term ttp) tt-top)
       ((typed-term ttc) tt-cond)
       ((typed-term ttt) tt-then)
       ((typed-term tte) tt-else)
       ((unless (and (equal ttc.path-cond ttp.path-cond)
                     (equal ttt.path-cond
                            `(if ,(simple-transformer ttc.term)
                                 ,ttc.path-cond 'nil))
                     (equal tte.path-cond
                            `(if ,(simple-transformer `(not ,ttc.term))
                                 ,ttc.path-cond 'nil))))
        (prog2$
         (er hard? 'typed-term=>make-typed-term-if
             "Inconsistent inputs.~%")
         tt-cond)))
    (make-typed-term
     :term `(if ,ttc.term ,ttt.term ,tte.term)
     :path-cond ttp.path-cond
     :judgements
     `(if ,ttp.judgements
          (if ,ttc.judgements
              (if ,ttc.term ,ttt.judgements ,tte.judgements)
            'nil)
        'nil)))
  ///
  (more-returns
   (new-tt (typed-term-p new-tt)
           :name typed-term-of-make-typed-if))
  (defthm correctness-of-make-typed-if
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (type-options-p options)
                  (typed-term-p tt-top)
                  (good-typed-term-p tt-cond options)
                  (good-typed-term-p tt-then options)
                  (good-typed-term-p tt-else options)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tt-top) a)
                  (ev-smtcp (correct-typed-term tt-cond) a)
                  (ev-smtcp (correct-typed-term tt-then) a)
                  (ev-smtcp (correct-typed-term tt-else) a))
             (ev-smtcp (correct-typed-term
                        (make-typed-if tt-top tt-cond tt-then tt-else options))
                       a))
    :hints (("Goal"
             :in-theory (e/d (correct-typed-term) ())))))

;; (local
;;  (defthm pseudo-termp-of-lambda
;;    (implies (and (symbol-listp formals)
;;                  (pseudo-termp body-judge)
;;                  (pseudo-term-listp actuals)
;;                  (equal (len formals) (len actuals)))
;;             (pseudo-termp
;;              `((lambda ,formals ,body-judge) ,@actuals)))
;;    :hints (("Goal"
;;             :in-theory (enable pseudo-termp))))
;;  )

;; (defthm kind-of-make-typed-lambda
;;   (implies
;;      (and (typed-term-p tt-top)
;;           (good-typed-term-p tt-body options)
;;           (good-typed-term-list-p tt-actuals options)
;;           (pseudo-lambdap (car (typed-term->term tt-top))))
;;      (equal (typed-term->kind
;;              (typed-term
;;               (typed-term->term tt-top)
;;               (typed-term->path-cond tt-top)
;;               (list* 'if
;;                      (typed-term->judgements tt-top)
;;                      (list* 'if
;;                             (cons (list 'lambda
;;                                         (cadr (car (typed-term->term tt-top)))
;;                                         (typed-term->judgements tt-body))
;;                                   (typed-term-list->term-lst tt-actuals))
;;                             (typed-term-list->judgements tt-actuals)
;;                             '('nil))
;;                      '('nil))))
;;             'lambdap))
;;   :hints (("Goal"
;;            :in-theory (enable typed-term->kind))))

;; (define make-typed-lambda ((tt-top typed-term-p)
;;                            (tt-body typed-term-p)
;;                            (tt-actuals typed-term-list-p)
;;                            (options type-options-p))
;;   :guard (and (good-typed-term-p tt-body options)
;;               (good-typed-term-list-p tt-actuals options))
;;   :returns (new-tt (good-typed-term-p new-tt options)
;;                    :hints (("Goal"
;;                             :in-theory (enable good-typed-lambda-p))))
;;   (b* (((unless (mbt (and (type-options-p options)
;;                           (typed-term-p tt-top)
;;                           (typed-term-p tt-body)
;;                           (typed-term-list-p tt-actuals)
;;                           (good-typed-term-p tt-body options)
;;                           (good-typed-term-list-p tt-actuals options))))
;;         (make-typed-term))
;;        ((typed-term ttt) tt-top)
;;        ((typed-term ttb) tt-body)
;;        (tta.term-lst (typed-term-list->term-lst tt-actuals))
;;        (tta.path-cond (typed-term-list->path-cond tt-actuals))
;;        (tta.judgements (typed-term-list->judgements tt-actuals))
;;        ((unless (and (consp ttt.term)
;;                      (pseudo-lambdap (car ttt.term))))
;;         (prog2$ (er hard? 'typed-term=>make-typed-term-lambda
;;                     "Inconsistent inputs.~%")
;;                 (make-typed-term)))
;;        (formals (lambda-formals (car ttt.term)))
;;        (body (lambda-body (car ttt.term)))
;;        (actuals (cdr ttt.term))
;;        (body-path-cond
;;         `(if ,(shadow-path-cond formals ttt.path-cond)
;;              ,(term-substitution tta.judgements
;;                                  (pairlis$ tta.term-lst formals) t)
;;            'nil))
;;        (- (cw "formals: ~p0 actuals ~p1 body: ~p2~%" formals actuals body))
;;        (- (cw "tta.term-lst: ~q0" tta.term-lst))
;;        (- (cw "ttb.path-cond: ~q0" ttb.path-cond))
;;        (- (cw "ttb.term: ~q0" ttb.term))
;;        (- (cw "body-path-cond: ~q0" body-path-cond))
;;        (- (cw "ttt.path-cond: ~q0" ttt.path-cond))
;;        (- (cw "tta.path-cond: ~q0" tta.path-cond))
;;        ((unless (and (equal tta.term-lst actuals)
;;                      (equal body ttb.term)
;;                      (equal (len formals) (len actuals))
;;                      (equal ttb.path-cond body-path-cond)
;;                      (equal ttt.path-cond tta.path-cond)))
;;         (prog2$ (er hard? 'typed-term=>make-typed-term-lambda
;;                     "Inconsistent inputs.~%")
;;                 (make-typed-term))))
;;     (make-typed-term
;;      :term ttt.term
;;      :path-cond ttt.path-cond
;;      :judgements `(if ,ttt.judgements
;;                       (if ((lambda ,formals
;;                              ,ttb.judgements)
;;                            ,@actuals)
;;                           ,tta.judgements
;;                         'nil)
;;                     'nil)))
;;   ///
;;   (more-returns
;;    (new-tt (typed-term-p new-tt)
;;            :name typed-term-of-make-typed-lambda)))

(defthm kind-of-make-typed-fncall
  (implies
     (and (typed-term-p tt-top)
          (good-typed-term-list-p tt-actuals options)
          (consp (typed-term->term tt-top))
          (symbolp (car (typed-term->term tt-top)))
          (not (equal (car (typed-term->term tt-top)) 'quote))
          (not (equal (car (typed-term->term tt-top)) 'if)))
     (equal (typed-term->kind
             (typed-term (typed-term->term tt-top)
                         (typed-term->path-cond tt-top)
                         (list* 'if
                                (typed-term->judgements tt-top)
                                (typed-term-list->judgements tt-actuals)
                                '('nil))))
            'fncallp))
  :hints (("Goal"
           :in-theory (enable typed-term->kind))))

(define make-typed-fncall-guard ((tt-top typed-term-p)
                                 (tt-actuals typed-term-list-p)
                                 (options type-options-p))
  :returns (ok booleanp)
  (b* (((unless (mbt (and (typed-term-p tt-top)
                          (typed-term-list-p tt-actuals)
                          (type-options-p options))))
        nil)
       ((typed-term ttt) tt-top)
       (tta.term-lst (typed-term-list->term-lst tt-actuals))
       (tta.path-cond (typed-term-list->path-cond tt-actuals)))
    (and (good-typed-term-list-p tt-actuals options)
         (consp ttt.term)
         (symbolp (car ttt.term))
         (not (equal (car ttt.term) 'quote))
         (not (equal (car ttt.term) 'if))
         (equal (cdr ttt.term) tta.term-lst)
         (equal ttt.path-cond tta.path-cond))))

(define make-typed-fncall ((tt-top typed-term-p)
                           (tt-actuals typed-term-list-p)
                           (options type-options-p))
  :guard (make-typed-fncall-guard tt-top tt-actuals options)
  :returns (new-tt (good-typed-term-p new-tt options)
                   :hints (("Goal"
                            :in-theory (enable good-typed-fncall-p
                                               make-typed-fncall-guard))))
  (b* (((unless (mbt (make-typed-fncall-guard tt-top tt-actuals options)))
        (make-typed-term))
       ((typed-term ttt) tt-top)
       (tta.judgements (typed-term-list->judgements tt-actuals)))
    (make-typed-term
     :term ttt.term
     :path-cond ttt.path-cond
     :judgements `(if ,ttt.judgements ,tta.judgements 'nil)))
  ///
  (more-returns
   (new-tt (typed-term-p new-tt)
           :name typed-term-of-make-typed-fncall)
   (new-tt (implies (make-typed-fncall-guard tt-top tt-actuals options)
                    (equal (typed-term->term new-tt)
                           (typed-term->term tt-top)))
           :name make-typed-fncall-maintains-term)
   (new-tt (implies (make-typed-fncall-guard tt-top tt-actuals options)
                    (equal (typed-term->path-cond new-tt)
                           (typed-term->path-cond tt-top)))
           :name make-typed-fncall-maintains-path-cond))
  (defthm correctness-of-make-typed-fncall
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (type-options-p options)
                  (good-typed-term-p tt-top options)
                  (good-typed-term-list-p tt-actuals options)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tt-top) a)
                  (ev-smtcp (correct-typed-term-list tt-actuals) a))
             (ev-smtcp (correct-typed-term
                        (make-typed-fncall tt-top tt-actuals options))
                       a))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (correct-typed-term
                              correct-typed-term-list
                              make-typed-fncall-guard)
                             ()))))
  )
