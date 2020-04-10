;; Copyright (C) 2019, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "./utils/pseudo-term")
(include-book "path-cond")
(include-book "term-substitution")

;; reduce not's in term
(define simple-transformer ((term pseudo-termp))
  :returns (new-term pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (new-term
        (case-match term
          (('not ('not term1)) term1)
          (& term))))
    new-term))

(encapsulate ()
  (local (in-theory (disable pseudo-termp)))

  (fty::defprod typed-term
    ((term pseudo-termp :default ''nil)
     (path-cond pseudo-termp :default ''t)
     (judgements pseudo-termp :default '(if (if (symbolp 'nil)
                                                (if (booleanp 'nil) 't 'nil)
                                              'nil)
                                            't
                                          'nil))))

  (fty::defprod typed-term-list
    ((term-lst pseudo-term-listp :default nil)
     (path-cond pseudo-termp :default ''t)
     (judgements pseudo-termp :default ''t)))

  (fty::defoption maybe-typed-term typed-term-p)
  )

(define typed-term-list-consp ((tterm-lst typed-term-list-p))
  :returns (ok booleanp)
  (b* ((tterm-lst (typed-term-list-fix tterm-lst))
       ((typed-term-list ttl) tterm-lst))
    (consp ttl.term-lst))
  ///
  (more-returns
   (ok (implies (and (typed-term-list-p tterm-lst) ok)
                (consp (typed-term-list->term-lst tterm-lst)))
       :name consp-of-term-lst-of-typed-term-list-consp)))

;; ---------------------------------------------
;;       Recognizers

(define typed-term->kind ((tterm typed-term-p))
  :returns (kind symbolp)
  (b* ((tterm (typed-term-fix tterm))
       ((typed-term tt) tterm)
       ((if (acl2::variablep tt.term)) 'variablep)
       ((if (acl2::quotep tt.term)) 'quotep)
       ((cons fn &) tt.term)
       ((if (pseudo-lambdap fn)) 'lambdap)
       ((if (equal fn 'if)) 'ifp))
    'fncallp)
  ///
  (more-returns
   (kind (member-equal kind '(variablep quotep lambdap ifp fncallp))
         :name range-of-typed-term->kind)
   (kind (implies (and (typed-term-p tterm)
                       (not (equal kind 'variablep))
                       (not (equal kind 'quotep))
                       (not (equal kind 'lambdap))
                       (not (equal kind 'ifp)))
                  (equal kind 'fncallp))
         :name cases-of-typed-term->kind)
   (kind (implies (equal kind 'variablep)
                  (acl2::variablep (typed-term->term tterm)))
         :name implies-of-variable-kind)
   (kind (implies (equal kind 'quotep)
                  (acl2::quotep (typed-term->term tterm)))
         :name implies-of-quote-kind)
   (kind (implies (equal kind 'lambdap)
                  (and (consp (typed-term->term tterm))
                       (pseudo-lambdap (car (typed-term->term tterm)))))
         :name implies-of-lambda-kind)
   (kind (implies (equal kind 'ifp)
                  (and (consp (typed-term->term tterm))
                       (equal (car (typed-term->term tterm)) 'if)))
         :name implies-of-if-kind)
   (kind (implies (equal kind 'fncallp)
                  (and (consp (typed-term->term tterm))
                       (not (equal (car (typed-term->term tterm)) 'quote))
                       (symbolp (car (typed-term->term tterm)))))
         :name implies-of-fncall-kind)
   (kind (implies (equal kind x)
                  (equal (typed-term->kind
                          (typed-term (typed-term->term tterm) a b))
                         x))
         :name kind-preserved)))

(define good-typed-variable-p ((tterm typed-term-p)
                               (options type-options-p))
  :returns (ok booleanp)
  (b* ((tterm (typed-term-fix tterm))
       (options (type-options-fix options))
       ((typed-term tt) tterm)
       ((type-options to) options))
    ;; (if (is-conjunct-list? tt.judgements tt.term to.supertype) t nil)
    t))

#|
(good-typed-variable-p (typed-term 'x
                                   ''t
                                   '(if (if (booleanp (rational-integer-alistp x))
                                            't
                                          'nil)
                                        (if (if 't 't 'nil) 't 'nil)
                                      'nil)))
|#

(define good-typed-quote-p ((tterm typed-term-p)
                            (options type-options-p))
  :returns (ok booleanp)
  (b* ((tterm (typed-term-fix tterm))
       (options (type-options-fix options))
       ((typed-term tt) tterm)
       ((type-options to) options))
    ;; (if (is-conjunct-list? tt.judgements tt.term to.supertype) t nil)
    t))

#|
(good-typed-quote-p (typed-term ''t
                                ''t
                                '(if (if (symbolp 't)
                                         (if (booleanp 't) 't 'nil)
                                       'nil)
                                     't
                                   'nil)))
|#

(defines good-typed-term
  :well-founded-relation l<
  :verify-guards nil
  :hints (("Goal"
           :in-theory (disable pseudo-termp
                               equal-fixed-and-x-of-pseudo-termp
                               symbol-listp
                               pseudo-term-listp
                               acl2::pseudo-termp-cadr-from-pseudo-term-listp)))

  (define good-typed-lambda-p ((tterm typed-term-p)
                               (options type-options-p))
    :returns (ok booleanp)
    :guard (and (consp (typed-term->term tterm))
                (pseudo-lambdap (car (typed-term->term tterm))))
    :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                   0)
    :ignore-ok t
    (b* ((tterm (typed-term-fix tterm))
         (options (type-options-fix options))
         ((typed-term tt) tterm)
         ((type-options to) options)
         ((unless (mbt (and (consp tt.term)
                            (pseudo-lambdap (car tt.term)))))
          nil)
         ((cons fn actuals) tt.term)
         (formals (lambda-formals fn))
         (body (lambda-body fn))
         ((unless (consp tt.judgements)) nil)
         (match?
          (case-match tt.judgements
            (('if return-judge
                 ('if (('lambda !formals body-judge) . !actuals)
                     actuals-judge
                   ''nil)
               ''nil)
             (and ;; (is-conjunct-list? return-judge tt.term to.supertype)
                  (good-typed-term-list-p
                   (make-typed-term-list :term-lst actuals
                                         :path-cond tt.path-cond
                                         :judgements actuals-judge)
                   to)
                  (b* ((shadowed-path-cond (shadow-path-cond formals tt.path-cond)))
                    (good-typed-term-p
                     (make-typed-term :term body
                                      :path-cond shadowed-path-cond
                                      :judgements body-judge)
                     to))))
            (& nil))))
      (if match? t nil)))

  (define good-typed-if-p ((tterm typed-term-p)
                           (options type-options-p))
    :returns (ok booleanp)
    :guard (and (consp (typed-term->term tterm))
                (equal (car (typed-term->term tterm)) 'if))
    :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                   0)
    :ignore-ok t
    (b* ((tterm (typed-term-fix tterm))
         (options (type-options-fix options))
         ((typed-term tt) tterm)
         ((type-options to) options)
         ((unless (mbt (and (consp tt.term)
                            (equal (car tt.term) 'if))))
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

  (define good-typed-fncall-p ((tterm typed-term-p)
                               (options type-options-p))
    :returns (ok booleanp)
    :guard (and (consp (typed-term->term tterm))
                (not (equal (car (typed-term->term tterm)) 'quote))
                (symbolp (car (typed-term->term tterm))))
    :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                   0)
    :ignore-ok t
    (b* ((tterm (typed-term-fix tterm))
         (options (type-options-fix options))
         ((typed-term tt) tterm)
         ((type-options to) options)
         ((unless (mbt (consp tt.term))) nil)
         ((cons & actuals) tt.term)
         ((unless (consp tt.judgements)) nil)
         (match?
          (case-match tt.judgements
            (('if return-judge actuals-judge ''nil)
             (and ;; (is-conjunct-list? return-judge tt.term to.supertype)
                  (good-typed-term-list-p
                   (make-typed-term-list :term-lst actuals
                                         :path-cond tt.path-cond
                                         :judgements actuals-judge)
                   options)))
            (& nil))))
      (if match? t nil)))

  (define good-typed-term-p ((tterm typed-term-p)
                             (options type-options-p))
    :returns (ok booleanp)
    :measure (list (acl2-count
                    (typed-term->term
                     (typed-term-fix tterm)))
                   1)
    (b* ((tterm (typed-term-fix tterm))
         ((typed-term tt) tterm)
         ((if (equal (typed-term->kind tt) 'variablep))
          (good-typed-variable-p tt options))
         ((if (equal (typed-term->kind tt) 'quotep))
          (good-typed-quote-p tt options))
         ((if (equal (typed-term->kind tt) 'lambdap))
          (good-typed-lambda-p tt options))
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
    (b* ((tterm-lst (typed-term-list-fix tterm-lst))
         ((typed-term-list ttl) tterm-lst)
         ((unless (is-conjunct? ttl.judgements))
          (er hard? 'typed-term=>good-typed-term-list-p
              "Judgements ~p0 is not a conjunct.~%" ttl.judgements))
         ((if (and (null ttl.term-lst) (equal ttl.judgements ''t))) t)
         ((unless (consp ttl.term-lst))
          (er hard? 'typed-term=>good-typed-term-list-p
              "Term runs out but there are judgements left ~p0.~%"
              ttl.judgements))
         ((if (equal ttl.judgements ''t))
          (er hard? 'typed-term=>good-typed-term-list-p
              "Judgements runs out but there are terms left ~p0.~%"
              ttl.term-lst))
         ((cons term-hd term-tl) ttl.term-lst)
         ((mv err judge-hd judge-tl)
          (case-match ttl.judgements
            (('if judge-hd judge-tl ''nil)
             (mv nil judge-hd judge-tl))
            (& (mv t nil nil))))
         ((if err)
          (er hard? 'typed-term=>good-typed-term-list-p
              "Malformed typed-term-list: ~p0~%"
              ttl.term-lst)))
      (and (good-typed-term-p
            (make-typed-term :term term-hd
                             :path-cond ttl.path-cond
                             :judgements judge-hd)
            options)
           (good-typed-term-list-p
            (make-typed-term-list :term-lst term-tl
                                  :path-cond ttl.path-cond
                                  :judgements judge-tl)
            options))))
  ///
   (defthm good-typed-variable-p-of-good-term
     (implies (and (typed-term-p tterm)
                   (equal (typed-term->kind tterm) 'variablep))
              (iff (good-typed-term-p tterm options)
                   (good-typed-variable-p tterm options))))
   (defthm good-typed-quote-p-of-good-term
     (implies (and (typed-term-p tterm)
                   (equal (typed-term->kind tterm) 'quotep))
              (iff (good-typed-term-p tterm options)
                   (good-typed-quote-p tterm options))))
   (defthm good-typed-lambda-p-of-good-term
     (implies (and (typed-term-p tterm)
                   (equal (typed-term->kind tterm) 'lambdap))
              (iff (good-typed-term-p tterm options)
                   (good-typed-lambda-p tterm options))))
   (defthm good-typed-if-p-of-good-term
     (implies (and (typed-term-p tterm)
                   (equal (typed-term->kind tterm) 'ifp))
              (iff (good-typed-term-p tterm options)
                   (good-typed-if-p tterm options))))
   (defthm good-typed-fncall-p-of-good-term
     (implies (and (typed-term-p tterm)
                   (equal (typed-term->kind tterm) 'fncallp))
              (iff (good-typed-term-p tterm options)
                   (good-typed-fncall-p tterm options))))
  )

(local (in-theory (disable pseudo-termp
                           symbol-listp
                           acl2::pseudo-termp-opener
                           pseudo-term-listp-of-symbol-listp)))

(verify-guards good-typed-term-p)

(defthm kind-of-make-typed-term-change
  (equal (typed-term->kind
          (typed-term ''nil
                      path-cond
                      '(if (if (symbolp 'nil)
                               (if (booleanp 'nil) 't 'nil)
                               'nil)
                           't
                           'nil)))
         'quotep)
  :hints (("Goal"
           :in-theory (enable typed-term->kind))))

(defthm good-typed-term-of-make-typed-term
  (good-typed-term-p (make-typed-term) options)
  :hints (("Goal" :in-theory (enable good-typed-term-p
                                     good-typed-quote-p
                                     is-conjunct-list?
                                     judgement-of-term))))

(defthm good-typed-term-of-make-typed-term-change
  (good-typed-term-p
   (change-typed-term (make-typed-term) :path-cond path-cond)
   options)
  :hints (("Goal" :in-theory (enable good-typed-term-p
                                     good-typed-quote-p
                                     is-conjunct-list?
                                     judgement-of-term))))

(defthm good-typed-term-list-of-make-typed-term-list
  (good-typed-term-list-p (make-typed-term-list) options)
  :hints (("Goal" :in-theory (enable good-typed-term-list-p))))

(defthm good-typed-term-of-make-typed-term-list-change
  (good-typed-term-list-p
   (typed-term-list nil path-cond ''t)
   options)
  :hints (("Goal" :in-theory (enable good-typed-term-list-p))))

;; -------------------------------------------------------------------
;; Theorems for destructors
;; TODO: simplify the proof

(defthm implies-of-good-typed-if
  (implies (and (typed-term-p tterm) (type-options-p options)
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
  (implies (and (typed-term-p tterm) (type-options-p options)
                (good-typed-fncall-p tterm options))
           (and (consp (typed-term->judgements tterm))
                (consp (cdr (typed-term->judgements tterm)))
                (consp (cddr (typed-term->judgements tterm)))
                (consp (cdddr (typed-term->judgements tterm)))
                (pseudo-termp (cadr (typed-term->judgements tterm)))
                (pseudo-termp (caddr (typed-term->judgements tterm)))
                (not (cddddr (typed-term->judgements tterm)))
                (good-typed-term-list-p
                 (typed-term-list (cdr (typed-term->term tterm))
                                  (typed-term->path-cond tterm)
                                  (caddr (typed-term->judgements tterm)))
                 options)))
  :hints (("Goal"
           :expand (good-typed-fncall-p tterm options))))

(defthm implies-of-good-typed-lambda
  (implies (and (typed-term-p tterm) (type-options-p options)
                (good-typed-lambda-p tterm options))
           (and (consp (typed-term->judgements tterm))
                (consp (cdr (typed-term->judgements tterm)))
                (consp (caddr (typed-term->judgements tterm)))
                (consp (cddr (typed-term->judgements tterm)))
                (consp (cdddr (typed-term->judgements tterm)))
                (consp (cadr (caddr (typed-term->judgements tterm))))
                (consp (car (cadr (caddr (typed-term->judgements tterm)))))
                (consp (cdr (caddr (typed-term->judgements tterm))))
                (consp (cdr (car (cadr (caddr (typed-term->judgements tterm))))))
                (consp (cddr (caddr (typed-term->judgements tterm))))
                (consp (cdddr (caddr (typed-term->judgements tterm))))
                (consp (cddr (car (cadr (caddr (typed-term->judgements tterm))))))
                (not (cddddr (typed-term->judgements tterm)))
                (not (cddddr (caddr (typed-term->judgements tterm))))
                (not (cdddr (car (cadr (caddr (typed-term->judgements
                                               tterm))))))
                (pseudo-termp (cadr (typed-term->judgements tterm)))
                (good-typed-term-list-p
                 (typed-term-list (cdr (typed-term->term tterm))
                                  (typed-term->path-cond tterm)
                                  (caddr (caddr (typed-term->judgements
                                                 tterm))))
                 options)
                (good-typed-term-p
                 (typed-term (caddr (car (typed-term->term tterm)))
                             (shadow-path-cond (cadr (car (typed-term->term tterm)))
                                               (typed-term->path-cond tterm))
                             (caddr (car (cadr (caddr (typed-term->judgements tterm))))))
                 options)))
  :hints (("Goal"
           :expand (good-typed-lambda-p tterm options))))

(defthm implies-of-good-typed-term-list
  (implies (and (typed-term-list-p tterm-lst)
                (type-options-p options)
                (good-typed-term-list-p tterm-lst options)
                (typed-term-list-consp tterm-lst))
           (and (consp (typed-term-list->judgements tterm-lst))
                (pseudo-termp (cadr (typed-term-list->judgements tterm-lst)))
                (not (cddddr (typed-term-list->judgements tterm-lst)))
                (consp (cddr (typed-term-list->judgements tterm-lst)))
                (consp (cdr (typed-term-list->judgements tterm-lst)))
                (consp (cdddr (typed-term-list->judgements tterm-lst)))
                (pseudo-termp (caddr (typed-term-list->judgements tterm-lst)))
                (good-typed-term-p
                 (typed-term (car (typed-term-list->term-lst tterm-lst))
                             (typed-term-list->path-cond tterm-lst)
                             (cadr (typed-term-list->judgements tterm-lst)))
                 options)
                (good-typed-term-list-p
                 (typed-term-list (cdr (typed-term-list->term-lst tterm-lst))
                                  (typed-term-list->path-cond tterm-lst)
                                  (caddr (typed-term-list->judgements
                                          tterm-lst)))
                 options)))
  :hints (("Goal" :expand ((good-typed-term-list-p tterm-lst options)
                           (typed-term-list-consp tterm-lst)))))

;; ---------------------------------------------
;;       Destructors for typed-terms
(local (in-theory (disable (:executable-counterpart typed-term)
                           (:executable-counterpart typed-term-list))))

;; ifp destructors
(define typed-term-if->cond ((tterm typed-term-p)
                             (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm options))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options)))
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
   (new-tt (implies
            (and (typed-term-p tterm)
                 (type-options-p options)
                 (equal (typed-term->kind tterm) 'ifp)
                 (good-typed-term-p tterm options))
            (< (acl2-count (typed-term->term new-tt))
               (acl2-count (typed-term->term tterm))))
           :name acl2-count-of-typed-term-if->cond)))

(define typed-term-if->then ((tterm typed-term-p)
                             (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm options))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options)))
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
   (new-tt (implies
            (and (typed-term-p tterm)
                 (type-options-p options)
                 (equal (typed-term->kind tterm) 'ifp)
                 (good-typed-term-p tterm options))
            (< (acl2-count (typed-term->term new-tt))
               (acl2-count (typed-term->term tterm))))
           :name acl2-count-of-typed-term-if->then)))

(define typed-term-if->else ((tterm typed-term-p)
                             (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm options))
  :returns (new-tt (and (typed-term-p new-tt) (good-typed-term-p new-tt options)))
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
   (new-tt (implies
            (and (typed-term-p tterm)
                 (type-options-p options)
                 (equal (typed-term->kind tterm) 'ifp)
                 (good-typed-term-p tterm options))
            (< (acl2-count (typed-term->term new-tt))
               (acl2-count (typed-term->term tterm))))
           :name acl2-count-of-typed-term-if->else)))

(define typed-term->top ((tterm typed-term-p)
                         (options type-options-p))
  :guard (and (or (equal (typed-term->kind tterm) 'ifp)
                  (equal (typed-term->kind tterm) 'lambdap)
                  (equal (typed-term->kind tterm) 'fncallp))
              (good-typed-term-p tterm options))
  :returns (new-tt typed-term-p)
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (or (equal (typed-term->kind tterm) 'ifp)
                              (equal (typed-term->kind tterm) 'lambdap)
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
                (change-typed-term (make-typed-term) :path-cond tt.path-cond))))
    (make-typed-term :term tt.term
                     :path-cond tt.path-cond
                     :judgements top-judge))
  ///
  (more-returns
   (new-tt (implies (and (equal (typed-term->kind tterm)
                                'lambdap)
                         (good-typed-term-p tterm options)
                         (typed-term-p tterm)
                         (type-options-p options))
                    (and (consp (typed-term->term new-tt))
                         (pseudo-lambdap (car (typed-term->term new-tt)))))
           :name implies-of-typed-term->top)
   (new-tt (implies (and (typed-term-p tterm)
                         (type-options-p options)
                         (or (equal (typed-term->kind tterm) 'ifp)
                             (equal (typed-term->kind tterm) 'lambdap)
                             (equal (typed-term->kind tterm) 'fncallp))
                         (good-typed-term-p tterm options))
                    (equal (typed-term->path-cond new-tt)
                           (typed-term->path-cond tterm)))
           :name typed-term->top-maintains-path-cond)))

;; fncallp destructors
(define typed-term-fncall->actuals ((tterm typed-term-p)
                                    (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'fncallp)
              (good-typed-term-p tterm options))
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'fncallp)
                          (good-typed-term-p tterm options))))
        (make-typed-term-list))
       ((typed-term tt) tterm)
       ((cons & actuals) tt.term)
       ((mv err actuals-judgements)
        (case-match tt.judgements
          ((& & actuals-judge . &)
           (mv nil actuals-judge))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-fncall->actuals
            "Malformed fncall judgements ~q0" tt.judgements)))
    (make-typed-term-list :term-lst actuals
                          :path-cond tt.path-cond
                          :judgements actuals-judgements))
  ///
  (more-returns
   (new-ttl (implies (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'fncallp)
                          (good-typed-term-p tterm options))
                     (< (acl2-count
                         (typed-term-list->term-lst new-ttl))
                        (acl2-count (typed-term->term tterm))))
           :name acl2-count-of-make-typed-fncall)))

;; lambdap destructors
(define typed-term-lambda->actuals ((tterm typed-term-p)
                                    (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'lambdap)
              (good-typed-term-p tterm options))
  :guard-hints (("Goal"
                 :expand (good-typed-lambda-p tterm options)))
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'lambdap)
                          (good-typed-term-p tterm options))))
        (make-typed-term-list))
       ((typed-term tt) tterm)
       ((cons & actuals) tt.term)
       ((mv err actuals-judgements)
        (case-match tt.judgements
          ((& & (& & actuals-judge . &) &)
           (mv nil actuals-judge))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-lambda->actuals
            "Malformed lambda judgements ~q0" tt.judgements)))
    (make-typed-term-list :term-lst actuals
                          :path-cond tt.path-cond
                          :judgements actuals-judgements))
  ///
  (more-returns
   (new-ttl (implies (and (typed-term-p tterm)
                          (equal (typed-term->kind tterm)
                                 'lambdap)
                          (good-typed-term-p tterm options))
                     (< (acl2-count
                         (typed-term-list->term-lst new-ttl))
                        (acl2-count (typed-term->term tterm))))
            :name acl2-count-of-typed-term-lambda->actuals)
   (new-ttl (implies (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm)
                                 'lambdap)
                          (good-typed-term-p tterm options))
                     (equal (len (cdr (typed-term->term tterm)))
                            (len (typed-term-list->term-lst new-ttl))))
            :name typed-term-lambda->actuals-preserve-len)))

(define typed-term-lambda->body ((tterm typed-term-p)
                                 (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'lambdap)
              (good-typed-term-p tterm options))
  :guard-hints (("Goal"
                 :expand (good-typed-lambda-p tterm options)))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'lambdap)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((cons fn &) tt.term)
       (formals (lambda-formals fn))
       (body (lambda-body fn))
       (shadowed-path-cond (shadow-path-cond formals tt.path-cond))
       ((mv err body-judgements)
        (case-match tt.judgements
          ((& & (& ((& & body-judge) . &) & &) &)
           (mv nil body-judge))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-lambda->body
            "Malformed lambda judgements ~q0" tt.judgements)))
    (make-typed-term :term body
                     :path-cond shadowed-path-cond
                     :judgements body-judgements))
  ///
  (more-returns
   (new-tt (implies (and (typed-term-p tterm)
                         (type-options-p options)
                         (equal (typed-term->kind tterm)
                                'lambdap)
                         (good-typed-term-p tterm options))
                    (< (acl2-count (typed-term->term new-tt))
                       (acl2-count (typed-term->term tterm))))
           :name acl2-count-of-typed-term-lambda->body)))

;; typed-term-list
(define typed-term-list->car ((tterm-lst typed-term-list-p)
                              (options type-options-p))
  :guard (and (good-typed-term-list-p tterm-lst options)
              (typed-term-list-consp tterm-lst))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options)))
  (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                          (type-options-p options)
                          (good-typed-term-list-p tterm-lst options)
                          (typed-term-list-consp tterm-lst))))
        (make-typed-term))
       ((typed-term-list ttl) tterm-lst)
       ((cons lst-hd &) ttl.term-lst)
       ((mv err judge-hd)
        (case-match ttl.judgements
          ((& judge-hd & &)
           (mv nil judge-hd))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-list->car
            "Malformed fncall judgements ~q0" ttl.judgements)))
    (make-typed-term :term lst-hd
                     :path-cond ttl.path-cond
                     :judgements judge-hd))
  ///
  (more-returns
   (new-tt (implies (and (typed-term-list-p tterm-lst)
                         (type-options-p options)
                         (good-typed-term-list-p tterm-lst options)
                         (typed-term-list-consp tterm-lst))
                    (< (acl2-count (typed-term->term new-tt))
                       (acl2-count (typed-term-list->term-lst tterm-lst))))
           :name acl2-count-of-typed-term-list->car)
   (new-tt (implies (and (typed-term-list-p tterm-lst)
                         (type-options-p options)
                         (good-typed-term-list-p tterm-lst options)
                         (typed-term-list-consp tterm-lst))
                    (equal (typed-term->path-cond new-tt)
                           (typed-term-list->path-cond tterm-lst)))
           :name typed-term-list->car-maintains-path-cond)))

(define typed-term-list->cdr ((tterm-lst typed-term-list-p)
                              (options type-options-p))
  :guard (and (good-typed-term-list-p tterm-lst options)
              (typed-term-list-consp tterm-lst))
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl options)))
  (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                          (type-options-p options)
                          (good-typed-term-list-p tterm-lst options)
                          (typed-term-list-consp tterm-lst))))
        (make-typed-term-list))
       ((typed-term-list ttl) tterm-lst)
       ((cons & lst-tl) ttl.term-lst)
       ((mv err judge-tl)
        (case-match ttl.judgements
          ((& & judge-tl &)
           (mv nil judge-tl))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-list->cdr
            "Malformed fncall judgements ~q0" ttl.judgements)))
    (make-typed-term-list :term-lst lst-tl
                          :path-cond ttl.path-cond
                          :judgements judge-tl))
  ///
  (more-returns
   (new-ttl (implies (and (typed-term-list-p tterm-lst)
                          (type-options-p options)
                          (good-typed-term-list-p tterm-lst options)
                          (typed-term-list-consp tterm-lst))
                     (< (acl2-count (typed-term-list->term-lst new-ttl))
                        (acl2-count (typed-term-list->term-lst tterm-lst))))
            :name acl2-count-of-typed-term-list->cdr)
   (new-ttl (implies (and (typed-term-list-p tterm-lst)
                          (good-typed-term-list-p tterm-lst options)
                          (type-options-p options)
                          (typed-term-list-consp tterm-lst))
                     (equal (len (typed-term-list->term-lst tterm-lst))
                            (+ 1 (len (typed-term-list->term-lst new-ttl)))))
            :name len-of-typed-term-list->cdr)
   (new-ttl (implies (and (typed-term-list-p tterm-lst)
                          (type-options-p options)
                          (good-typed-term-list-p tterm-lst options)
                          (typed-term-list-consp tterm-lst))
                     (equal (typed-term-list->path-cond new-ttl)
                            (typed-term-list->path-cond tterm-lst)))
            :name typed-term-list->cdr-maintains-path-cond)))

;; -----------------------------------------------
;; Theorems for constructors
(defthm implies-of-good-typed-term
  (implies (and (typed-term-p tterm)
                (typed-term-list-p tterm-lst)
                (type-options-p options)
                (good-typed-term-p tterm options)
                (good-typed-term-list-p tterm-lst options)
                (equal (typed-term->path-cond tterm)
                       (typed-term-list->path-cond tterm-lst)))
           (good-typed-term-list-p
            (typed-term-list (cons (typed-term->term tterm)
                                   (typed-term-list->term-lst tterm-lst))
                             (typed-term->path-cond tterm)
                             (list* 'if
                                    (typed-term->judgements tterm)
                                    (typed-term-list->judgements tterm-lst)
                                    '('nil)))
            options))
  :hints (("Goal"
           :expand (good-typed-term-list-p
                    (typed-term-list (cons (typed-term->term tterm)
                                           (typed-term-list->term-lst tterm-lst))
                                     (typed-term->path-cond tterm)
                                     (list* 'if
                                            (typed-term->judgements tterm)
                                            (typed-term-list->judgements tterm-lst)
                                            '('nil)))
                    options))))

;; --------------------------------------------------------------------
;;      Constructors

(defthm kind-of-make-typed-if
  (implies
     (and (typed-term-p tt-top)
          (typed-term-p tt-cond)
          (typed-term-p tt-then)
          (typed-term-p tt-else)
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
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options))
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
         (change-typed-term (make-typed-term) :path-cond ttp.path-cond))))
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
   (new-tt
    (implies (and (type-options-p options)
                  (typed-term-p tt-top)
                  (typed-term-p tt-cond)
                  (typed-term-p tt-then)
                  (typed-term-p tt-else)
                  (good-typed-term-p tt-cond options)
                  (good-typed-term-p tt-then options)
                  (good-typed-term-p tt-else options))
             (equal (typed-term->path-cond new-tt)
                    (typed-term->path-cond tt-top)))
    :name make-typed-if-maintains-path-cond)))

(local
 (defthm pseudo-termp-of-lambda
   (implies (and (symbol-listp formals)
                 (pseudo-termp body-judge)
                 (pseudo-term-listp actuals)
                 (equal (len formals) (len actuals)))
            (pseudo-termp
             `((lambda ,formals ,body-judge) ,@actuals)))
   :hints (("Goal"
            :in-theory (enable pseudo-termp))))
 )

(defthm kind-of-make-typed-lambda
  (implies
     (and (typed-term-p tt-top)
          (typed-term-p tt-body)
          (typed-term-list-p tt-actuals)
          (good-typed-term-p tt-body options)
          (good-typed-term-list-p tt-actuals options)
          (pseudo-lambdap (car (typed-term->term tt-top))))
     (equal (typed-term->kind
             (typed-term
              (typed-term->term tt-top)
              (typed-term->path-cond tt-top)
              (list* 'if
                     (typed-term->judgements tt-top)
                     (list* 'if
                            (cons (list 'lambda
                                        (cadr (car (typed-term->term tt-top)))
                                        (typed-term->judgements tt-body))
                                  (typed-term-list->term-lst tt-actuals))
                            (typed-term-list->judgements tt-actuals)
                            '('nil))
                     '('nil))))
            'lambdap))
  :hints (("Goal"
           :in-theory (enable typed-term->kind))))

(define make-typed-lambda ((tt-top typed-term-p)
                           (tt-body typed-term-p)
                           (tt-actuals typed-term-list-p)
                           (options type-options-p))
  :guard (and (good-typed-term-p tt-body options)
              (good-typed-term-list-p tt-actuals options))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options))
                   :hints (("Goal"
                            :in-theory (enable good-typed-lambda-p))))
  (b* (((unless (mbt (and (type-options-p options)
                          (typed-term-p tt-top)
                          (typed-term-p tt-body)
                          (typed-term-list-p tt-actuals)
                          (good-typed-term-p tt-body options)
                          (good-typed-term-list-p tt-actuals options))))
        (make-typed-term))
       ((typed-term ttt) tt-top)
       ((typed-term ttb) tt-body)
       ((typed-term-list tta) tt-actuals)
       ((unless (and (consp ttt.term)
                     (pseudo-lambdap (car ttt.term))))
        (prog2$ (er hard? 'typed-term=>make-typed-term-lambda
                    "Inconsistent inputs.~%")
                (change-typed-term (make-typed-term)
                                   :path-cond ttt.path-cond)))
       (formals (lambda-formals (car ttt.term)))
       (body (lambda-body (car ttt.term)))
       (actuals (cdr ttt.term))
       ((unless (and (equal tta.term-lst actuals)
                     (equal body ttb.term)
                     (equal (len formals) (len actuals))
                     (equal ttb.path-cond
                            (shadow-path-cond formals ttt.path-cond))
                     (equal ttt.path-cond tta.path-cond)))
        (prog2$ (er hard? 'typed-term=>make-typed-term-lambda
                    "Inconsistent inputs.~%")
                (change-typed-term (make-typed-term)
                                   :path-cond ttt.path-cond))))
    (make-typed-term
     :term ttt.term
     :path-cond ttt.path-cond
     :judgements `(if ,ttt.judgements
                      (if ((lambda ,formals
                             ,ttb.judgements)
                           ,@actuals)
                          ,tta.judgements
                        'nil)
                    'nil)))
  ///
  (more-returns
   (new-tt
    (implies (and (type-options-p options)
                  (typed-term-p tt-top)
                  (typed-term-p tt-body)
                  (typed-term-list-p tt-actuals)
                  (good-typed-term-p tt-body options)
                  (good-typed-term-list-p tt-actuals options))
             (equal (typed-term->path-cond new-tt)
                    (typed-term->path-cond tt-top)))
    :name make-typed-lambda-maintains-path-cond)))

(defthm kind-of-make-typed-fncall
  (implies
     (and (typed-term-p tt-top)
          (typed-term-list-p tt-actuals)
          (good-typed-term-list-p tt-actuals options)
          (consp (typed-term->term tt-top))
          (symbolp (car (typed-term->term tt-top)))
          (not (equal (car (typed-term->term tt-top)) 'quote))
          (not (equal (car (typed-term->term tt-top)) 'if))
          (equal (cdr (typed-term->term tt-top))
                 (typed-term-list->term-lst tt-actuals))
          (equal (typed-term->path-cond tt-top)
                 (typed-term-list->path-cond tt-actuals)))
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

(define make-typed-fncall ((tt-top typed-term-p)
                           (tt-actuals typed-term-list-p)
                           (options type-options-p))
  :guard (good-typed-term-list-p tt-actuals options)
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options))
                   :hints (("Goal"
                            :in-theory (enable good-typed-fncall-p))))
  (b* (((unless (mbt (and (typed-term-p tt-top)
                          (typed-term-list-p tt-actuals)
                          (type-options-p options)
                          (good-typed-term-list-p tt-actuals options))))
        (make-typed-term))
       ((typed-term ttt) tt-top)
       ((typed-term-list tta) tt-actuals)
       ((unless (and (consp ttt.term)
                     (symbolp (car ttt.term))
                     (equal (cdr ttt.term) tta.term-lst)
                     (equal ttt.path-cond tta.path-cond)
                     (not (equal (car (typed-term->term tt-top)) 'quote))
                     (not (equal (car (typed-term->term tt-top)) 'if))))
        (prog2$ (er hard? 'typed-term=>make-typed-fncall
                    "Inconsistent inputs.~%")
                (change-typed-term (make-typed-term)
                                   :path-cond ttt.path-cond))))
    (make-typed-term
     :term ttt.term
     :path-cond ttt.path-cond
     :judgements `(if ,ttt.judgements ,tta.judgements 'nil)))
  ///
  (more-returns
   (new-tt
    (implies (and (typed-term-p tt-top)
                  (typed-term-list-p tt-actuals)
                  (type-options-p options)
                  (good-typed-term-list-p tt-actuals options))
             (equal (typed-term->path-cond new-tt)
                    (typed-term->path-cond tt-top)))
    :name make-typed-fncall-maintains-path-cond)))

(define typed-term-list->cons ((tterm typed-term-p)
                               (tterm-lst typed-term-list-p)
                               (options type-options-p))
  :guard (and (good-typed-term-p tterm options)
              (good-typed-term-list-p tterm-lst options)
              (equal (typed-term->path-cond tterm)
                     (typed-term-list->path-cond tterm-lst)))
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (typed-term-list-p tterm-lst)
                          (type-options-p options)
                          (good-typed-term-p tterm options)
                          (good-typed-term-list-p tterm-lst options))))
        (make-typed-term-list))
       ((typed-term tt) tterm)
       ((typed-term-list ttl) tterm-lst)
       ((unless (equal tt.path-cond ttl.path-cond))
        (prog2$ (er hard? 'typed-term=>typed-term-list->cons
                    "tterm and tterm-lst of cons must have the same path-cond.~%")
                (change-typed-term-list (make-typed-term-list)
                                        :path-cond tt.path-cond))))
    (make-typed-term-list :term-lst `(,tt.term ,@ttl.term-lst)
                          :path-cond tt.path-cond
                          :judgements `(if ,tt.judgements ,ttl.judgements
                                         'nil)))
  ///
  (more-returns
   (new-ttl (implies (and (typed-term-p tterm)
                          (typed-term-list-p tterm-lst)
                          (type-options-p options)
                          (good-typed-term-p tterm options)
                          (good-typed-term-list-p tterm-lst options)
                          (equal (typed-term->path-cond tterm)
                                 (typed-term-list->path-cond tterm-lst)))
                     (equal (typed-term-list->path-cond new-ttl)
                            (typed-term->path-cond tterm)))
            :name typed-term-list->cons-maintains-path-cond))
  (defthm len-of-typed-term-list->cons
    (implies (and (typed-term-p tterm)
                  (typed-term-list-p tterm-lst)
                  (type-options-p options)
                  (good-typed-term-p tterm options)
                  (good-typed-term-list-p tterm-lst options)
                  (equal (typed-term->path-cond tterm)
                         (typed-term-list->path-cond tterm-lst)))
             (equal (len (typed-term-list->term-lst
                          (typed-term-list->cons tterm tterm-lst options)))
                    (+ 1
                       (len (typed-term-list->term-lst tterm-lst)))))))

(define typed-term-list->cdr-induct ((ttl typed-term-list-p)
                                     (options type-options-p))
  :guard (good-typed-term-list-p ttl options)
  :measure (acl2-count (typed-term-list->term-lst ttl))
  :hints (("Goal" :in-theory (enable typed-term-list->cdr
                                     typed-term-list-consp)))
  (if (and (typed-term-list-consp ttl)
           (good-typed-term-list-p ttl options)
           (typed-term-list-p ttl)
           (type-options-p options))
      (typed-term-list->cdr-induct
       (typed-term-list->cdr ttl options) options)
      nil))
