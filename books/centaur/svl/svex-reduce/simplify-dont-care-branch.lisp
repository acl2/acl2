; Copyright (C) 2023 Intel Corporation
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Mertcan Temel <mert.temel@intel.com>

(in-package "SVL")

(include-book "base")

(include-book "integerp-of-svex")
(include-book "svex-reduce-apply")

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/ihs-extensions" :dir :system)
  use-ihs-extensions
  ))

(local
 (rp::fetch-new-events
  (include-book "ihs/logops-lemmas" :dir :system)
  use-ihs-logops-lemmas
  ))

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(define has-care-branch? (svex)
  (case-match svex
    (('sv::?* & & else)
     (or (and* (4vec-p else)
               (not (integerp else)))
         (has-care-branch? else)))
    (('sv::? & & else)
     (or (and* (4vec-p else)
               (not (integerp else)))
         (has-care-branch? else)))))

(progn
  (local
   (defthm svexlist-p-implies-true-listp
     (implies (svexlist-p lst)
              (true-listp lst))))

  (local
   (defthm svexlist-p-of-remove-duplicates-equal
     (implies (svexlist-p x)
              (svexlist-p (remove-duplicates-equal x)))))

  (local
   (defthm svexlist-p-of-union-equal
     (implies (and (svexlist-p x)
                   (svexlist-p y))
              (svexlist-p (union-equal x y))))))

(defsection collect-part-sels-from-tests
  (defines collect-part-sels-from-tests-aux
    :prepwork
    ((defconst *collect-part-sels-from-tests-aux-limit*
       20))
    (define collect-part-sels-from-tests-aux ((x sv::Svex-p)
                                              (limit natp))
      :verify-guards nil
      :measure (acl2::nat-list-measure (list limit 0))
      :Returns (mv (collected sv::svexlist-p :hyp (sv::svex-p x))
                   valid)
      (if (zp limit)
          (mv nil nil)
        (sv::svex-case
         x
         :var (mv nil nil)
         :quote (mv nil t)
         :call
         (cond ((and (equal x.fn 'sv::partsel)
                     (equal-len x.args 3)
                     (atom (third x.args)) ;; only collect variables
                     )
                (mv (list x) (and (natp (first x.args))
                                  (natp (second x.args))
                                  (< (second x.args) 9))))
               (t (collect-part-sels-from-tests-aux-lst x.args (1- limit)))))))
    (define collect-part-sels-from-tests-aux-lst ((lst sv::svexlist-p)
                                                  (limit natp))
      :measure (acl2::nat-list-measure (list limit (len lst)))
      :Returns (mv (collected sv::svexlist-p :hyp (sv::svexlist-p lst))
                   valid)
      (if (zp limit)
          (mv nil nil)
        (if (atom lst)
            (mv nil t)
          (b* (((mv c1 v1) (collect-part-sels-from-tests-aux (car lst) (1- limit)))
               ((Unless v1) (mv nil nil))
               ((mv c2 v2) (collect-part-sels-from-tests-aux-lst (cdr lst) limit))
               ((Unless v2) (mv nil nil)))
            (mv (union-equal c1 c2) t)))))
    ///

    (verify-guards collect-part-sels-from-tests-aux))

  (define collect-part-sels-from-tests ((x sv::Svex-p))
    :returns (mv (collected sv::svexlist-p
                            :hyp (sv::svex-p x)
                            :hints (("Goal"
                                     :in-theory (e/d (svex-p) ()))))
                 valid)
    :verify-guards nil
    (case-match x
      (('sv::?* test & else)
       (b* (((mv c1 v1)
             (collect-part-sels-from-tests-aux test
                                               *collect-part-sels-from-tests-aux-limit*))
            ((unless v1) (mv nil nil))
            ((mv c2 v2)
             (collect-part-sels-from-tests else ))
            ((unless v2) (mv nil nil)))
         (mv (union-equal c1 c2) t)))
      (('sv::? test & else)
       (b* (((mv c1 v1)
             (collect-part-sels-from-tests-aux test
                                               *collect-part-sels-from-tests-aux-limit*))
            ((unless v1) (mv nil nil))
            ((mv c2 v2)
             (collect-part-sels-from-tests else ))
            ((unless v2) (mv nil nil)))
         (mv (union-equal c1 c2) t)))
      (& (mv nil t)))
    ///
    (verify-guards collect-part-sels-from-tests
      :hints (("Goal"
               :in-theory (e/d (svex-p)
                               ()))))))

;; (define simplify-dont-care-branch-simulate-aux
;;   )

;; (defines simplify-dont-care-branch-simulate
;;   (define simplify-dont-care-branch-simulate ((x1 svex-p)
;;                                               (x2 svex-p)
;;                                               (collected)
;;                                               (bindings))
;;    :Returns (mv res valid)
;;    (cond ((atom collected)
;;           (simplify-dont-care-branch-simulate-aux x1 x2 bindings))
;;          (t (b* ((c (car collected))
;;                  ((mv size size-valid)
;;                   (case-match c (('sv::partsel & size &) (mv size (natp size))) (& (mv 0 nil))))
;;                  ((unless size-valid)
;;                   (mv 0 nil)))
;;               (simplify-dont-care-branch-simulate-iter x1 x2 (cdr collected) bindings
;;                                                        (car collected)
;;                                                        (expt 2 size))))))
;; (define simplify-dont-care-branch-simulate-iter ((x1 svex-p)
;;                                                  (x2 svex-p)
;;                                                  (collected)
;;                                                  (bindings)
;;                                                  (cur-term)
;;                                                  (cnt))
;;   (if (zp cnt)

(svex-eval-lemma-tmpl
 (defthm svex-eval-of-cons-fn-args
   (Implies (and (svex-p x)
                 (equal (svex-kind x) :call))
            (equal (svex-eval (cons (svex-call->fn x)
                                    args)
                              env)
                   (svex-apply (svex-call->fn x)
                               (svexlist-eval args ENV))))
   :hints (("Goal"
            :expand ((SVEX-P X))
            :in-theory (e/d (SVEX-EVAL
                             svex-p
                             svex-call->fn
                             SVEX-CALL->ARGS
                             svex-kind)
                            ())))))

(defines simplify-dont-care-branch-apply
  (define simplify-dont-care-branch-apply ((x svex-p)
                                           partsel-term
                                           new-val)
    :measure (sv::svex-count x)
    :returns (res svex-p :hyp (and (svex-p x)
                                   (svex-p new-val)))
    (sv::svex-case
     x
     :var x
     :quote x
     :call
     (if (equal x partsel-term)
         new-val
       (b* ((args (simplify-dont-care-branch-apply-lst x.args partsel-term new-val))
            ;;((unless (sv::4veclist-p args)) x)
            )
         (svex-reduce-w/-env-apply x.fn args)))))
  (define simplify-dont-care-branch-apply-lst ((lst svexlist-p)
                                               partsel-term new-val)
    :measure (sv::svexlist-count lst)
    :returns (res svexlist-p :hyp (and (svexlist-p lst)
                                       (svex-p new-val)))
    (if (atom lst)
        nil
      ;; no need to hons
      (cons (simplify-dont-care-branch-apply (car lst)
                                             partsel-term new-val)
            (simplify-dont-care-branch-apply-lst (cdr lst)
                                                 partsel-term new-val))))
  ///
  (svex-eval-lemma-tmpl
   (defret-mutual correctness
     (defret svex-eval-of-<fn>-is-correct
       (implies (and (svex-p x)
                     (equal (svex-eval partsel-term env)
                            (svex-eval new-val env)))
                (equal (svex-eval res env)
                       (svex-eval x env)))
       :fn simplify-dont-care-branch-apply)
     (defret svex-eval-of-<fn>-is-correct
       (implies (and (svexlist-p lst)
                     (equal (svex-eval partsel-term env)
                            (svex-eval new-val env)))
                (equal (svexlist-eval res env)
                       (svexlist-eval lst env)))
       :fn simplify-dont-care-branch-apply-lst))))

(memoize 'simplify-dont-care-branch-apply)

(define simplify-dont-care-branch-cancel-test ((x sv::Svex-p)
                                               (partsel-term)
                                               (cnt natp))
  (if (zp cnt)
      t
    (b* ((res (simplify-dont-care-branch-apply x partsel-term (1- cnt)))
         ((unless (implies (4vec-p res)
                           (integerp res)))
          nil))
      (simplify-dont-care-branch-cancel-test x partsel-term (1- cnt)))))

(define simplify-dont-care-branch-count-cases (collected)
  (if (atom collected)
      1
    (b* ((c (car collected))
         (size (case-match c (('sv::partsel & size &) (if (natp size) size 100)) (& 100))))
      (* (expt 2 size)
         (simplify-dont-care-branch-count-cases (cdr collected))))))

(define simplify-dont-care-branch-build-other (x)
  :returns (res svex-p :hyp (svex-p x)
                :hints (("Goal"
                         :in-theory (e/d (svex-p) ()))))
  (case-match x
    (('sv::?* test then else)
     (if (4vec-p else)
         then
       (svex-reduce-w/-env-apply
        'sv::?*
        (Hons-list test then
                   (simplify-dont-care-branch-build-other else)))))
    (('sv::? test then else)
     (if (4vec-p else)
         then
       (svex-reduce-w/-env-apply
        'sv::?
        (hons-list test then
                   (simplify-dont-care-branch-build-other else)))))
    (& x)))

(define simplify-dont-care-branch-cosimulate ((x svex-p)
                                              (y svex-p)
                                              (partsel-term)
                                              (cnt natp))
  :returns equals
  (if (zp cnt)
      t
    (b* ((cnt (1- cnt))
         (resx (simplify-dont-care-branch-apply x partsel-term cnt))
         (resy (simplify-dont-care-branch-apply y partsel-term cnt))
         ((unless (equal resx resy))
          nil))
      (simplify-dont-care-branch-cosimulate x y partsel-term cnt)))
  ///

  (local
   (svex-eval-lemma-tmpl
    (defthm svex-eval-when-natp
      (implies (natp x)
               (equal (svex-eval x env)
                      x))
      :hints (("Goal"
               :in-theory (e/d (svex-eval
                                svex-kind
                                4vec-p
                                sv::svex-quote->val)
                               ()))))))
  (svex-eval-lemma-tmpl
   (defret svex-eval-of-<fn>-is-correct
     (implies (and equals
                   (natp cnt)
                   (force (natp (svex-eval partsel-term env)))
                   (force (< (svex-eval partsel-term env)
                             cnt))
                   (svex-p x)
                   (svex-p y))
              (equal (svex-eval y env)
                     (svex-eval x env)))
     :hints (("Goal"
              :in-theory (e/d () (svex-eval-of-simplify-dont-care-branch-apply-is-correct)))
             (and stable-under-simplificationp
                  '(:use ((:instance svex-eval-of-simplify-dont-care-branch-apply-is-correct
                                     (new-val (+ -1 CNT)))
                          (:instance svex-eval-of-simplify-dont-care-branch-apply-is-correct
                                     (x y)
                                     (new-val (+ -1 CNT))))))))))

(local
 (defthm natp-of-4vec-part-select
   (implies (and (natp start)
                 (natp size)
                 (integerp x))
            (natp (4vec-part-select start size x)))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal"
            :in-theory (e/d (4vec-part-select
                             SV::4VEC->UPPER
                             sv::4vec->lower
                             4VEC-RSH
                             4VEC-ZERO-EXT
                             4VEC-SHIFT-CORE
                             4VEC)
                            ())))))

(local
 (defthm upperbound-of-4vec-part-select
   (implies (and (natp start)
                 (natp size)
                 (integerp x))
            (< (4vec-part-select start size x)
               (expt 2 size)))
   :rule-classes (:rewrite :linear)
   :hints (("Goal"
            :in-theory (e/d (4vec-part-select
                             SV::4VEC->UPPER
                             sv::4vec->lower
                             4VEC-RSH
                             4VEC-ZERO-EXT
                             4VEC-SHIFT-CORE
                             4VEC)
                            ())))))

(define simplify-dont-care-branch ((x svex-p)
                                   &key
                                   ((env) 'env)
                                   ((context rp::rp-term-listp) 'context)
                                   ((config svex-reduce-config-p) 'config))

  :returns (res svex-p :hyp (svex-p x))
  :prepwork ((local
              (in-theory (disable ash))))
  (b* (((unless (has-care-branch? x))
        x)
       ((mv collected valid)
        (collect-part-sels-from-tests x))
       ((unless valid)
        x)
       ((unless (equal-len collected 1))
        ;; TODO: for now, I  will only allow one item in  collected to make the
        ;; proofs go through more easily. !!!
        x)
       ((when (> (simplify-dont-care-branch-count-cases collected)
                 512))
        x)

       ;;(- (cw "simplify-dont-care-branch: Collected: ~p0 ~%" collected))

       (partsel-term (car collected))
       ((mv size ?inner-term size-valid)
        (case-match partsel-term (('sv::partsel start size inner-term)
                                  (mv size inner-term (and (natp start)
                                                           (natp size))))
          (& (mv 0 0 nil))))
       ((unless size-valid)
        x)
       ((Unless (integerp-of-svex partsel-term))
        x)
       ((unless (simplify-dont-care-branch-cancel-test x partsel-term (ash 1 size)))
        x)
       (x-simplified (simplify-dont-care-branch-build-other x))
       (equals (simplify-dont-care-branch-cosimulate x x-simplified
                                                     partsel-term
                                                     (ash 1 size))))
    (if equals
        x-simplified
      x))
  ///

  (local
   (in-theory (disable SV::SVEX-APPLY$-IS-SVEX-APPLY)))

  (local
   (svex-eval-lemma-tmpl
    (defthm svex-eval-of-partsel-pattern
      (implies (case-match x (('partsel & & &) t))
               (equal (svex-eval x env)
                      (4vec-part-select (svex-eval (first (cdr x)) env)
                                        (svex-eval (second (cdr x)) env)
                                        (svex-eval (third (cdr x)) env))))
      :hints (("Goal"
               :in-theory (e/d (svex-apply
                                svex-eval svex-kind
                                sv::svex-call->args
                                sv::svex-call->fn)
                               ()))))))

  (local
   (svex-eval-lemma-tmpl
    (defthm svex-eval-when-natp
      (implies (natp x)
               (equal (svex-eval x env)
                      x))
      :hints (("Goal"
               :in-theory (e/d (svex-eval
                                svex-kind
                                4vec-p
                                sv::svex-quote->val)
                               ()))))))

  (local
   (defthm integerp-of-svex-of-partsel-pattern
     (implies (case-match x (('partsel & & &) t))
              (equal (integerp-of-svex x)
                     (and (integerp-of-svex (third (cdr x)))
                          (natp (first (cdr x)))
                          (natp (second (cdr x))))))
     :hints (("Goal"
              :expand (integerp-of-svex x)
              :in-theory (e/d (EQUAL-LEN SVEX-KIND) ())))))

  (local
   (defthm svex-p-of-partsel-pattern
     (implies (and (svex-p x)
                   (case-match x (('partsel & & &) t)))
              (and (svex-p (third (cdr x)))
                   (svex-p (first (cdr x)))
                   (svex-p (second (cdr x)))))
     :hints (("Goal"
              :in-theory (e/d (svex-p EQUAL-LEN SVEX-KIND) ())))))

  (local
   (defthm integerp-of-expt
     (implies (natp x)
              (integerp (expt 2 x)))
     :hints (("Goal"
              :in-theory (e/d (ACL2::|(integerp (expt x n))|) ())))))

  (svex-eval-lemma-tmpl
   (defret SVEX-EVAL-of-<fn>-is-correct
     (implies (and
               (sub-alistp env big-env)
               (rp::rp-term-listp context)
               (rp::valid-sc env-term a)
               (rp::eval-and-all context a)
               (rp::falist-consistent-aux big-env env-term)
               (svex-p x)
               (:@ :dollar-eval
                   (integerp-of-svex-extn-correct<$>-lst
                    (svex-reduce-config->integerp-extns config)))
               (:@ :normal-eval
                   (equal (svex-reduce-config->integerp-extns config) nil))
               (or* (svex-reduce-config->keep-missing-env-vars config)
                    (equal big-env env)))
              (equal (svex-eval res (rp-evlt env-term a))
                     (svex-eval x   (rp-evlt env-term a))))
     :hints (("Goal"
              :use ((:instance svex-eval-of-simplify-dont-care-branch-cosimulate-is-correct
                               (x x)
                               (y (simplify-dont-care-branch-build-other x))
                               (partsel-term (car (mv-nth 0 (collect-part-sels-from-tests x))))
                               (cnt (expt 2
                                          (caddr (car (mv-nth 0 (collect-part-sels-from-tests x))))))
                               (env (rp-evlt env-term a))))
              :in-theory (e/d () (acl2::|(integerp (expt x n))|
                                        natp
                                        svex-eval-of-simplify-dont-care-branch-cosimulate-is-correct
                                        rp::falist-consistent-aux
                                        rp::ex-from-rp
                                        rp::eval-and-all
                                        rp::rp-term-listp
                                        rp-trans
                                        rp::valid-sc
                                        rp::valid-sc-subterms)))))))


;; (simplify-dont-care-branch
;;  '(SV::?*
;;    (SV::==?? (SV::CONCAT 1 0 (SV::PARTSEL 0 2 A))
;;              4)
;;    0
;;    (SV::?*
;;     (SV::==?? (SV::CONCAT 1 0 (SV::PARTSEL 0 2 A))
;;               6)
;;     1
;;     (SV::?* (SV::==?? (SV::CONCAT 1 0 (SV::PARTSEL 0 2 A))
;;                       0)
;;             0
;;             (SV::?* (SV::==?? (SV::CONCAT 1 0 (SV::PARTSEL 0 2 A))
;;                               2)
;;                     1 (1 . 0)))))
;;  :env (make-fast-alist `((a . a)))
;;  :context '((Integerp a)))


;; (svl::simplify-dont-care-branch
;;  '(SV::?*
;;    (SV::BITOR (SV::==?? (SV::PARTSEL 13 3 A) 4)
;;               (SV::BITOR (SV::==?? (SV::PARTSEL 13 3 A) 5)
;;                          (SV::==?? (SV::PARTSEL 13 3 A) 6)))
;;    1
;;    (SV::?*
;;     (SV::BITOR
;;      (SV::==?? (SV::PARTSEL 13 3 A) 7)
;;      (SV::BITOR (SV::==?? (SV::PARTSEL 13 3 A) 0)
;;                 (SV::BITOR (SV::==?? (SV::PARTSEL 13 3 A) 1)
;;                            (SV::BITOR (SV::==?? (SV::PARTSEL 13 3 A) 2)
;;                                       (SV::==?? (SV::PARTSEL 13 3 A) 3)))))
;;     0 (1 . 0)))
;;  :env (make-fast-alist `((a . a)))
;;  :context '((Integerp a)))
