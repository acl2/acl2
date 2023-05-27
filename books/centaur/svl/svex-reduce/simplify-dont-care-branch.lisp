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
 (include-book "../4vec-lemmas"))

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
       128))
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

  ;; No need to verify anything about this...
  (define collect-part-sels-from-tests-merge-aux ((start natp)
                                                  (size natp)
                                                  var
                                                  collected)

    :prepwork ((Local
                (defthm 4vec-p-of-natp
                  (implies (natp x) (sv::4vec-p x)))))
    :returns (mv (new-collected sv::svexlist-p
                                :hyp (and (sv::svexlist-p collected)
                                          (natp size)
                                          (natp start))
                                :hints (("Goal"
                                         :in-theory (e/d (sv::svex-p) ()))))
                 (merged))
    (if (atom collected)
        (mv nil nil)
      (b* ((other (car collected))
           ((mv ovar ostart osize valid)
            (case-match other
              (('sv::partsel ostart osize ovar)
               (mv ovar ostart osize (and (natp ostart)
                                          (natp osize))))
              (& (mv 0 0 0 nil))))
           ((unless valid)
            ;; should never happen!!
            (progn$
             (cw "Something unexpected happened in ~p0~%" acl2::__function__)
             (mv collected nil)))
           ((unless (equal var ovar))
            (b* (((mv rest merged)
                  (collect-part-sels-from-tests-merge-aux
                   start size var (cdr collected))))
              (if merged
                  (mv (cons (car collected) rest) t)
                (mv collected nil))))
           (end (+ start size ))
           (oend (+ ostart osize ))
           ;; case1 osize merges on the lower end.
           ((when (and (<= ostart start)
                       (>= oend start)
                       (<= oend end)))
            (mv (cons (hons-list 'sv::partsel ostart (+ end (- ostart)) var)
                      (cdr collected))
                t))
           ;; case2 osize merges on the upper end.
           ((when (and (<= start ostart)
                       (>= end ostart)
                       (<= end oend)))
            (mv (cons (hons-list 'sv::partsel start (+ oend (- start)) var)
                      (cdr collected))
                t))
           ;; case3 osize falls within
           ((when (and (<= start ostart)
                       (>= end oend)))
            (mv (cons (hons-list 'sv::partsel start size var)
                      (cdr collected))
                t))
           ;; case4 size falls within
           ((when (and (<= ostart start)
                       (>= oend end)))
            (mv (cons (hons-list 'sv::partsel ostart osize var)
                      (cdr collected))
                t))
           ((mv rest merged)
            (collect-part-sels-from-tests-merge-aux
             start size var (cdr collected))))
        (if merged
            (mv (cons (car collected) rest) t)
          (mv collected nil))))
    ///
    (defret len-of-<fn>
      (<= (len new-collected)
          (len collected))
      :hints (("Goal"
               :in-theory (e/d (cons-count) ())))))

  (define collect-part-sels-from-tests-merge (collected)
    :measure (len collected)
    :returns (new-collected sv::svexlist-p
                            :hyp (sv::svexlist-p collected))
    :hints (("Goal"
             :in-theory (e/d () (len))))
    :prepwork ((local
                (defthm len-measure-lemma
                  (implies
                   (and (consp collected)
                        (<= (len x) (len (cdr collected))))
                   (< (len x) (len collected))))))
    (if (atom collected)
        nil
      (b* ((cur (car collected))
           ((mv var start size valid)
            (case-match cur
              (('sv::partsel start size var)
               (mv var start size (and (natp start)
                                       (natp size))))
              (& (mv 0 0 0 nil))))
           ((Unless valid) ;; should never come here!!!!
            (progn$ (cw "Something unexpected happened in ~p0~%" acl2::__function__)
                    collected))
           ((mv new-collected merged)
            (collect-part-sels-from-tests-merge-aux start size var (cdr collected)))
           ((when merged)
            (collect-part-sels-from-tests-merge new-collected)))
        (cons-with-hint cur
                        (collect-part-sels-from-tests-merge (cdr collected))
                        collected))))

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
            ((unless v2) (mv nil nil))
            (res (union-equal c1 c2))
            (res (collect-part-sels-from-tests-merge res)))
         (mv res t)))
      (('sv::? test & else)
       (b* (((mv c1 v1)
             (collect-part-sels-from-tests-aux test
                                               *collect-part-sels-from-tests-aux-limit*))
            ((unless v1) (mv nil nil))
            ((mv c2 v2)
             (collect-part-sels-from-tests else ))
            ((unless v2) (mv nil nil))
            (res (union-equal c1 c2))
            (res (collect-part-sels-from-tests-merge res)))
         (mv res t)))
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

(define simplify-dont-care-branch-apply-aux (svex
                                             partsel-term
                                             (new-val natp))
  :returns (mv (res-val sv::svex-p :hyp (natp new-val))
               changed)
  :prepwork ((local
              (defthm svex-p-of-4vec-p
                (implies (sv::4vec-p x)
                         (sv::svex-p x))
                :hints (("Goal"
                         :in-theory (e/d (sv::svex-p 4vec-p svex-kind)
                                         ())))))
             (Local
              (defthm 4vec-p-of-natp
                (implies (natp x) (sv::4vec-p x)))))
  (case-match svex
    (('partsel start size var)
     (b* (((unless (and (natp start)
                        (natp size)))
           (mv 0 nil))
          ((mv start2 size2 var2 valid)
           (case-match partsel-term
             (('partsel start size var)
              (mv start size var (and (natp start)
                                      (natp size))))
             (&
              (mv 0 0 0 nil))))
          ((unless (and (equal var var2)
                        valid))
           (mv 0 nil))
          (end (+ start size))
          (end2 (+ start2 size2))
          ;; svex should fall within partsel-term
          ((unless (and (<= start2 start)
                        (<= end end2)))
           (mv 0 nil))
          (new-start (- start start2)))
       (mv (sv::4vec-part-select new-start size new-val)
           t)))
    (&
     (mv 0 nil)))
  ///

  (local
   (use-ihs-extensions t))

  (local
   (use-ihs-logops-lemmas t))

  (local
   (use-arithmetic-5 t))

  (local
   (defthm dummy-cancel-lemma
     (implies (and (EQUAL (+ x y)
                          (+ a b))
                   (acl2-numberp y))
              (equal (+ a (- x) b)
                     y))))

  (local
   (in-theory (disable SV::SVEX-APPLY$-IS-SVEX-APPLY)))

  (local
   (svex-eval-lemma-tmpl
    (defthm svex-eval-of-4vec-p
      (implies (4vec-p x)
               (equal (sv::svex-eval x env)
                      x))
      :hints (("Goal"
               :in-theory (e/d (sv::svex-eval
                                svex-kind
                                4vec-p
                                sv::svex-quote->val)
                               ()))))))

  (svex-eval-lemma-tmpl
   (defret svex-eval-of-<fn>-is-correct
     (implies (and (equal (svex-eval partsel-term env)
                          new-val)
                   changed
                   (natp new-val))
              (and (equal res-val
                          (svex-eval svex env))
                   (equal ;; to prevent free-vars
                    (svex-eval res-val env)
                    (svex-eval svex env))
                   ))
     :hints (("Goal"
              :do-not-induct t
              :expand ((SVEX-EVAL PARTSEL-TERM ENV)
                       (NTH 2 (CDR SVEX))
                       (NTH 1 (CDR SVEX))
                       (NTH 1 (CDDR SVEX))
                       (NTH 0 (CDR SVEX))
                       (NTH 2 (CDR PARTSEL-TERM))
                       (NTH 1 (CDR PARTSEL-TERM))
                       (NTH 0 (CDddR PARTSEL-TERM)))
              :in-theory (e/d* (SVEX-CALL->FN
                                SVEX-APPLY
                                SVEXLIST-EVAL
                                4VEC
                                4VECLIST-NTH-SAFE
                                SVEX-CALL->ARGS
                                SV::SVEX-QUOTE->VAL
                                SVEX-KIND
                                ;;bitops::ihsext-inductions
                                ;;bitops::ihsext-recursive-redefs
                                4VEC-ZERO-EXT
                                4VEC-SHIFT-CORE
                                4VEC-RSH
                                ACL2::DEFAULT-MINUS
                                SV::4VEC->UPPER
                                SV::4VEC->lower
                                ;;4VEC-PART-SELECT
                                ACL2::|(- (- x))|)
                               (;;4VEC-PART-SELECT-OF-4VEC-PART-SELECT-2
                                )))))))

(defines simplify-dont-care-branch-apply
  (define simplify-dont-care-branch-apply ((x svex-p)
					   &key
                                           (partsel-term 'partsel-term)
                                           ((new-val natp) 'new-val)
					   ((under-test-arg booleanp) 'under-test-arg))
    :measure (sv::svex-count x)
    :returns (res svex-p :hyp (and (svex-p x)
                                   (natp new-val)))
    (sv::svex-case
     x
     :var x
     :quote x
     :call
     ;; TODO:  Maybe try  to apply  partsel  terms only  for test  cases if  it
     ;; becomes too slow..
     (b* (((when (and* (not under-test-arg)
		       (or (equal x.fn 'sv::?*)
			   (equal x.fn 'sv::?))
		       (equal-len x.args 3)))
           (b* ((test (simplify-dont-care-branch-apply (first x.args) :under-test-arg t))
                ((when (equal test -1))
                 (second x.args))
                ((when (equal test 0))
                 (simplify-dont-care-branch-apply (third x.args))))
             x)
	   #|(svex-reduce-w/-env-apply x.fn
				     (cons (simplify-dont-care-branch-apply (first x.args) :under-test-arg t)
	   (simplify-dont-care-branch-apply-lst (cdr x.args))))|#
           )
	  ((unless under-test-arg) x)		   
	  ((mv val changed)
           (simplify-dont-care-branch-apply-aux x partsel-term new-val))
          ((when changed) val)
          (args (simplify-dont-care-branch-apply-lst x.args)))
       (svex-reduce-w/-env-apply x.fn args))))
  (define simplify-dont-care-branch-apply-lst ((lst svexlist-p)
                                                &key
						(partsel-term 'partsel-term)
						((new-val natp) 'new-val)
						((under-test-arg booleanp) 'under-test-arg))
    :measure (sv::svexlist-count lst)
    :returns (res svexlist-p :hyp (and (svexlist-p lst)
                                       (natp new-val)))
    (if (atom lst)
        nil
      ;; no need to hons
      (cons (simplify-dont-care-branch-apply (car lst))
            (simplify-dont-care-branch-apply-lst (cdr lst)))))
  ///
  (local
   (in-theory (disable sv::svex-apply$-is-svex-apply)))
  (svex-eval-lemma-tmpl
   (defret-mutual correctness
     (defret svex-eval-of-<fn>-is-correct
       (implies (and (svex-p x)
                     (natp new-val)
                     (equal (svex-eval partsel-term env)
                            new-val))
                (equal (svex-eval res env)
                       (svex-eval x env)))
       :fn simplify-dont-care-branch-apply)
     (defret svex-eval-of-<fn>-is-correct
       (implies (and (svexlist-p lst)
                     (natp new-val)
                     (equal (svex-eval partsel-term env)
                            new-val))
                (equal (svexlist-eval res env)
                       (svexlist-eval lst env)))
       :fn simplify-dont-care-branch-apply-lst)
     :hints (("Goal"
              :expand ((SVEXLIST-EVAL (CDR X) ENV)
                       (SVEXLIST-EVAL (CdDR X) ENV)
                       (SVEXLIST-EVAL (CddDR X) ENV)
                       (:free (x y)
                              (svex-apply x (cons -1 y)))
                       (:free (x y)
                              (svex-apply x (cons 0 y)))
                       (:free (x y env)
                              (svex-eval (cons x y) env))
                       (:free (x y)
                              (svex-kind (cons x y))))
              :in-theory (e/d (SVEX-CALL->FN
                               SVEX-CALL->ARGS)
                              ()))))))

(memoize 'simplify-dont-care-branch-apply)

(define simplify-dont-care-branch-cancel-test ((x sv::Svex-p)
                                               (partsel-term)
                                               (cnt natp))
  (if (zp cnt)
      t
    (b* ((res (simplify-dont-care-branch-apply x
                                               :new-val (1- cnt)
                                               :under-test-arg nil))
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
         (new-val cnt)
         (under-test-arg nil)
         (resx (simplify-dont-care-branch-apply x))
         (resy (simplify-dont-care-branch-apply y))
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
                                     (new-val (+ -1 CNT))
                                     (UNDER-TEST-ARG nil))
                          (:instance svex-eval-of-simplify-dont-care-branch-apply-is-correct
                                     (x y)
                                     (UNDER-TEST-ARG nil)
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
                            (4VEC-ZERO-EXT-IS-4VEC-CONCAT))))))

;; memoizing saves some time.
(memoize 'collect-part-sels-from-tests)

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
