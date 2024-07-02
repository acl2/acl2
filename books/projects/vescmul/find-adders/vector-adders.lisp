; Multiplier verification

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

(in-package "RP")

(include-book "../fnc-defs")
(include-book "centaur/svl/top" :dir :system)
(include-book "centaur/sv/svex/lists" :dir :system)

(include-book "heuristics")
(include-book "adder-patterns")
(include-book "quick-search")
(include-book "macros")
(include-book "misc")

(local
 (include-book "centaur/bitops/ihs-extensions" :dir :system))

(local
 (include-book "ihs/logops-lemmas" :dir :system))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/equal-by-logbitp" :dir :system)
  use-equal-by-logbitp
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (defthm svexlist-p-of-remove-duplicates
   (implies (sv::Svexlist-p x)
            (sv::Svexlist-p (remove-duplicates-equal x)))))

(local
 (in-theory (disable acl2::merge-sort-lexorder
                     acl2::merge-lexorder)))

(local
 (in-theory (e/d (acl2::maybe-integerp
                  sv::svex-kind)
                 ((:e tau-system)))))

(local
 (defthm sv::svexlist-eval$-when-consp
   (implies (consp lst)
            (equal (sv::svexlist-eval$ lst env)
                   (cons (sv::svex-eval$ (car lst) env)
                         (sv::svexlist-eval$ (cdr lst) env))))))




;; part of ppfx-simplify
(define create-fa-c-chain-instance (arg1 arg2 arg3)
  :inline t
  :returns (res sv::svex-p :hyp (and (sv::svex-p arg1)
                                     (sv::svex-p arg2)
                                     (sv::svex-p arg3))
                :hints (("Goal"
                         :in-theory (e/d (ACL2::MERGE-SORT-LEXORDER
                                          ACL2::MERGE-LEXORDER)
                                         ()))))
  (b* (((list arg1 arg2 arg3)
        (acl2::merge-sort-lexorder (list arg1 arg2 arg3))))
    (hons-list 'fa-c-chain 0 arg1 arg2 arg3))
  ///
  (defret <fn>-correct
    (implies (warrants-for-adder-pattern-match)
             (equal (sv::svex-eval$ res env)
                    (fa-c-chain 0
                                (sv::svex-eval$ arg1 env)
                                (sv::svex-eval$ arg2 env)
                                (sv::svex-eval$ arg3 env))))
    :hints (("Goal"
             :in-theory (e/d (fa-c-chain
                              sv::svex-call->args
                              sv::svex-call->fn
                              sv::svex-apply$
                              acl2::merge-lexorder
                              acl2::merge-sort-lexorder)
                             ())))))


(local
 ;; some more lemmas first.
 (defsection 4vec-lemmas

   (defthm 4vec-concat$-to-logapp
     (implies (and (natp size)
                   (integerp x)
                   (integerp y))
              (equal (svl::4vec-concat$ size x y)
                     (logapp size x y)))
     :hints (("goal"
              :in-theory (e/d (svl::4vec-concat$
                               svl::logapp-to-4vec-concat)
                              ()))))

   (defthm sv::4vec-bitops-to-logops
     (and (implies (and (integerp x)
                        (integerp y))
                   (and (equal (sv::4vec-bitxor x y)
                               (logxor x y))
                        (equal (sv::4vec-bitand x y)
                               (logand x y))
                        (equal (sv::4vec-bitor x y)
                               (logior x y))))
          (implies (integerp x)
                   (equal (sv::4vec-bitnot x)
                          (lognot x))))
     :hints (("goal"
              :do-not-induct t
              :in-theory (e/d* (sv::4vec
                                sv::4vec-bitand
                                sv::3vec-bitand
                                sv::3vec-bitor
                                sv::4vec-bitor
                                sv::3vec-bitnot
                                sv::4vec-bitnot
                                bitops::ihsext-inductions
                                bitops::ihsext-recursive-redefs
                                sv::4vec-bitxor
                                sv::4vec->lower
                                sv::4vec->upper
                                sv::4vec-rsh
                                sv::4vec-shift-core
                                svl::bits
                                sv::4vec-part-select
                                sv::4vec-concat)
                               (floor
                                svl::equal-of-4vec-concat-with-size=1
                                logand)))))

   (defthm sv::svexlist-eval$-when-consp
     (implies (consp lst)
              (equal (sv::svexlist-eval$ lst env)
                     (cons (sv::svex-eval$ (car lst) env)
                           (sv::svexlist-eval$ (cdr lst) env)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Vector adders.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Simplification for carry select adder

(define csel-branch (svex)
  :returns (mv (test sv::Svex-p :hyp (sv::Svex-p svex))
               (then sv::Svex-p :hyp (sv::Svex-p svex))
               (else sv::Svex-p :hyp (sv::Svex-p svex))
               valid)
  (case-match svex
    (('sv::bitor ('sv::bitand b ('sv::Bitxor 1 y))
                 ('sv::bitand a y))
     (mv y a b t))
    (('sv::bitor ('sv::bitand a y)
                 ('sv::bitand b ('sv::Bitxor 1 y)))
     (mv y a b t))
    (('sv::? test a b)
     (mv test a b t))
    (& (mv 0 0 0 nil)))
  ///
  (defret <fn>-is-correct
    (implies (and valid
                  (bitp (sv::svex-eval$ test env))
                  (bitp (sv::svex-eval$ then env))
                  (bitp (sv::svex-eval$ else env)))
             (and (implies (case-split
                            (equal (sv::svex-eval$ test env) 1))
                           (equal (sv::svex-eval$ then env)
                                  (sv::svex-eval$ svex env)))
                  (implies (not (equal (sv::svex-eval$ test env) 1))
                           (equal (sv::svex-eval$ else env)
                                  (sv::svex-eval$ svex env)))))
    :hints (("Goal"
             :in-theory (e/d (SV::SVEX-APPLY
                              SV::SVEX-CALL->FN
                              SV::SVEX-CALL->args)
                             ())))))



(local
 (defthm subsetp-equal-of-intersection-equal
   (and (subsetp-equal (intersection-equal x y)
                       x)
        (subsetp-equal (intersection-equal x y)
                       y))))

(local
 (defthm fa-c-chain-reorder
   (and (equal (fa-c-chain 0 y x z)
               (fa-c-chain 0 x y z))
        (equal (fa-c-chain 0 x z y)
               (fa-c-chain 0 x y z)))
   :hints (("Goal"
            :in-theory (e/d (fa-c-chain) ())))))

(local
 (defthm fa-s-chain-reorder
   (and (equal (fa-s-chain y x z)
               (fa-s-chain x y z))
        (equal (fa-s-chain x z y)
               (fa-s-chain x y z)))
   :hints (("Goal"
            :in-theory (e/d (fa-s-chain) ())))))


(define get-two-common-one-diff (lst1 lst2)
  :returns (mv (c1 sv::svex-p :hyp (sv::svexlist-p lst1))
               (c2 sv::svex-p :hyp (sv::svexlist-p lst1))
               (o1 sv::svex-p :hyp (sv::svexlist-p lst1))
               (o2 sv::svex-p :hyp (sv::svexlist-p lst2))
               valid)
  (b* (((unless (and* (svl::equal-len lst1 3)
                      (svl::equal-len lst2 3)))
        (mv 0 0 0 0 nil))
       ((unless (and* (no-duplicatesp-equal lst1)
                      (no-duplicatesp-equal lst2)))
        (mv 0 0 0 0 nil))
       (inter (intersection-equal lst1 lst2))
       ((unless (svl::equal-len inter 2))
        (mv 0 0 0 0 nil))
       (t0 (set-difference-equal lst1 inter))
       (e0 (set-difference-equal lst2 inter))
       ((unless (and* (svl::equal-len t0 1)
                      (svl::equal-len e0 1)))
        (mv 0 0 0 0 nil)))
    (mv (first inter)
        (second inter)
        (car t0)
        (car e0)
        t))
  ///
  (local
   (in-theory (e/d ()
                   (;;member-equal
                    ;;intersection-equal
                    acl2::member-equal-newvar-components-2
                    acl2::true-list-listp-implies-true-listp-xxx
                    true-list-listp
                    true-listp
                    ;;svexlist-p-implies-true-listp
                    acl2::true-listp-of-car-when-true-list-listp
                    acl2::true-list-listp-of-cons
                    cdr-of-x-is-svexlist-p-when-kind-is-svex-fn-call
                    sv::svexlist-p-of-cdr-when-svexlist-p
                    (:rewrite sv::svex-p-of-car-when-svexlist-p)
                    (:rewrite
                     sv::svexlist-p-of-car-when-svexlistlist-p)
                    (:rewrite
                     sv::svexlistlist-p-of-cdr-when-svexlistlist-p)
                    acl2::member-equal-newvar-components-1
                    acl2::loop$-as
                    default-car
                    acl2::cdr-loop$-as-tuple
                    acl2::car-loop$-as-tuple
                    set-difference-equal
                    (:type-prescription member-equal)
                    (:definition acl2::empty-loop$-as-tuplep)
                    acl2::member-equal-newvar-components-3
                    (:type-prescription acl2::loop$-as)
                    (:definition sv::svex-kind$inline)
                    default-cdr))))

  (defret measure-lemma
    (implies valid
             (and (< (cons-count c1)
                     (cons-count lst1))
                  (< (cons-count c2)
                     (cons-count lst1))
                  (< (cons-count o1)
                     (cons-count lst1))
                  (< (cons-count c1)
                     (cons-count lst2))
                  (< (cons-count c2)
                     (cons-count lst2))
                  (< (cons-count o2)
                     (cons-count lst2))))
    :rule-classes (:linear :rewrite)
    :hints (("goal"
             :expand ((:free (x) (set-difference-equal (cdr lst2) x))
                      (:free (x) (set-difference-equal (cddr lst2) x))
                      (:free (x) (set-difference-equal lst2 x))
                      (:free (x) (set-difference-equal (cdr lst1) x))
                      (:free (x) (set-difference-equal (cddr lst1) x))
                      (:free (x) (set-difference-equal lst1 x))
                      (intersection-equal lst1 lst2)
                      (intersection-equal (cdr lst1) lst2))
             :in-theory (e/d (svl::equal-len
                              intersection-equal
                              cons-count)
                             ()))))

  (defret <fn>-is-correct
    (implies (and valid
                  ;;(bitp (sv::svex-eval$ c1 env))
                  ;;(bitp (sv::svex-eval$ c2 env))
                  )
             (and
              (equal (fa-c-chain 0
                                 (sv::svex-eval$ c1 env)
                                 (sv::svex-eval$ c2 env)
                                 (sv::svex-eval$ o1 env))
                     (fa-c-chain 0
                                 (sv::svex-eval$ (first lst1) env)
                                 (sv::svex-eval$ (second lst1) env)
                                 (sv::svex-eval$ (third lst1) env)))
              (equal (fa-s-chain (sv::svex-eval$ c1 env)
                                 (sv::svex-eval$ c2 env)
                                 (sv::svex-eval$ o1 env))
                     (fa-s-chain (sv::svex-eval$ (first lst1) env)
                                 (sv::svex-eval$ (second lst1) env)
                                 (sv::svex-eval$ (third lst1) env)))
              (equal (fa-c-chain 0
                                 (sv::svex-eval$ c1 env)
                                 (sv::svex-eval$ c2 env)
                                 (sv::svex-eval$ o2 env))
                     (fa-c-chain 0
                                 (sv::svex-eval$ (first lst2) env)
                                 (sv::svex-eval$ (second lst2) env)
                                 (sv::svex-eval$ (third lst2) env)))
              (equal (fa-s-chain (sv::svex-eval$ c1 env)
                                 (sv::svex-eval$ c2 env)
                                 (sv::svex-eval$ o2 env))
                     (fa-s-chain (sv::svex-eval$ (first lst2) env)
                                 (sv::svex-eval$ (second lst2) env)
                                 (sv::svex-eval$ (third lst2) env)))))
    :hints (("goal"
             :expand ((svl::equal-len (cddr lst1) 1)
                      (svl::equal-len (cdr lst1) 2)
                      (svl::equal-len lst1 3)
                      (svl::equal-len (cddr lst2) 1)
                      (svl::equal-len (cdr lst2) 2)
                      (svl::equal-len lst2 3)
                      (:free (then else)
                             (intersection-equal (cdr then) (cdr else)))
                      (member-equal (cadr lst1) lst2)
                      (member-equal (caddr lst1) lst2)
                      (member-equal (car lst1) lst2)
                      (member-equal (cadr lst1) (cdr lst2))
                      (member-equal (caddr lst1) (cdr lst2))
                      (member-equal (car lst1) (cdr lst2))
                      (member-equal (cadr lst1) (cddr lst2))
                      (member-equal (caddr lst1) (cddr lst2))
                      (member-equal (car lst1) (cddr lst2))
                      (member-equal (cadr lst1) (cdddr lst2))
                      (member-equal (caddr lst1) (cdddr lst2))
                      (member-equal (car lst1) (cdddr lst2))
                      (:free (x)
                             (set-difference-equal lst2 x))
                      (:free (x)
                             (set-difference-equal (cdr lst2) x))
                      (:free (x)
                             (set-difference-equal (cddr lst2) x))
                      (:free (x)
                             (set-difference-equal lst1 x))
                      (:free (x)
                             (set-difference-equal nil x))
                      (:free (x)
                             (set-difference-equal (cdr lst1) x))
                      (:free (x)
                             (set-difference-equal (cddr lst1) x))
                      )
             :in-theory (e/d (and*
                              bitp
                              ;;set-difference-equal
                              svl::equal-len
                              )
                             ())))))




(with-output
  :off :all
  :on (error summary)
  :gag-mode :goals
  (define csel-simplify-end-at-bitand ((test sv::svex-p)
                                       (then sv::Svex-p)
                                       (else sv::svex-p)
                                       &key

                                       ((env) 'env)
                                       ((context rp-term-listp) 'context)
                                       ((config svl::svex-reduce-config-p) 'config))
    :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                (sv::svex-p then)
                                                (sv::svex-p else)))
                 valid)

    (cond
     ((and* (bitand-pattern-p else)
            (bitor-pattern-p then))
      (b* (((list e1 e2) (cdr else))
           ((list t1 t2) (cdr then))
           ((unless (or (and* (equal e1 t1) (equal e2 t2))
                        (and* (equal e1 t2) (equal e2 t1))))
            (mv 0 nil))
           ((unless (and* (svl::bitp-of-svex e1)
                          (svl::bitp-of-svex e2)
                          (svl::bitp-of-svex test)))
            (progn$ (or (svl::bitp-of-svex e1)
                        (cwe "bitp failing on e1: ~p0~%" e1)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e1)
                             (svl::width-of-svex e1)))
                    (or (svl::bitp-of-svex e2)
                        (cwe "bitp failing on e2 ~p0~%" e2)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e2)
                             (svl::width-of-svex e2)))
                    (or (svl::bitp-of-svex test)
                        (cwe "bitp failing on test: ~p0~%" test)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex test)
                             (svl::width-of-svex test)))
                    (raise "Bitp check failed at last step~%")
                    (mv 0 nil)))
           (new-args (hons-list 0 test e1 e2)))
        (mv (sv::svex-call 'fa-c-chain new-args)
            t)))
     (t (mv 0 nil)))))

(with-output
  :off :all
  :on (error summary)
  :gag-mode :goals
  (define csel-simplify-end-at-bitxor ((test sv::svex-p)
                                       (then sv::Svex-p)
                                       (else sv::svex-p)
                                       &key
                                       ((env) 'env)
                                       ((context rp-term-listp) 'context)
                                       ((config svl::svex-reduce-config-p) 'config))
    :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                (sv::svex-p then)
                                                (sv::svex-p else)))
                 valid)
    (cond
     ((and* (bitxor-pattern-p else)
            (or (ha+1-s-chain-pattern-2-p then)
                (ha+1-s-chain-pattern-3-p then)))
      (b* (((list e1 e2) (cdr else))
           ((mv t1 t2) (cond ((ha+1-s-chain-pattern-2-p then)
                              (ha+1-s-chain-pattern-2-body
                               then
                               (b* (((mv t1 t2 &) (look-for-ha+1-s-chain-pattern-aux x y z)))
                                 (mv t1 t2))))
                             (t
                              (ha+1-s-chain-pattern-3-body
                               then
                               (b* (((mv t1 t2 &) (look-for-ha+1-s-chain-pattern-aux x y z)))
                                 (mv t1 t2))))))
           ((unless (or (and* (equal e1 t1) (equal e2 t2))
                        (and* (equal e1 t2) (equal e2 t1))))
            (mv 0 nil))
           ((unless (and* (svl::bitp-of-svex e1) ;; maybe remove
                          (svl::bitp-of-svex e2) ;; maybe remove
                          (svl::bitp-of-svex test)))
            (progn$ (or (svl::bitp-of-svex e1)
                        (cwe "bitp failing on e1: ~p0~%" e1)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e1)
                             (svl::width-of-svex e1)))
                    (or (svl::bitp-of-svex e2)
                        (cwe "bitp failing on e2 ~p0~%" e2)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e2)
                             (svl::width-of-svex e2)))
                    (or (svl::bitp-of-svex test)
                        (cwe "bitp failing on test: ~p0~%" test)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex test)
                             (svl::width-of-svex test)))
                    (raise "Bitp check failed at last step~%")
                    (mv 0 nil)))
           (new-args (hons-list test e1 e2)))
        (mv (sv::svex-call 'fa-s-chain new-args)
            t)))
     (t (mv 0 nil)))))




(with-output :off :all
  :on (error summary)
  :gag-mode :goals
  (define csel-simplify-end-at-special-bitxor ((test sv::svex-p)
                                               (then sv::Svex-p)
                                               (else sv::svex-p)
                                               &key
                                               ((env) 'env)
                                               ((context rp-term-listp) 'context)
                                               ((config svl::svex-reduce-config-p) 'config))
    :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                (sv::svex-p then)
                                                (sv::svex-p else)))
                 valid)
    (cond
     ((and* (fa-s-chain-itself-pattern-p then)
            (bitxor-pattern-p else))
      (b* (((list e1 e2) (cdr else))
           ((list t1 t2 t3) (cdr then))
           ((mv o1 valid)
            (cond ((equal e1 t1)
                   (cond ((equal e2 t2)
                          (mv t3 t))
                         ((equal e2 t3)
                          (mv t2 t))
                         (t (mv 0 nil))))
                  ((equal e1 t2)
                   (cond ((equal e2 t1)
                          (mv t3 t))
                         ((equal e2 t3)
                          (mv t1 t))
                         (t (mv 0 nil))))
                  ((equal e1 t3)
                   (cond ((equal e2 t1)
                          (mv t2 t))
                         ((equal e2 t2)
                          (mv t1 t))
                         (t (mv 0 nil))))
                  (t (mv 0 nil))))
           ((Unless valid)
            (mv 0 nil))

           ((unless (and* ;;(svl::bitp-of-svex then) ;; redundant but helps the proofs
                     ;;(svl::bitp-of-svex else) ;; redundant but helps the proofs
                     (svl::bitp-of-svex e1)
                     (svl::bitp-of-svex e2)
                     (svl::bitp-of-svex o1)
                     (svl::bitp-of-svex test)))
            (progn$ (or (svl::bitp-of-svex e1)
                        (cwe "bitp failing on e1: ~p0~%" e1)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e1)
                             (svl::width-of-svex e1)))
                    (or (svl::bitp-of-svex e2)
                        (cwe "bitp failing on e2: ~p0~%" e2)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e2)
                             (svl::width-of-svex e2)))
                    (or (svl::bitp-of-svex o1)
                        (cwe "bitp failing on o1: ~p0~%" o1)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex o1)
                             (svl::width-of-svex o1)))
                    (or (svl::bitp-of-svex test)
                        (cwe "bitp failing on test: ~p0~%" test)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex test)
                             (svl::width-of-svex test)))
                    (raise "Bitp check failed at last step~%")
                    (mv 0 nil)))
           (new-inner-arg (hons-list 'sv::bitand test o1))
           (new-args (hons-list new-inner-arg e1 e2)))
        (mv (sv::svex-call 'fa-s-chain new-args)
            t)))
     (t (mv 0 nil)))))




(with-output :off :all
  :on (error summary)
  :gag-mode :goals
  (define csel-simplify-end-at-special-bitand ((test sv::svex-p)
                                               (then sv::Svex-p)
                                               (else sv::svex-p)
                                               &key
                                               ((env) 'env)
                                               ((context rp-term-listp) 'context)
                                               ((config svl::svex-reduce-config-p) 'config))
    :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                (sv::svex-p then)
                                                (sv::svex-p else)))
                 valid)
    (cond
     ((and* (fa-c-chain-itself-pattern-p then)
            (bitand-pattern-p else))
      (b* (((list m t1 t2 t3) (cdr then))
           ((list e1 e2) (cdr else))
           ((Unless (valid-fa-c-chain-args-p m t1))
            (mv 0 nil))
           ((mv o1 valid)
            (cond ((equal e1 t1)
                   (cond ((equal e2 t2)
                          (mv t3 t))
                         ((equal e2 t3)
                          (mv t2 t))
                         (t (mv 0 nil))))
                  ((equal e1 t2)
                   (cond ((equal e2 t1)
                          (mv t3 t))
                         ((equal e2 t3)
                          (mv t1 t))
                         (t (mv 0 nil))))
                  ((equal e1 t3)
                   (cond ((equal e2 t1)
                          (mv t2 t))
                         ((equal e2 t2)
                          (mv t1 t))
                         (t (mv 0 nil))))
                  (t (mv 0 nil))))
           ((Unless valid)
            (mv 0 nil))

           ((unless (and* ;;(svl::bitp-of-svex then) ;; redundant but helps the proofs
                     ;;(svl::bitp-of-svex else) ;; redundant but helps the proofs
                     (svl::bitp-of-svex e1)
                     (svl::bitp-of-svex e2)
                     (svl::bitp-of-svex o1)
                     (svl::bitp-of-svex test)))
            (progn$ (or (svl::bitp-of-svex e1)
                        (cwe "bitp failing on e1: ~p0~%" e1)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e1)
                             (svl::width-of-svex e1)))
                    (or (svl::bitp-of-svex e2)
                        (cwe "bitp failing on e2: ~p0~%" e2)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e2)
                             (svl::width-of-svex e2)))
                    (or (svl::bitp-of-svex o1)
                        (cwe "bitp failing on o1: ~p0~%" o1)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex o1)
                             (svl::width-of-svex o1)))
                    (or (svl::bitp-of-svex test)
                        (cwe "bitp failing on test: ~p0~%" test)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex test)
                             (svl::width-of-svex test)))
                    (raise "Bitp check failed at last step~%")
                    (mv 0 nil)))
           (new-inner-arg (hons-list 'sv::bitand test o1))
           (new-args (hons-list 0 new-inner-arg e1 e2)))
        (mv (sv::svex-call 'fa-c-chain new-args)
            t)))
     (t (mv 0 nil)))))




(with-output
  :off :all
  :on (summary error)
  :gag-mode :goals
  (defines csel-simplify
    ;; splitting into multiple functions to reduce casepslits and speed up proofs
    (define csel-simplify-fa-c ((test sv::svex-p)
                                (then sv::Svex-p)
                                (else sv::svex-p)
                                &key
                                ((limit natp) '(1- limit))
                                ((env) 'env)
                                ((context rp-term-listp) 'context)
                                ((config svl::svex-reduce-config-p) 'config))
      :measure (nfix limit)
      :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                  (sv::svex-p then)
                                                  (sv::svex-p else)))
                   valid)
      :verify-guards nil

      (cond ((zp limit)
             (mv 0 nil))
            ((and* (fa-c-chain-itself-pattern-p then)
                   (fa-c-chain-itself-pattern-p else))
             (b* (((unless (and* (valid-fa-c-chain-args-p (first (cdr then))
                                                          (second (cdr then)))
                                 (valid-fa-c-chain-args-p (first (cdr else))
                                                          (second (cdr else)))))
                   (mv 0 nil))

                  ((mv c1 c2 o1 o2 valid)
                   (get-two-common-one-diff (cddr then)
                                            (cddr else)))
                  ((unless valid)
                   (mv 0 nil))
                  ((mv rest-svex valid)
                   (csel-simplify test o1 o2))
                  ((unless valid)
                   (mv 0 nil))
                  ((unless (and* (svl::bit-listp-of-svex (cddr then))
                                 (svl::bit-listp-of-svex (cddr else))))
                   (progn$ (raise "Bitp check failed under fa-c-chain-pattern-p~%")
                           (mv 0 nil)))
                  (new-args (hons-list 0 rest-svex c1 c2)))
               (mv (sv::svex-call 'fa-c-chain new-args)
                   t)))
            (t (mv 0 nil))))

    (define csel-simplify-fa-s ((test sv::svex-p)
                                (then sv::Svex-p)
                                (else sv::svex-p)
                                &key
                                ((limit natp) '(1- limit))
                                ((env) 'env)
                                ((context rp-term-listp) 'context)
                                ((config svl::svex-reduce-config-p) 'config))

      :measure (nfix limit)
      :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                  (sv::svex-p then)
                                                  (sv::svex-p else)))
                   valid)

      (cond ((zp limit)
             (mv 0 nil))
            ((and* (or (fa-s-chain-itself-pattern-p then)
                       (fa-s-chain-pattern-1-p then)
                       (fa-s-chain-pattern-2-p then))
                   (or (fa-s-chain-itself-pattern-p else)
                       (fa-s-chain-pattern-1-p else)
                       (fa-s-chain-pattern-2-p else)))
             (b* ((then-args (cond ((fa-s-chain-itself-pattern-p then)
                                    (cdr then))
                                   ((fa-s-chain-pattern-1-p then)
                                    (fa-s-chain-pattern-1-body then
                                                               (list x y z)))
                                   ((fa-s-chain-pattern-2-p then)
                                    (fa-s-chain-pattern-2-body then
                                                               (list x y z)))))
                  (else-args (cond ((fa-s-chain-itself-pattern-p else)
                                    (cdr else))
                                   ((fa-s-chain-pattern-1-p else)
                                    (fa-s-chain-pattern-1-body else
                                                               (list x y z)))
                                   ((fa-s-chain-pattern-2-p else)
                                    (fa-s-chain-pattern-2-body else
                                                               (list x y z)))))

                  ((mv c1 c2 o1 o2 valid)
                   (get-two-common-one-diff then-args
                                            else-args))
                  ((unless valid)
                   (mv 0 nil))
                  ((mv rest-svex valid)
                   (csel-simplify test o1 o2))
                  ((unless valid)
                   (mv 0 nil))
                  ((unless (and* (svl::bit-listp-of-svex then-args)
                                 (svl::bit-listp-of-svex else-args)))
                   (progn$ (raise "Bitp check failed under fa-s-chain-pattern-p~%")
                           (mv 0 nil)))
                  (new-args (hons-list rest-svex c1 c2)))
               (mv (sv::svex-call 'fa-s-chain new-args)
                   t)))
            (t (mv 0 nil))))

    (define csel-simplify-ha-s ((test sv::svex-p)
                                (then sv::Svex-p)
                                (else sv::svex-p)
                                &key
                                ((limit natp) '(1- limit))
                                ((env) 'env)
                                ((context rp-term-listp) 'context)
                                ((config svl::svex-reduce-config-p) 'config))

      :measure (nfix limit)
      :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                  (sv::svex-p then)
                                                  (sv::svex-p else)))
                   valid)

      (cond ((zp limit)
             (mv 0 nil))
            ((and* (bitxor-pattern-p then)
                   (bitxor-pattern-p else))
             (b* (((list t1 t2) (cdr then))
                  ((list e1 e2) (cdr else))
                  ((mv c eo to valid)
                   (cond ((equal e1 t1)
                          (mv e1 e2 t2 t))
                         ((equal e1 t2)
                          (mv e1 e2 t1 t))
                         ((equal e2 t1)
                          (mv e2 e1 t2 t))
                         ((equal e2 t2)
                          (mv e2 e1 t1 t))
                         (t (mv 0 0 0 nil))))
                  ((unless valid) (mv 0 nil))
                  ((mv rest-svex valid)
                   (csel-simplify test to eo))
                  ((unless valid) (mv 0 nil))
                  ((unless (and* (svl::bit-listp-of-svex (cdr then))
                                 (svl::bit-listp-of-svex (cdr else))))
                   (progn$ (raise "Bitp check failed under bitxor-pattern-p~%")
                           (mv 0 nil)))
                  (new-args (hons-list rest-svex c)))
               (mv (sv::svex-call 'sv::bitxor new-args)
                   t)))
            (t (mv 0 nil))))

    (define csel-simplify-ha-c ((test sv::svex-p)
                                (then sv::Svex-p)
                                (else sv::svex-p)
                                &key
                                ((limit natp) '(1- limit))
                                ((env) 'env)
                                ((context rp-term-listp) 'context)
                                ((config svl::svex-reduce-config-p) 'config))

      :measure (nfix limit)
      :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                  (sv::svex-p then)
                                                  (sv::svex-p else)))
                   valid)

      (cond ((zp limit)
             (mv 0 nil))
            ((and* (bitand-pattern-p then)
                   (bitand-pattern-p else))
             (b* (((list t1 t2) (cdr then))
                  ((list e1 e2) (cdr else))
                  ((mv c eo to valid)
                   (cond ((equal e1 t1)
                          (mv e1 e2 t2 t))
                         ((equal e1 t2)
                          (mv e1 e2 t1 t))
                         ((equal e2 t1)
                          (mv e2 e1 t2 t))
                         ((equal e2 t2)
                          (mv e2 e1 t1 t))
                         (t (mv 0 0 0 nil))))
                  ((unless valid) (mv 0 nil))
                  ((mv rest-svex valid)
                   (csel-simplify test to eo))
                  ((unless valid) (mv 0 nil))
                  ((unless (and* (svl::bit-listp-of-svex (cdr then))
                                 (svl::bit-listp-of-svex (cdr else))))
                   (progn$ (raise "Bitp check failed under bitxor-pattern-p~%")
                           (mv 0 nil)))
                  (new-args (hons-list rest-svex c)))
               (mv (sv::svex-call 'sv::bitand new-args)
                   t)))
            (t (mv 0 nil))))

    (define csel-simplify ((test sv::svex-p)
                           (then sv::Svex-p)
                           (else sv::svex-p)
                           &key
                           ((limit natp) '(1- limit))
                           ((env) 'env)
                           ((context rp-term-listp) 'context)
                           ((config svl::svex-reduce-config-p) 'config))

      :measure (nfix limit)
      :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                  (sv::svex-p then)
                                                  (sv::svex-p else)))
                   valid)
      :verify-guards nil

      (cond ((zp limit)
             (mv 0 nil))
            (t (b* (((mv new-svex valid) (csel-simplify-fa-c test then else))
                    ((when valid) (mv new-svex valid))

                    ((mv new-svex valid) (csel-simplify-fa-s test then else))
                    ((when valid)(mv new-svex valid))

                    ((mv new-svex valid) (csel-simplify-ha-s test then else))
                    ((when valid)(mv new-svex valid))

                    ((mv new-svex valid) (csel-simplify-ha-c test then else))
                    ((when valid)(mv new-svex valid))

                    ((mv new-svex valid) (csel-simplify-end-at-bitand test then else))
                    ((when valid) (mv new-svex valid))

                    ((mv new-svex valid) (csel-simplify-end-at-bitxor test then else))
                    ((when valid) (mv new-svex valid))

                    ((mv new-svex valid) (csel-simplify-end-at-special-bitxor test then else))
                    ((when valid) (mv new-svex valid))

                    ((mv new-svex valid) (csel-simplify-end-at-special-bitand test then else))
                    ((when valid) (mv new-svex valid))
                    )
                 (mv 0 nil)))))
    ///

    (local
     (defthm dummy-lemma
       (implies (and (sv::svex-p then)
                     (or (fa-c-chain-itself-pattern-p then)
                         (fa-s-chain-itself-pattern-p then)
                         (bitxor-PATTERN-P then)
                         (bitand-PATTERN-P then)))
                (SV::SVEXLIST-P (CDR THEN)))
       :hints (("Goal"
                :in-theory (e/d (sv::svex-p
                                 sv::Svex-kind
                                 sv::svex-call->args
                                 sv::svex-call->fn)
                                ())))))

    (local
     (defthm svexlist-p-of-cdr
       (implies (sv::Svexlist-p lst)
                (sv::Svexlist-p (cdr lst)))))

    (verify-guards csel-simplify-fn
      :hints (("Goal"
               :do-not-induct t
               :in-theory (e/d (sv::svex-p-of-car-when-svexlist-p)
                               (valid-fa-c-chain-args-p)))))

    #|(local
    (defthmd bitp-of-svex-eval$-casesplit-trigger ;
    (implies (and (sv::svex-p svex) ;
    (rp::rp-term-listp context) ;
    (rp::valid-sc env-term a) ;
    (rp::eval-and-all context a) ;
    (rp::falist-consistent-aux env env-term) ;
    (svl::width-of-svex-extn-correct$-lst ;
    (svl::svex-reduce-config->width-extns config)) ;
    (svl::integerp-of-svex-extn-correct$-lst ;
    (svl::svex-reduce-config->integerp-extns config))) ;
    (equal (svl::bitp-of-svex svex) ;
    (and (hide (svl::bitp-of-svex svex)) ;
    (bitp (sv::Svex-eval$ svex (rp-evlt env-term a)))))) ;
    :hints (("Goal" ;
    :expand (hide (svl::bitp-of-svex svex )) ;
    :in-theory (e/d () ())))))|#

    (local
     (defthm dummy-svex-lemma
       (implies (and (sv::svex-p x)
                     (FA-C-CHAIN-ITSELF-PATTERN-P x))
                (and (SV::SVEX-P (CAR (CDDDDR x)))
                     (SV::SVEX-P (CAR (CDDDR x)))
                     (SV::SVEX-P (CAR (CDDR x)))
                     (SV::SVEX-P (CAR (CDR x)))))
       :hints (("Goal"
                :expand ((sv::svex-p x))
                :in-theory (e/d (sv::svex-p) ())))))

    (local
     (defthm c-spec-of-1-when-bitp
       (implies (and (bitp x)
                     (bitp y))
                (and (equal (c-spec (list 1 x y))
                            (logior x y))
                     (equal (c-spec (list 0 x y))
                            (logand x y))))
       :hints (("Goal"
                :in-theory (e/d (bitp) ())))))

    (local
     (defthm fa-c-chain-when-valid-args
       (implies (and (valid-fa-c-chain-args-p m x)
                     (bitp (SV::SVEX-EVAL$ x env))
                     (bitp (SV::SVEX-EVAL$ y env))
                     (bitp (SV::SVEX-EVAL$ z env)))
                (equal (FA-C-CHAIN (SV::SVEX-EVAL$ m env)
                                   (SV::SVEX-EVAL$ x env)
                                   (SV::SVEX-EVAL$ y env)
                                   (SV::SVEX-EVAL$ z env))
                       (FA-C-CHAIN 0
                                   (SV::SVEX-EVAL$ x env)
                                   (SV::SVEX-EVAL$ y env)
                                   (SV::SVEX-EVAL$ z env))))
       :hints (("Goal"
                :in-theory (e/d (bitp
                                 SV::SVEX-QUOTE->VAL
                                 fa-c-chain)
                                ())))))

    (local
     (defthm bitp-of-logior/and/c-spec
       (implies (and (bitp x)
                     (bitp y))
                (and (bitp (logior x y))
                     (bitp (logxor x y))
                     (bitp (logand x y))
                     (implies (bitp z)
                              (bitp (c-spec (list x y z))))
                     (implies (bitp z)
                              (bitp (s-spec (list x y z))))))
       :hints (("Goal"
                :in-theory (e/d (bitp) ())))))

    (defret <fn>-is-correct-bitp
      (implies (and valid
                    (sv::Svex-p test)
                    (sv::Svex-p then)
                    (sv::Svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-bitand
      :hints (("Goal"
               :in-theory (e/d (csel-simplify-end-at-bitand
                                SVL::BIT-LISTP-OF-SVEX-FN
                                SV::SVEX-APPLY
                                SV::SVEX-APPLY$
                                SV::SVEX-CALL->FN SV::SVEX-CALL->args
                                SVL::BIT-LISTP-OF-SVEX
                                )
                               (valid-fa-c-chain-args-p
                                ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP
                                SYMBOL-LISTP
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$-LST
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))

    (defret <fn>-is-correct-bitp
      (implies (and valid
                    (sv::Svex-p test)
                    (sv::Svex-p then)
                    (sv::Svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-bitxor
      :hints (("Goal"
               :in-theory (e/d (ha+1-s-chain-pattern-2-p
                                csel-simplify-end-at-bitxor
                                SVL::BIT-LISTP-OF-SVEX-FN
                                SV::SVEX-APPLY
                                SV::SVEX-APPLY$
                                SV::SVEX-CALL->FN SV::SVEX-CALL->args
                                SVL::BIT-LISTP-OF-SVEX
                                )
                               (valid-fa-c-chain-args-p
                                ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP
                                SYMBOL-LISTP
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$-LST
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))

    (defret <fn>-is-correct-bitp
      (implies (and valid
                    (sv::Svex-p test)
                    (sv::Svex-p then)
                    (sv::Svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-special-bitxor
      :hints (("Goal"
               :in-theory (e/d (csel-simplify-end-at-special-bitxor
                                svl::bit-listp-of-svex-fn
                                sv::svex-apply
                                sv::svex-apply$
                                sv::svex-call->fn sv::svex-call->args
                                svl::bit-listp-of-svex
                                )
                               (valid-fa-c-chain-args-p
                                acl2::symbolp-of-car-when-symbol-listp
                                symbol-listp
                                svl::width-of-svex-extn-correct$-lst
                                svl::width-of-svex-extn-correct$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))

    (defret <fn>-is-correct-bitp
      (implies (and valid
                    (sv::Svex-p test)
                    (sv::Svex-p then)
                    (sv::Svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-special-bitand
      :hints (("Goal"
               :in-theory (e/d (csel-simplify-end-at-special-bitand
                                svl::bit-listp-of-svex-fn
                                sv::svex-apply
                                sv::svex-apply$
                                sv::svex-call->fn sv::svex-call->args
                                svl::bit-listp-of-svex
                                )
                               (valid-fa-c-chain-args-p
                                acl2::symbolp-of-car-when-symbol-listp
                                symbol-listp
                                svl::width-of-svex-extn-correct$-lst
                                svl::width-of-svex-extn-correct$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))

    (defret-mutual implies-args-are-bitp
      (defret <fn>-is-correct-bitp
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-fa-c)
      (defret <fn>-is-correct-bitp
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-fa-s)
      (defret <fn>-is-correct-bitp
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-ha-s)
      (defret <fn>-is-correct-bitp
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-ha-c)
      (defret <fn>-is-correct-bitp
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify)
      :hints (("Goal"
               :expand ((csel-simplify-fa-c test then else
                                            :limit limit)
                        (csel-simplify-fa-s test then else
                                            :limit limit)
                        (csel-simplify-ha-s test then else
                                            :limit limit)
                        (csel-simplify-ha-c test then else
                                            :limit limit)
                        (csel-simplify test then else
                                       :limit limit))
               :do-not-induct t
               :in-theory (e/d (;;bitp
                                SVL::BIT-LISTP-OF-SVEX-FN
                                SV::SVEX-APPLY
                                SV::SVEX-APPLY$
                                SV::SVEX-CALL->FN SV::SVEX-CALL->args
                                SVL::BIT-LISTP-OF-SVEX
                                ;;bitp-of-svex-eval$-casesplit-trigger
                                ;;bitp
                                )
                               (;;WARRANTS-FOR-ADDER-PATTERN-MATCH
                                valid-fa-c-chain-args-p
                                ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP
                                SYMBOL-LISTP
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$-LST
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))

    (local
     (defthm s-spec-to-logxor
       (implies (and (bitp x)
                     (bitp y)
                     (bitp z))
                (equal (s-spec (list x y z))
                       (logxor x y z)))
       :hints (("Goal"
                :in-theory (e/d (bitp) ())))))

    (local
     (defthm 4vec-fncs-to-logops-when-bitp
       (implies (and (bitp x)
                     (bitp y))
                (and (equal (sv::4vec-bitxor x y) (logxor x y))
                     (equal (sv::4vec-bitor x y) (logior x y))
                     (equal (sv::4vec-bitand x y) (logand x y))))
       :hints (("Goal"
                :in-theory (e/d () (bitp))))))

    (defret <fn>-is-correct
      (implies (and valid
                    (sv::svex-p test)
                    (sv::svex-p then)
                    (sv::svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                      (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                          (sv::svex-eval$ then (rp-evlt env-term a))
                        (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-bitxor
      :hints (("goal"
               :in-theory (e/d (HA+1-S-CHAIN-PATTERN-2-P
                                csel-simplify-end-at-bitxor
                                svl::bit-listp-of-svex-fn
                                sv::svex-apply
                                sv::svex-apply$
                                sv::svex-call->fn sv::svex-call->args
                                svl::bit-listp-of-svex)
                               (valid-fa-c-chain-args-p
                                acl2::symbolp-of-car-when-symbol-listp
                                symbol-listp
                                svl::width-of-svex-extn-correct$-lst
                                svl::width-of-svex-extn-correct$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))

    (defret <fn>-is-correct
      (implies (and valid
                    (sv::svex-p test)
                    (sv::svex-p then)
                    (sv::svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                      (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                          (sv::svex-eval$ then (rp-evlt env-term a))
                        (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-bitand
      :hints (("goal"
               :in-theory (e/d (csel-simplify-end-at-bitand
                                svl::bit-listp-of-svex-fn
                                sv::svex-apply
                                sv::svex-apply$
                                sv::svex-call->fn sv::svex-call->args
                                svl::bit-listp-of-svex)
                               (valid-fa-c-chain-args-p
                                acl2::symbolp-of-car-when-symbol-listp
                                symbol-listp
                                svl::width-of-svex-extn-correct$-lst
                                svl::width-of-svex-extn-correct$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))

    (Local
     (defthm loghead-1-of-bitp
       (Implies (bitp x)
                (equal (loghead 1 x) x))))

    (defret <fn>-is-correct
      (implies (and valid
                    (sv::svex-p test)
                    (sv::svex-p then)
                    (sv::svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                      (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                          (sv::svex-eval$ then (rp-evlt env-term a))
                        (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-special-bitxor
      :hints (("goal"
               :in-theory (e/d (csel-simplify-end-at-special-bitxor
                                svl::bit-listp-of-svex-fn
                                sv::svex-apply
                                sv::svex-apply$
                                sv::svex-call->fn sv::svex-call->args
                                svl::bit-listp-of-svex)
                               (valid-fa-c-chain-args-p
                                acl2::symbolp-of-car-when-symbol-listp
                                symbol-listp
                                svl::width-of-svex-extn-correct$-lst
                                svl::width-of-svex-extn-correct$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                ACL2::LOGAND-WITH-MASK)))))

    (local
     (defthm c-spec-of-0
       (and (equal (c-spec (list x y 0))
                   (c-spec (list x y)))
            (equal (c-spec (list x 0 y))
                   (c-spec (list x y)))
            (equal (c-spec (list 0 x y))
                   (c-spec (list x y))))
       :hints (("Goal"
                :in-theory (e/d (SUM sum-list c-spec) ())))))

    (local
     (defthm c-spec-logand-equiv
       (implies (and (bitp x)
                     (bitp y))
                (equal (equal (c-spec (list x y))
                              (logand x y))
                       t))
       :hints (("Goal"
                :in-theory (e/d (bitp) ())))))

    (defret <fn>-is-correct
      (implies (and valid
                    (sv::svex-p test)
                    (sv::svex-p then)
                    (sv::svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                      (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                          (sv::svex-eval$ then (rp-evlt env-term a))
                        (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-special-bitand
      :hints (("goal"
               :in-theory (e/d (csel-simplify-end-at-special-bitand
                                svl::bit-listp-of-svex-fn
                                sv::svex-apply
                                sv::svex-apply$
                                sv::svex-call->fn sv::svex-call->args
                                svl::bit-listp-of-svex)
                               (valid-fa-c-chain-args-p
                                acl2::symbolp-of-car-when-symbol-listp
                                symbol-listp
                                svl::width-of-svex-extn-correct$-lst
                                svl::width-of-svex-extn-correct$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                ACL2::LOGAND-WITH-MASK)))))

    (defret-mutual evals-correctly
      (defret <fn>-is-correct
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                        (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                            (sv::svex-eval$ then (rp-evlt env-term a))
                          (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-fa-c)
      (defret <fn>-is-correct
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                        (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                            (sv::svex-eval$ then (rp-evlt env-term a))
                          (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-fa-s)
      (defret <fn>-is-correct
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                        (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                            (sv::svex-eval$ then (rp-evlt env-term a))
                          (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-ha-s)
      (defret <fn>-is-correct
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                        (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                            (sv::svex-eval$ then (rp-evlt env-term a))
                          (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-ha-c)
      (defret <fn>-is-correct
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                        (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                            (sv::svex-eval$ then (rp-evlt env-term a))
                          (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify)
      :hints (("Goal"
               :expand ((csel-simplify-fa-c test then else
                                            :limit limit)
                        (csel-simplify-fa-s test then else
                                            :limit limit)
                        (csel-simplify-ha-s test then else
                                            :limit limit)
                        (csel-simplify-ha-c test then else
                                            :limit limit)
                        (csel-simplify test then else
                                       :limit limit))
               :do-not-induct t
               :in-theory (e/d (;;bitp
                                SVL::BIT-LISTP-OF-SVEX-FN
                                SV::SVEX-APPLY
                                SV::SVEX-APPLY$
                                SV::SVEX-CALL->FN SV::SVEX-CALL->args
                                SVL::BIT-LISTP-OF-SVEX
                                ;;bitp-of-svex-eval$-casesplit-trigger
                                ;;bitp
                                )
                               (;;WARRANTS-FOR-ADDER-PATTERN-MATCH

                                ;;BITP-OF-SVEX-EVAL$-CASESPLIT-TRIGGER

                                valid-fa-c-chain-args-p
                                ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP
                                SYMBOL-LISTP
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$-LST
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))))





(define csel-simplify-main ((svex sv::svex-p)
                            &key
                            ((env) 'env)
                            ((context rp-term-listp) 'context)
                            ((config svl::svex-reduce-config-p) 'config))
  :returns (res sv::svex-p :hyp (sv::svex-p svex))
  (b* (((mv test then else valid)
        (csel-branch svex))
       ((unless valid)
        svex)
       ((mv new-svex valid)
        (csel-simplify test then else :limit *large-number*)))
    (if valid
        new-svex
      svex))
  ///
  (defret <fn>-is-correct
    (implies (and (sv::Svex-p svex)
                  (rp-term-listp context)
                  (valid-sc env-term a)
                  (eval-and-all context a)
                  (falist-consistent-aux env env-term)
                  (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config))
                  (svl::integerp-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->integerp-extns config))
                  (force (warrants-for-adder-pattern-match)))
             (and (equal (sv::svex-eval$ res (rp-evlt env-term a))
                         (sv::svex-eval$ svex (rp-evlt env-term a)))
                  ))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d ()
                             ())))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Simplification for paralel-prefix logic

(define ppx-mergeable-precheck--collect-fa-c-args (svex)
  :returns (list-of-fa-c-args)
  (case-match svex
    (('sv::bitor x y)
     (append (ppx-mergeable-precheck--collect-fa-c-args x)
             (ppx-mergeable-precheck--collect-fa-c-args y)))
    (('sv::id x)
     (ppx-mergeable-precheck--collect-fa-c-args x))
    (('fa-c-chain & x y z)
     (list (list svex x y z)))
    (('ha-c-chain x y)
     (list (list svex x y 0)))
    (('sv::bitand x y)
     (list (list svex x y 0))))
  ///
  (defret svex-p-lemma-of-<fn>
    (implies (sv::Svex-p svex)
             (sv::svexlistlist-p list-of-fa-c-args))))




(define ppx-mergeable-find-matching-m2-aux (x y collected-fa-c-args)
  :returns (mv (foundp booleanp)
               (fa-c-term sv::Svex-p :hyp (sv::svexlistlist-p collected-fa-c-args)))
  (if (atom collected-fa-c-args)
      (mv nil 0)
    (b* (((unless (svl::equal-len (car collected-fa-c-args) 4))
          (ppx-mergeable-find-matching-m2-aux x y (cdr collected-fa-c-args)))
         ((list fa-c-term arg1 arg2 arg3) (car collected-fa-c-args))
         ((when (or (and (equal x arg1)
                         (or (equal y arg2)
                             (equal y arg3)))
                    (and (equal x arg2)
                         (or (equal y arg1)
                             (equal y arg3)))
                    (and (equal x arg3)
                         (or (equal y arg1)
                             (equal y arg2)))))
          (mv t fa-c-term)))
      (ppx-mergeable-find-matching-m2-aux x y (cdr collected-fa-c-args)))))


(define ppx-mergeable-find-matching-m2 ((svex sv::Svex-p)
                                        collected-fa-c-args
                                        &key
                                        ((config svl::svex-reduce-config-p)
                                         'config))
  ;; Given a collected-fa-c-args, finds and extracts a matching m2 term from a given bitand list.
  :returns (mv (foundp booleanp)
               (remaining-bitand sv::svex-p :hyp (sv::Svex-p svex))
               (m2-term sv::Svex-p :hyp (sv::Svex-p svex))
               (fa-c-term sv::Svex-p :hyp (sv::svexlistlist-p collected-fa-c-args)))
  :verify-guards :after-returns
  (case-match svex
    (('sv::bitand x y)
     (b* (((mv foundp rest-bitand m2-term fa-c-term)
           (ppx-mergeable-find-matching-m2 x collected-fa-c-args))
          ((when foundp)
           (mv foundp
               (ex-adder-fnc-from-unfloat
                (svl::bitand/or/xor-simple-constant-simplify 'sv::bitand rest-bitand y))
               m2-term fa-c-term))
          ((mv foundp rest-bitand m2-term fa-c-term)
           (ppx-mergeable-find-matching-m2 y collected-fa-c-args))
          ((when foundp)
           (mv foundp
               (ex-adder-fnc-from-unfloat
                (svl::bitand/or/xor-simple-constant-simplify 'sv::bitand rest-bitand x))
               m2-term fa-c-term)))
       (mv nil 0 0 0)))
    (('sv::bitxor x y)
     (b* (((mv found fa-c-term)
           (ppx-mergeable-find-matching-m2-aux x y collected-fa-c-args))
          (remaining-bitand (if (bitp (svl::width-of-svex svex)) 1 -1)))
       (mv found remaining-bitand svex fa-c-term)))
    (('sv::bitor x y) ;; instead of XOR, OR can work too.
     (b* (((mv found fa-c-term)
           (ppx-mergeable-find-matching-m2-aux x y collected-fa-c-args))
          (remaining-bitand (if (bitp (svl::width-of-svex svex)) 1 -1)))
       (mv found remaining-bitand svex fa-c-term)))
    (('ha-s-chain x y)
     (b* (((mv found fa-c-term)
           (ppx-mergeable-find-matching-m2-aux x y collected-fa-c-args))
          (remaining-bitand (if (bitp (svl::width-of-svex svex)) 1 -1)))
       (mv found remaining-bitand svex fa-c-term)))
    (('sv::id x)
     (ppx-mergeable-find-matching-m2 x collected-fa-c-args))
    (&
     (mv nil 0 0 0)))

  ///

  (defret <fn>-is-correct
    (implies (and (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config))
                  (sv::svex-p svex)
                  (warrants-for-adder-pattern-match)
                  foundp
                  )
             (equal (sv::4vec-bitand (sv::svex-eval$ remaining-bitand env)
                                     (sv::svex-eval$ m2-term env))
                    (sv::svex-eval$ svex env)))
    :hints (("Goal"
             :expand ((sv::svex-eval$ svex env))
             :in-theory (e/d (bitp
                              sv::svex-call->fn
                              sv::svex-apply$
                              sv::svex-apply
                              ha-s-chain
                              sv::svex-call->args)
                             (svl::svex-eval$-width-of-svex-is-correct
                              svl::svex-eval$-width-of-svex-is-correct
                              (:TYPE-PRESCRIPTION SVL::WIDTH-OF-SVEX-FN)
                              (:TYPE-PRESCRIPTION
                               SVL::WIDTH-OF-SVEX-EXTN-CORRECT$-LST))))
            (and stable-under-simplificationp
                 '(:use ((:instance svl::svex-eval$-width-of-svex-is-correct
                                    (svl::x svex)
                                    (svl::free-var-width 0)
                                    (svl::env env))
                         (:instance svl::svex-eval$-width-of-svex-is-correct
                                    (svl::x svex)
                                    (svl::free-var-width 1)
                                    (svl::env env)))))))

  )



(define ppx-mergeable-extract-matching-m2 ((svex sv::Svex-p)
                                           collected-fa-c-args
                                           &key
                                           ((config svl::svex-reduce-config-p) 'config))
  :verify-guards :after-returns
  :returns (mv (foundp booleanp)
               (remaining-bitor sv::Svex-p :hyp (sv::Svex-p svex))
               (remaining-bitand sv::svex-p :hyp (sv::Svex-p svex))
               (m2-term sv::Svex-p :hyp (sv::Svex-p svex))
               (fa-c-term sv::Svex-p :hyp (sv::svexlistlist-p collected-fa-c-args)))
  (case-match svex
    (('sv::bitor x y)
     (b* (((mv foundp remaining-bitand m2-term fa-c-term)
           (ppx-mergeable-find-matching-m2 svex collected-fa-c-args))
          ((when foundp)
           (mv foundp 0 remaining-bitand m2-term fa-c-term))

          ((mv foundp remaining-bitor remaining-bitand m2-term fa-c-term)
           (ppx-mergeable-extract-matching-m2 x collected-fa-c-args))
          ((when foundp)
           (mv foundp
               (ex-adder-fnc-from-unfloat
                (svl::bitand/or/xor-simple-constant-simplify 'sv::bitor remaining-bitor y))
               remaining-bitand m2-term fa-c-term))
          ((mv foundp remaining-bitor remaining-bitand m2-term fa-c-term)
           (ppx-mergeable-extract-matching-m2 y collected-fa-c-args))
          ((when foundp)
           (mv foundp
               (ex-adder-fnc-from-unfloat
                (svl::bitand/or/xor-simple-constant-simplify 'sv::bitor remaining-bitor x))
               remaining-bitand m2-term fa-c-term)))
       (mv nil svex 0 0 0)))
    ((fn & &)
     (b* (((unless (or (equal fn 'sv::bitxor)
                       (equal fn 'sv::bitand)
                       (equal fn 'ha-s-chain)
                       (equal fn 'ha-c-chain)))
           (mv nil svex 0 0 0))
          ((mv foundp remaining-bitand m2-term fa-c-term)
           (ppx-mergeable-find-matching-m2 svex collected-fa-c-args)))
       (mv foundp 0 remaining-bitand m2-term fa-c-term)))
    (('sv::id x)
     (ppx-mergeable-extract-matching-m2 x collected-fa-c-args))
    (& (mv nil svex 0 0 0)))
  ///

  (defret <fn>-is-correct
    (implies (and (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config))
                  (sv::svex-p svex)
                  (warrants-for-adder-pattern-match)
                  foundp
                  )
             (equal (sv::4vec-bitor (sv::svex-eval$ remaining-bitor env)
                                    (sv::4vec-bitand (sv::svex-eval$ remaining-bitand env)
                                                     (sv::svex-eval$ m2-term env)))
                    (sv::svex-eval$ svex env)))
    :hints (("Goal"
             :in-theory (e/d (sv::svex-call->fn
                              sv::svex-apply$
                              sv::svex-apply
                              ha-s-chain ha-c-chain
                              sv::svex-call->args)
                             ())))))





(local
 (defthm SVEX-QUOTE->VAL-when-integerp
   (implies (integerp x)
            (equal (sv::SVEX-QUOTE->VAL x) x))
   :hints (("Goal"
            :in-theory (e/d (sv::SVEX-QUOTE->VAL) ())))))



(define ppx-mergeable-node-pull-common-args (m2-term fa-c-term)
  :returns (mv success
               m2-regular-type-p
               (shared-arg1 sv::Svex-p :hyp (sv::Svex-p m2-term))
               (shared-arg2 sv::Svex-p :hyp (sv::Svex-p m2-term))
               (other-arg sv::Svex-p :hyp (sv::Svex-p fa-c-term)))
  (b* (((mv success m2-regular-type-p m2-arg1 m2-arg2)
        (case-match m2-term
          (('sv::bitxor x y)
           (mv t t x y))
          (('ha-s-chain x y)
           (mv t t x y))
          (('sv::bitor x y)
           (mv t nil x y))
          (& (mv nil nil 0 0))))
       ((unless success)
        (mv nil nil 0 0 0))
       ((mv success fa-c-arg1 fa-c-arg2 fa-c-arg3)
        (case-match fa-c-term
          (('fa-c-chain m x y z) (mv (valid-fa-c-chain-args-p m x)
                                     x y z))
          (('sv::bitand x y) (mv t x y 0))
          (('ha-c-chain x y) (mv t x y 0))
          (& (mv nil 0 0 0))))
       ((unless success)
        (mv nil nil 0 0 0))
       ((mv success shared-arg1 shared-arg2 other-arg)
        (cond ((or* (and* (equal fa-c-arg1 m2-arg1)
                          (equal fa-c-arg2 m2-arg2))
                    (and* (equal fa-c-arg1 m2-arg2)
                          (equal fa-c-arg2 m2-arg1)))
               (mv t m2-arg1 m2-arg2 fa-c-arg3))
              ((or* (and* (equal fa-c-arg1 m2-arg1)
                          (equal fa-c-arg3 m2-arg2))
                    (and* (equal fa-c-arg1 m2-arg2)
                          (equal fa-c-arg3 m2-arg1)))
               (mv t m2-arg1 m2-arg2 fa-c-arg2))
              ((or* (and* (equal fa-c-arg2 m2-arg1)
                          (equal fa-c-arg3 m2-arg2))
                    (and* (equal fa-c-arg2 m2-arg2)
                          (equal fa-c-arg3 m2-arg1)))
               (mv t m2-arg1 m2-arg2 fa-c-arg1))
              (t (mv nil 0 0 0)))))
    (mv success m2-regular-type-p shared-arg1 shared-arg2 other-arg))
  ///

  (defret <fn>-is-correct
    (implies (and success
                  (warrants-for-adder-pattern-match))
             (and (implies (and (bitp (sv::svex-eval$ shared-arg1 env))
                                (bitp (sv::svex-eval$ shared-arg2 env))
                                (case-split m2-regular-type-p))
                           (equal (s-spec (list (sv::svex-eval$ shared-arg1 env)
                                                (sv::svex-eval$ shared-arg2 env)))
                                  (sv::svex-eval$ m2-term env)))

                  (implies (and (bitp (sv::svex-eval$ shared-arg1 env))
                                (bitp (sv::svex-eval$ shared-arg2 env))
                                (not m2-regular-type-p))
                           (equal
                            (binary-or (sv::svex-eval$ shared-arg1 env)
                                       (sv::svex-eval$ shared-arg2 env))
                            (sv::svex-eval$ m2-term env)))

                  (implies (and (bitp (sv::svex-eval$ shared-arg1 env))
                                (bitp (sv::svex-eval$ shared-arg2 env))
                                (bitp (sv::svex-eval$ other-arg env)))
                           (equal (c-spec (list (sv::svex-eval$ shared-arg1 env)
                                                (sv::svex-eval$ shared-arg2 env)
                                                (sv::svex-eval$ other-arg env)))
                                  (sv::svex-eval$ fa-c-term env)))))
    :hints (("Goal"
             :in-theory (e/d (or*
                              bitp
                              SV::SVEX-APPLY$
                              SV::SVEX-CALL->FN
                              SV::SVEX-CALL->args)
                             ()))))

  #|(defret <fn>-is-correct-2
  (implies (and success
  (warrants-for-adder-pattern-match))
  (implies (and (bitp (sv::svex-eval$ shared-arg1 env))
  (bitp (sv::svex-eval$ shared-arg2 env))
  (equal other-arg -1))
  (equal (fa-c-chain 0
  (sv::svex-eval$ shared-arg1 env)
  (sv::svex-eval$ shared-arg2 env)
  -1)
  (sv::svex-eval$ fa-c-term env))))
  :hints (("Goal"
  :in-theory (e/d (or*
  bitp
  SV::SVEX-APPLY$
  SV::SVEX-CALL->FN
  SV::SVEX-CALL->args)
  ()))))|#
  )



(local
 (defthm 4vec-bitor-of-minus1
   (equal (sv::4vec-bitor -1 x)
          -1)
   :hints (("Goal"
            :in-theory (e/d (SV::3VEC-BITOR
                             sv::4vec-bitor)
                            ())))))

(define ppx-simplify-mergeable-node-simplify-args ((remaining-bitor sv::Svex-p)
                                                   (fa-c-arg1 sv::Svex-p)
                                                   (fa-c-arg2 sv::Svex-p)
                                                   (fa-c-arg3 sv::Svex-p)
                                                   &key
                                                   ((env) 'env)
                                                   ((context rp-term-listp) 'context)
                                                   ((config svl::svex-reduce-config-p) 'config))
  (b* ((svl::under-xor nil)
       (svl::leave-depth 2)
       (leaves (svl::bitand/or/xor-collect-leaves remaining-bitor 'sv::bitor))
       (svl::nodes-to-skip-alist nil)
       (svl::fn 'sv::bitor)
       ((mv fa-c-arg1 &) (svl::bitand/bitor-cancel-repeated-aux fa-c-arg1 leaves 0))
       ((mv fa-c-arg2 &) (svl::bitand/bitor-cancel-repeated-aux fa-c-arg2 leaves 0))
       ((mv fa-c-arg3 &) (svl::bitand/bitor-cancel-repeated-aux fa-c-arg3 leaves 0)))
    (mv fa-c-arg1 fa-c-arg2 fa-c-arg3)))



(define ppx-simplify-mergeable-node ((svex sv::svex-p)
                                     &key
                                     ((limit natp) 'limit)
                                     ((env) 'env)
                                     ((context rp-term-listp) 'context)
                                     ((config svl::svex-reduce-config-p) 'config))
  :measure (nfix limit)
  :no-function t
  :Returns (res-svex sv::svex-p :hyp (sv::svex-p svex))
  :verify-guards :after-returns
  (if (zp limit) ;; proving the measure is not easy so I will use memoize-partial
      svex
    (let ((limit (1- limit)))
      (b* (((unless (and (consp svex)
                         (equal (car svex) 'sv::bitor)
                         (svl::equal-len (cdr svex) 2)))
            svex)

           (pattern-fn-call-list (look-for-fa-c-chain-pattern svex))
           ((when (consp pattern-fn-call-list))
            (b* ((pattern-fn-call (pull-the-first-applicable-adder-pattern nil pattern-fn-call-list nil))
                 ((unless pattern-fn-call)
                  svex)
                 ((pattern-fn-call x) pattern-fn-call)
                 (svex (pattern-call x)))
              (zero-fa-c-chain-extra-arg svex)))

           (collected-fa-c-args (ppx-mergeable-precheck--collect-fa-c-args svex))
           ((mv found remaining-bitor remaining-bitand m2-term fa-c-term)
            (ppx-mergeable-extract-matching-m2 svex collected-fa-c-args))
           ((unless found)
            (b* (;; if not found try simplifing first
                 #|((mv new-svex &) ;; NOTE: THIS MAY NEVER BE USEFUL.
                 (simplify-to-find-fa-c-patterns-aux
                 x 5 :strength 2
                 :inside-out t))|#
                 (new-svex (svl::bitand/or/xor-cancel-repeated
                            'sv::bitor (first (cdr svex)) (second (cdr svex))
                            :leave-depth 5
                            :nodes-to-skip-alist nil))
                 (simp-changed (not (equal new-svex svex)))
                 (new-new-svex (if simp-changed
                                   (ppx-simplify-mergeable-node new-svex)
                                 new-svex))
                 ((when (not (equal new-new-svex new-svex)))
                  new-new-svex)
                 ;; if here, it means svl::bitand/or/xor-cancel-repeated didn't
                 ;; help.
                 ((mv common-terms pulled-svex)
                  (svl::bitor-of-and-pull-commons-aux svex
                                                      :leave-depth 5
                                                      :collect-from-arg1 nil))
                 ((mv common-terms pulled-svex)
                  (if common-terms
                      (mv common-terms pulled-svex)
                    ;; try again but collect from the first arg this time.
                    (svl::bitor-of-and-pull-commons-aux svex
                                                        :leave-depth 5
                                                        :collect-from-arg1 t)))
                 ((unless common-terms) svex)
                 (new-svex (ppx-simplify-mergeable-node pulled-svex))
                 ((when (equal new-svex pulled-svex)) svex))
              (svl::bitand/or/xor-simple-constant-simplify
               'sv::bitand common-terms new-svex)))
           ((mv remove-success remaining-bitor)
            (svl::bitor-remove-node remaining-bitor fa-c-term))
           ((unless remove-success) svex)

           (remaining-bitor (ex-adder-fnc-from-unfloat remaining-bitor))

           ((mv success & shared-arg1 shared-arg2 other-arg)
            (ppx-mergeable-node-pull-common-args m2-term fa-c-term))

           ((unless success) svex)

           ((Unless (and (svl::bitp-of-svex other-arg)
                         (svl::bitp-of-svex remaining-bitor)
                         (or (svl::bitp-of-svex remaining-bitand)
                             #|(equal remaining-bitand -1)|#)
                         (svl::bitp-of-svex shared-arg1)
                         (svl::bitp-of-svex shared-arg2)))
            (progn$ (cwe "Failed: ~p0. remaining-bitor: ~p1 remaining-bitand: ~p2 ~%Config:~p3,context:~p4,env:~p5"
                         (list (cons :other-arg (svl::bitp-of-svex other-arg))
                               (cons :remaining-bitor (svl::bitp-of-svex remaining-bitor))
                               (cons :remaining-bitand (svl::bitp-of-svex remaining-bitand))
                               (cons :shared-arg1 (svl::bitp-of-svex shared-arg1))
                               (cons :shared-arg2 (svl::bitp-of-svex shared-arg2)))
                         remaining-bitor remaining-bitand
                         config context env)
                    ;;(hard-error 'nil "" nil)
                    svex))

           (new-inner-bitor (ex-adder-fnc-from-unfloat
                             (svl::bitand/or/xor-simple-constant-simplify 'sv::bitor
                                                                          other-arg
                                                                          remaining-bitand)))
           #|((mv shared-arg1 shared-arg2 new-inner-bitor)
           (ppx-simplify-mergeable-node-simplify-args remaining-bitor shared-arg1 shared-arg2 new-inner-bitor))|#

           (new-inner-bitor (ppx-simplify-mergeable-node new-inner-bitor))

           #|((mv shared-arg1 shared-arg2 new-inner-bitor)
           (ppx-simplify-mergeable-node-simplify-args remaining-bitor shared-arg1 shared-arg2 new-inner-bitor))|#

           (new-fa-c-chain (create-fa-c-chain-instance shared-arg1 shared-arg2 new-inner-bitor))

           ;; TODO:
           ;; MAYBE I SHOULD TRY CLEARING  THE ARGS OF NEW-FA-C-CHAIN HERE WITH
           ;; REPEATED    CHECK    (svl::bitand/or/xor-cancel-repeated)    FROM
           ;; REMAINING-BITOR TO HELP THE CONSTANT 1 PROPAGATION CASE......
           ;; IDEALLY BEFORE THE RECURSIVE CALL.....

           (new-bitor (ex-adder-fnc-from-unfloat
                       (svl::bitand/or/xor-simple-constant-simplify 'sv::bitor
                                                                    remaining-bitor
                                                                    new-fa-c-chain))))
        (ppx-simplify-mergeable-node new-bitor))))
  ///

  (local
   (defthmd bitp-of-svex-eval$-casesplit-trigger
     (implies (and (sv::svex-p svex)
                   (rp::rp-term-listp context)
                   (rp::valid-sc env-term a)
                   (rp::eval-and-all context a)
                   (rp::falist-consistent-aux env env-term)
                   (svl::width-of-svex-extn-correct$-lst
                    (svl::svex-reduce-config->width-extns config))
                   (svl::integerp-of-svex-extn-correct$-lst
                    (svl::svex-reduce-config->integerp-extns config)))
              (equal (svl::bitp-of-svex svex )
                     (and (hide (svl::bitp-of-svex svex))
                          (bitp (sv::Svex-eval$ svex (rp-evlt env-term a))))))
     :hints (("Goal"
              :expand (hide (svl::bitp-of-svex svex ))
              :in-theory (e/d () ())))))

  (local
   (defthm ppx-merge-lemma
     (implies (and (bitp x)
                   (bitp y)
                   (bitp z1)
                   (bitp z2))
              (and (equal (c-spec (list x y (sv::4vec-bitor z2 z1)))
                          (sv::4vec-bitor (c-spec (list x y z1))
                                          (sv::4vec-bitand
                                           (if (mv-nth ;; m2-term can be bitxor
                                                ;; or bitor. This helps with a
                                                ;; nice caseplit between the two.
                                                1
                                                (ppx-mergeable-node-pull-common-args
                                                 (mv-nth 3
                                                         (ppx-mergeable-extract-matching-m2
                                                          svex
                                                          (ppx-mergeable-precheck--collect-fa-c-args svex)))
                                                 (mv-nth 4
                                                         (ppx-mergeable-extract-matching-m2
                                                          svex
                                                          (ppx-mergeable-precheck--collect-fa-c-args svex)))))

                                               (s-spec (list x y))
                                             (binary-or x y))
                                           z2)))
                   #|(equal (sv::4vec-bitor (c-spec (list x y z1))
                   (sv::4vec-bitand (b-or x y)
                   z2))
                   (sv::4vec-bitor (c-spec (list x y z1))
                   (sv::4vec-bitand (ha-s-chain x y)
                   z2)))|#))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (defret <fn>-is-correct
    (implies (and (sv::svex-p svex)
                  (rp::rp-term-listp context)
                  (rp::valid-sc env-term a)
                  (rp::eval-and-all context a)
                  (rp::falist-consistent-aux env env-term)
                  (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config))
                  (svl::integerp-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->integerp-extns config))
                  (force (warrants-for-adder-pattern-match)))
             (equal (sv::svex-eval$ res-svex (rp-evlt env-term a))
                    (sv::svex-eval$ svex (rp-evlt env-term a))))
    :hints (("Goal"
             :do-not-induct t
             :induct (ppx-simplify-mergeable-node svex)
             :expand ((:free (args) (sv::svex-apply 'sv::bitor args))
                      (:free (args) (sv::svex-apply$ 'sv::bitor args))
                      (:free (args) (sv::svex-apply 'sv::bitand args)))
             :in-theory (e/d (;;ppx-mergeable-node-pull-common-args
                              or*
                              sv::svex-call->fn
                              ;;sv::svex-apply$
                              ;;sv::svex-apply
                              ;;ha-s-chain
                              sv::svex-call->args
                              ;;bitp
                              )
                             ()))
            (and stable-under-simplificationp
                 '(:use ((:instance look-for-fa-c-chain-pattern-correct-pattern
                                    (pattern (pull-the-first-applicable-adder-pattern
                                              nil (look-for-fa-c-chain-pattern svex) nil))
                                    (env (rp-evlt env-term a)))
                         ;; unnecessary but just in case:
                         (:instance look-for-fa-c-chain-pattern-correct-pattern
                                    (pattern (pull-the-first-applicable-adder-pattern
                                              nil (look-for-fa-c-chain-pattern svex) nil))
                                    (env env)))
                        )))
    ))








(defines ppx-simplify
  :verify-guards nil
  (define ppx-simplify ((svex sv::svex-p)
                        &key
                        ((env) 'env)
                        ((context rp-term-listp) 'context)
                        ((config svl::svex-reduce-config-p) 'config))
    :returns (res-svex sv::svex-p :hyp (sv::svex-p svex))
    :measure (sv::Svex-count svex)
    (sv::svex-case
     svex
     :var svex
     :quote svex
     :call (b* ((args (ppx-simplify-lst svex.args))
                (new-svex (sv::svex-call svex.fn args))
                (new-svex (csel-simplify-main new-svex))
                (bitor-p (case-match new-svex (('sv::bitor & &) t)))
                ;; WARNING: TODO: DANGEROUS TO DO THIS HERE!!!!!!!!
                ;; But this may help with the case where a constant 1 is propagated
                ;; in the ppx adders...
                #|(new-svex (if bitor-p
                (svl::bitand/or/xor-cancel-repeated
                'sv::bitor (first (cdr new-svex)) (second (cdr new-svex))
                :leave-depth 1)
                new-svex))|#)
             (if bitor-p
                 (ppx-simplify-mergeable-node new-svex :limit 10000)
               new-svex))))
  (define ppx-simplify-lst ((lst sv::svexlist-p)
                            &key
                            ((env) 'env)
                            ((context rp-term-listp) 'context)
                            ((config svl::svex-reduce-config-p) 'config))
    :returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
    :measure (sv::Svexlist-count lst)
    (if (atom lst)
        nil
      (hons (ppx-simplify (car lst))
            (ppx-simplify-lst (cdr lst)))))
  ///
  (verify-guards ppx-simplify-fn)

  (memoize 'ppx-simplify-fn
           ;; :condition '(eq (sv::svex-kind svex) :call)
           )

  (defret-mutual ppx-simplify-correct
    (defret <fn>-is-correct
      (implies (and (sv::svex-p svex)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svex-eval$ res-svex (rp-evlt env-term a))
                      (sv::svex-eval$ svex (rp-evlt env-term a))))
      :fn ppx-simplify)
    (defret <fn>-is-correct
      (implies (and (sv::svexlist-p lst)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svexlist-eval$ res-lst (rp-evlt env-term a))
                      (sv::svexlist-eval$ lst (rp-evlt env-term a))))
      :fn ppx-simplify-lst)
    :hints (("Goal"
             :do-not-induct t
             :expand ((ppx-simplify-lst nil)
                      (ppx-simplify svex)
                      (ppx-simplify-lst lst)
                      (:free (args) (SV::SVEX-APPLY 'SV::BITOR args)))
             :in-theory (e/d (SV::SVEX-CALL->ARGS
                              SV::SVEX-CALL->fn)
                             (csel-simplify-main-is-correct)))
            (and stable-under-simplificationp
                 '(:use (:instance csel-simplify-main-is-correct
                                   (svex
                                    (sv::svex-call (car svex)
                                                   (ppx-simplify-lst (cdr svex)))))))))

  )




(define ppx-simplify-alist ((alist sv::svex-alist-p)
                            &key
                            ((env) 'env)
                            ((context rp-term-listp) 'context)
                            ((config svl::svex-reduce-config-p) 'config))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
  (if (atom alist)
      nil
    (acons (caar alist)
           (ppx-simplify (cdar alist))
           (ppx-simplify-alist (cdr alist))))
  ///
  (defret <fn>-is-correct
    (implies (and (sv::svex-alist-p alist)
                  (rp-term-listp context)
                  (valid-sc env-term a)
                  (eval-and-all context a)
                  (falist-consistent-aux env env-term)
                  (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config))
                  (svl::integerp-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->integerp-extns config))
                  (force (warrants-for-adder-pattern-match)))
             (equal (sv::svex-alist-eval$ res (rp-evlt env-term a))
                    (sv::svex-alist-eval$ alist (rp-evlt env-term a))))
    :hints (("goal"
             :do-not-induct t
             :induct (ppx-simplify-alist alist)
             :in-theory (e/d (sv::svex-alist-eval$)
                             ())))))
