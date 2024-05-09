

; Functions for quick search of adder patterns.


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

(local
 (include-book "centaur/bitops/ihs-extensions" :dir :system))

(local
 (include-book "ihs/logops-lemmas" :dir :system))

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; unfloat related functions.


;; Globally search and get rid of things like unfloat/id when possible.
;; NOT USED.
(defines clear-adder-fnc-from-unfloat
  :verify-guards nil
  (define clear-adder-fnc-from-unfloat ((svex sv::svex-p))
    :returns (res-svex sv::svex-p :hyp (sv::svex-p svex))
    :measure (sv::Svex-count svex)
    (sv::svex-case
     svex
     :quote svex
     :var svex
     :call
     (ex-adder-fnc-from-unfloat
      (sv::Svex-call svex.fn
                     (clear-adder-fnc-from-unfloat-lst svex.args)))))
  (define clear-adder-fnc-from-unfloat-lst ((lst sv::svexlist-p))
    :returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
    :measure (sv::Svexlist-count lst)
    (if (atom lst)
        nil
      (hons (clear-adder-fnc-from-unfloat (car lst))
            (clear-adder-fnc-from-unfloat-lst (cdr lst)))))
  ///
  (verify-guards clear-adder-fnc-from-unfloat)

  (memoize 'clear-adder-fnc-from-unfloat))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; (defsection fix-order-of-fa/ha-s-args
;;   ;; After replacements,  ordered-ness of  arguments might change,  which might
;;   ;; prevent patterns  from being found  when looking more carefully.   So This
;;   ;; function goes around and reorders arguments in ONLY fa-s and ha-s arguments.
;;   (defines fix-order-of-fa/ha-s-args
;;     :verify-guards nil
;;     (define fix-order-of-fa/ha-s-args ((x sv::svex-p))
;;       :measure (sv::svex-count x)
;;       :returns (res sv::svex-p :hyp (sv::svex-p x))
;;       (sv::svex-case
;;        x
;;        :var x
;;        :quote x
;;        :call (case-match x
;;                (('fa-s-chain & & &)
;;                 (b* ((lst1 (fix-order-of-fa/ha-s-args-list x.args))
;;                      (lst2 (acl2::merge-sort-lexorder lst1)))
;;                   (sv::svex-call x.fn lst2)))
;;                (('ha-s-chain & &)
;;                 (b* ((lst1 (fix-order-of-fa/ha-s-args-list x.args))
;;                      (lst2 (acl2::merge-sort-lexorder lst1)))
;;                   (sv::svex-call x.fn lst2)))
;;                (& (sv::svex-call
;;                    x.fn
;;                    (fix-order-of-fa/ha-s-args-list x.args))))))
;;     (define fix-order-of-fa/ha-s-args-list ((lst sv::svexlist-p))
;;       :measure (sv::svexlist-count lst)
;;       :returns (res sv::svexlist-p :hyp (sv::svexlist-p lst))
;;       (if (atom lst)
;;           nil
;;         (hons (fix-order-of-fa/ha-s-args (car lst))
;;               (fix-order-of-fa/ha-s-args-list (cdr lst)))))

;;     ///

;;     (local
;;      (defthm svexlist-p-implies-true-listp
;;        (implies (sv::svexlist-p lst)
;;                 (true-listp lst))))

;;     (verify-guards fix-order-of-fa/ha-s-args)

;;     (memoize 'fix-order-of-fa/ha-s-args
;;              ;; :condition '(eq (sv::svex-kind x) :call)
;;              )

;;     (defret-mutual <fn>-is-correct
;;       (defret <fn>-is-correct
;;         (implies (and (warrants-for-adder-pattern-match)
;;                       (sv::svex-p x))
;;                  (equal (sv::svex-eval$ res env)
;;                         (sv::svex-eval$ x env)))
;;         :fn fix-order-of-fa/ha-s-args)
;;       (defret <fn>-is-correct
;;         (implies (and (warrants-for-adder-pattern-match)
;;                       (sv::svexlist-p lst))
;;                  (equal (sv::svexlist-eval$ res env)
;;                         (sv::svexlist-eval$ lst env)))
;;         :fn fix-order-of-fa/ha-s-args-list)
;;       :hints (("Goal"

;;                :expand ((:free (args)
;;                                (sv::svex-apply$ 'ha-s-chain args))
;;                         (:free (args)
;;                                (sv::svex-apply$ 'fa-s-chain args))
;;                         (acl2::merge-sort-lexorder (cdr x))
;;                         (fix-order-of-fa/ha-s-args-list lst)
;;                         (fix-order-of-fa/ha-s-args x))
;;                :in-theory (e/d (acl2::merge-lexorder
;;                                 acl2::merge-sort-lexorder
;;                                 ha-s-chain
;;                                 fa-s-chain
;;                                 sv::svex-call->fn
;;                                 sv::svex-call->args)
;;                                ())))))

;;   (define fix-order-of-fa/ha-s-args-alist ((alist sv::svex-alist-p))
;;     :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
;;     (if (atom alist)
;;         nil
;;       (acons (caar alist)
;;              (fix-order-of-fa/ha-s-args (cdar alist))
;;              (fix-order-of-fa/ha-s-args-alist (cdr alist))))
;;     ///
;;     (defret <fn>-is-correct
;;       (implies (and (warrants-for-adder-pattern-match)
;;                     (sv::svex-alist-p alist))
;;                (equal (sv::svex-alist-eval$ res env)
;;                       (sv::svex-alist-eval$ alist env)))
;;       :fn fix-order-of-fa/ha-s-args-alist
;;       :hints (("Goal"
;;                :in-theory (e/d (SV::SVEX-ALIST-EVAL$) ()))))))


;; (define extract-from-unfloat ((x sv::svex-p))
;;   :returns (res sv::svex-p :hyp (sv::svex-p x))
;;   (case-match x
;;     (('sv::unfloat x)
;;      x)
;;     (& x)))


(defsection alistp-of-of-fast-alist-clean
  (defthm alistp-of-of-fast-alist-fork
    (implies (and (alistp x)
                  (alistp last))
             (alistp (fast-alist-fork x last))))

  (defthm alistp-of-last
    (implies (alistp x)
             (alistp (last x))))

  (defthm alistp-of-cdr
    (implies (alistp x)
             (alistp (cdr x))))

  (defthm alistp-of-of-fast-alist-clean
    (implies (force (alistp x))
             (alistp (fast-alist-clean x)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FOR STATISTICS
(progn
  (define count-newly-found-adders-in-pattern-alist-aux (fn-lst adder-type (full-lst true-listp))
    ;; look for a pair of ha with the same column value.
    (if (atom fn-lst)
        nil
      (b* ((x (car fn-lst))
           ((unless (consp x))
            (count-newly-found-adders-in-pattern-alist-aux (cdr fn-lst) adder-type full-lst))
           (fn (car x))
           (column (cdr x))
           ((when (and (eq adder-type 'ha)
                       (or (and (eq fn 'ha-c-chain)
                                (member-equal (cons 'ha-s-chain column)
                                              full-lst))
                           (and (eq fn 'ha-s-chain)
                                (member-equal (cons 'ha-c-chain column)
                                              full-lst))
                           (and (eq fn 'ha+1-c-chain)
                                (member-equal (cons 'ha+1-s-chain column)
                                              full-lst))
                           (and (eq fn 'ha+1-s-chain)
                                (member-equal (cons 'ha+1-c-chain column)
                                              full-lst)))))
            t))
        (count-newly-found-adders-in-pattern-alist-aux (cdr fn-lst) adder-type full-lst))))

  (define count-newly-found-adders-in-pattern-alist ((pattern-alist pattern-alist-p)
                                                     &key
                                                     (track-column? 'track-column?)
                                                     ((adder-type symbolp) 'adder-type))
    (if (atom pattern-alist)
        0
      (+ (b* ((fn-list (cdar pattern-alist)))
           (if (cond (track-column?
                      (and (member-eq :new fn-list)
                           (count-newly-found-adders-in-pattern-alist-aux fn-list adder-type fn-list)))
                     ((eq adder-type 'ha)
                      (or (subsetp-eq '(:new ha-c-chain ha-s-chain)
                                      fn-list)
                          (subsetp-eq '(:new ha+1-c-chain ha+1-s-chain)
                                      fn-list)))
                     ((eq adder-type 'fa)
                      (subsetp-eq '(:new fa-c-chain)
                                  fn-list)))
               1 0))
         (count-newly-found-adders-in-pattern-alist (cdr pattern-alist))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Try  to wrap  booth encoding  logic (partial  products) with  ID to  prevent
;; oversimplification.  Strategy: Look for  half-adder patters. Likely (but not
;; guaranteed), the  partial products will  first end  up in shared  bitand and
;; bitxor logic.

(defines wrap-pp-with-id-aux
  :verify-guards nil
  (define wrap-pp-with-id-aux ((x sv::svex-p)
                               (args-alist alistp))
    :returns (mv (res sv::svex-p :hyp (sv::svex-p x))
                 wrapped)
    :measure (sv::svex-count x)
    (sv::svex-case
     x
     :var (mv x nil)
     :quote (mv x nil)
     :call (b* (((mv args wrapped) (wrap-pp-with-id-lst-aux x.args args-alist))
                ((when wrapped) (mv (sv::svex-call x.fn args) t))
                ((when (hons-get x args-alist))
                 (mv (sv::svex-call 'id (hons-list x)) t)))
             (mv x nil))))
  (define wrap-pp-with-id-lst-aux ((lst sv::svexlist-p)
                                   (args-alist alistp))
    :returns (mv (res sv::svexlist-p :hyp (sv::svexlist-p lst))
                 wrapped)
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        (mv nil nil)
      (b* (((mv cur w1) (wrap-pp-with-id-aux (car lst) args-alist))
           ((mv rest w2) (wrap-pp-with-id-lst-aux (cdr lst) args-alist)))
        (mv (hons cur rest)
            (or w1 w2)))))
  ///
  (verify-guards wrap-pp-with-id-aux)

  (defret-mutual <fn>-is-correct
    (defret <fn>-is-correct
      (equal (sv::Svex-eval$ res env)
             (sv::Svex-eval$ x env))
      :fn wrap-pp-with-id-aux)
    (defret <fn>-is-correct
      (equal (sv::Svexlist-eval$ res env)
             (sv::Svexlist-eval$ lst env))
      :fn wrap-pp-with-id-lst-aux)
    :hints (("Goal"
             :Expand ((wrap-pp-with-id-aux nil args-alist)
                      (wrap-pp-with-id-aux x args-alist)
                      (wrap-pp-with-id-lst-aux lst args-alist))
             :in-theory (e/d (SV::SVEX-APPLY)
                             ()))))

  (memoize 'wrap-pp-with-id-aux
           ;; :condition '(eq (sv::svex-kind x) :call)
           )
  )

(define wrap-pp-with-id-alist-aux ((svex-alist sv::svex-alist-p)
                                   (args-alist alistp))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
  :verify-guards :after-returns
  (if (atom svex-alist)
      svex-alist
    (acons (caar svex-alist)
           (b* (((mv res &)
                 (wrap-pp-with-id-aux (cdar svex-alist) args-alist)))
             res)
           (wrap-pp-with-id-alist-aux (cdr svex-alist) args-alist)))
  ///
  (defret <fn>-is-correct
    (equal (sv::Svex-alist-eval$ res env)
           (sv::Svex-alist-eval$ svex-alist env))
    :fn wrap-pp-with-id-alist-aux
    :hints (("Goal"
             :in-theory (e/d (sv::svex-alist-eval$) ())))))



(define wrap-pp-with-id-process-pattern-alist ((pattern-alist pattern-alist-p))
  :returns (res alistp)
  (if (atom pattern-alist)
      nil
    (b* ((cur-args (caar pattern-alist))
         (cur-patterns (cdar pattern-alist))
         ((unless (and (svl::equal-len cur-args 2)
                       (subsetp-equal '(ha-s-chain ha-c-chain)
                                      cur-patterns)))
          (wrap-pp-with-id-process-pattern-alist (cdr pattern-alist))))
      (hons-acons
       (first cur-args)
       nil
       (hons-acons (second cur-args)
                   nil
                   (wrap-pp-with-id-process-pattern-alist (cdr
                                                           pattern-alist)))))))



(define wrap-pp-with-id-alist ((svex-alist sv::svex-alist-p)
                               &key
                               ((env) 'env)
                               ((context rp-term-listp) 'context)
                               ((config svl::svex-reduce-config-p) 'config))
  :Returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
  (b* (((unless (aggressive-find-adders-in-svex))
        svex-alist)
       (- (cw "- Before searching for adders, let's try to wrap partial products with ID to prevent oversimplification during adder pattern finding.~%~%"))
       ((mv pattern-alist &)
        (gather-adder-patterns-in-svex-alist svex-alist :adder-type 'ha :track-column? nil))
       (pattern-alist (fast-alist-clean pattern-alist))
       (args-alist (wrap-pp-with-id-process-pattern-alist pattern-alist))
       (- (fast-alist-free pattern-alist))
       (res (wrap-pp-with-id-alist-aux svex-alist args-alist))
       (- (fast-alist-free args-alist))
       (- (clear-memoize-table 'wrap-pp-with-id-aux)))
    res)
  ///
  (defret <fn>-is-correct
    (equal (sv::Svex-alist-eval$ res free-env)
           (sv::Svex-alist-eval$ svex-alist free-env))
    :fn wrap-pp-with-id-alist
    :hints (("Goal"
             :in-theory (e/d (sv::svex-alist-eval$) ())))))


(defines extract-svex-from-id
  :verify-guards nil
  :hints (("Goal"
           :expand ((SV::SVEX-COUNT X))
           :in-theory (e/d (SV::SVEX-CALL->ARGS)
                           ())))

  (define extract-svex-from-id ((x sv::svex-p))
    :returns (res sv::svex-p :hyp (sv::svex-p x))
    :measure (sv::svex-count x)
    (sv::svex-case
     x
     :var x
     :quote x
     :call
     (case-match x
       (('id x) (extract-svex-from-id x))
       (& (sv::Svex-call x.fn (extract-svex-from-id-lst x.args))))))

  (define extract-svex-from-id-lst ((lst sv::svexlist-p))
    :returns (res sv::svexlist-p :hyp (sv::svexlist-p lst))
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        nil
      (hons (extract-svex-from-id (car lst))
            (extract-svex-from-id-lst (cdr lst)))))
  ///
  (verify-guards extract-svex-from-id)

  (defret-mutual <fn>-is-correct
    (defret <fn>-is-correct
      (equal (sv::Svex-eval$ res env)
             (sv::Svex-eval$ x env))
      :fn extract-svex-from-id)
    (defret <fn>-is-correct
      (equal (sv::Svexlist-eval$ res env)
             (sv::Svexlist-eval$ lst env))
      :fn extract-svex-from-id-lst)
    :hints (("Goal"
             :Expand ((extract-svex-from-id nil)
                      (extract-svex-from-id-lst nil)
                      (extract-svex-from-id x)
                      (extract-svex-from-id-lst lst))
             :in-theory (e/d (SV::SVEX-CALL->FN
                              SV::SVEX-CALL->ARGS
                              SV::SVEX-APPLY)
                             ()))))

  (memoize 'extract-svex-from-id
           ;; :condition '(eq (sv::svex-kind x) :call)
           )
  )

(define extract-svex-from-id-alist ((svex-alist sv::svex-alist-p))
  :Returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
  (if (atom svex-alist)
      nil
    (acons (caar svex-alist)
           (extract-svex-from-id (cdar svex-alist))
           (extract-svex-from-id-alist (cdr svex-alist))))
  ///
  (defret <fn>-is-correct
    (equal (sv::Svex-alist-eval$ res env)
           (sv::Svex-alist-eval$ svex-alist env))
    :fn extract-svex-from-id-alist
    :hints (("Goal"
             :expand ((SV::SVEX-ALIST-EVAL NIL ENV))
             :in-theory (e/d (sv::svex-alist-eval$) ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define zero-fa-c-chain-extra-arg ((svex sv::svex-p)
                                   &key
                                   ((env) 'env)
                                   ((context rp-term-listp) 'context)
                                   ((config svl::svex-reduce-config-p) 'config))
  :Returns (res sv::svex-p :hyp (sv::svex-p svex))
  :prepwork ((local
              (in-theory (e/d (ACL2::MERGE-LEXORDER
                               acl2::merge-sort-lexorder)
                              ()))))
  :inline t
  (case-match svex
    (('fa-c-chain extra-arg arg1 arg2 arg3)
     (b* (((unless (valid-fa-c-chain-args-p extra-arg arg1))
           (progn$ (raise "valid-fa-c-chain-args-p failed for: ~p0~%" svex)
                   svex))
          ((unless (or (equal extra-arg 0)
                       (and* (svl::bitp-of-svex arg1)
                             (svl::bitp-of-svex arg2)
                             (svl::bitp-of-svex arg3))))
           (progn$ (cwe "bitp check in rp::zero-fa-c-chain-extra-arg ~p0 failed.~%"
                        (list (or (svl::bitp-of-svex arg1) arg1)
                              (or (svl::bitp-of-svex arg2) arg2)
                              (or (svl::bitp-of-svex arg3) arg3)))
                   svex))
          ((list arg1 arg2 arg3)
           (acl2::merge-sort-lexorder (list arg1 arg2 arg3)))
          ((when (and* (equal arg1 0)
                       (equal arg2 0)))
           0)
          ;; extract when one of the args is 1.
          ((when (and (equal arg1 1)
                      (svl::bitp-of-svex arg2)
                      (svl::bitp-of-svex arg3)))
           (ex-adder-fnc-from-unfloat
            (svl::bitand/or/xor-simple-constant-simplify 'sv::bitor arg2 arg3)))
          ((when (equal arg1 0))
           (ex-adder-fnc-from-unfloat
            (svl::bitand/or/xor-simple-constant-simplify 'sv::bitand arg2 arg3))))
       (sv::svex-call 'fa-c-chain (hons-list 0 arg1 arg2 arg3))))
    (& svex))
  ///

  (local
   (defthm fa-c-chain-commute-args
     (and (equal (fa-c-chain 0 y x z)
                 (fa-c-chain 0 x y z))
          (equal (fa-c-chain 0 x z y)
                 (fa-c-chain 0 x y z)))
     :hints (("Goal"
              :in-theory (e/d (fa-c-chain) ())))))

  (local
   (defthm |(FA-C-CHAIN 0 0 0 x)|
     (equal (FA-C-CHAIN 0 0 0 x)
            0)
     :hints (("Goal"
              :in-theory (e/d (FA-C-CHAIN c-spec) ())))))

  (local
   (defthm |(FA-C-CHAIN 0 0 x y)|
     (equal (FA-C-CHAIN 0 0 x y)
            (sv::4vec-bitand x y))
     :hints (("Goal"
              :in-theory (e/d (FA-C-CHAIN c-spec) ())))))

  (local
   (defthm c-spec-of-two-zeros
     (implies (bitp x)
              (and (equal (c-spec (list 0 x 0)) 0)
                   (equal (c-spec (list x 0 0)) 0)
                   (equal (c-spec (list 0 0 x)) 0)))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (local
   (defthm c-spec-of-one-zeros
     (implies (and (bitp x)
                   (bitp y))
              (and (equal (c-spec (list 0 x y)) (sv::4vec-bitand x y))
                   (equal (c-spec (list x y 0)) (sv::4vec-bitand x y))
                   (equal (c-spec (list y 0 x)) (sv::4vec-bitand x y))))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (local
   (defthm when-one-arg-of-fa-c-chain-is-1
     (implies (and (bitp x)
                   (bitp y))
              (and (equal (c-spec (list x 1 y))
                          (sv::4vec-bitor x y))
                   (equal (c-spec (list 1 x y))
                          (sv::4vec-bitor x y))
                   (equal (c-spec (list x y 1))
                          (sv::4vec-bitor x y))))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (local
   (defthm 3vec-fix-of-bitp
     (implies (bitp x)
              (equal (sv::3vec-fix x)
                     x))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (local
   (defthm SV::4VEC-PART-SELECt-of-bitp
     (implies (bitp x)
              (equal (sv::4vec-part-select 0 1 x)
                     x))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (defret <fn>-correct
    (implies (and (sv::svex-p svex)
                  (rp::rp-term-listp context)
                  (rp::valid-sc env-term a)
                  (rp::eval-and-all context a)
                  (rp::falist-consistent-aux env env-term)
                  (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config))
                  (svl::integerp-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->integerp-extns config))
                  (warrants-for-adder-pattern-match))
             (equal (sv::Svex-eval$ res (rp-evlt env-term a))
                    (sv::Svex-eval$ svex (rp-evlt env-term a))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (SV::SVEX-APPLY
                              ACL2::MERGE-LEXORDER
                              ACL2::MERGE-SORT-LEXORDER
                              SV::SVEX-CALL->FN
                              SV::SVEX-QUOTE->VAL
                              SV::SVEX-APPLY$
                              SV::SVEX-CALL->ARGS)
                             ())))))



(defines global-zero-fa-c-chain-extra-arg
  :verify-guards nil
  (define global-zero-fa-c-chain-extra-arg ((svex sv::svex-p)
                                            &key
                                            ((env) 'env)
                                            ((context rp-term-listp) 'context)
                                            ((config svl::svex-reduce-config-p) 'config))
    :measure (sv::Svex-count svex)
    :Returns (res sv::svex-p :hyp (sv::svex-p svex))
    (sv::svex-case
     svex
     :var svex
     :quote svex
     :call (zero-fa-c-chain-extra-arg
            (sv::Svex-call svex.fn
                           (global-zero-fa-c-chain-extra-arg-lst svex.args)))))
  (define global-zero-fa-c-chain-extra-arg-lst ((lst sv::svexlist-p)
                                                &key
                                                ((env) 'env)
                                                ((context rp-term-listp) 'context)
                                                ((config svl::svex-reduce-config-p) 'config))
    :measure (sv::Svexlist-count lst)
    :Returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
    (if (atom lst)
        nil
      (hons (global-zero-fa-c-chain-extra-arg (car lst))
            (global-zero-fa-c-chain-extra-arg-lst (cdr lst)))))
  ///
  (verify-guards global-zero-fa-c-chain-extra-arg-fn)
  (defret-mutual <fn>-is-correct
    (defret <fn>-correct
      (implies (and (sv::svex-p svex)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (warrants-for-adder-pattern-match))
               (equal (sv::Svex-eval$ res (rp-evlt env-term a))
                      (sv::Svex-eval$ svex (rp-evlt env-term a))))
      :fn global-zero-fa-c-chain-extra-arg)
    (defret <fn>-correct
      (implies (and (sv::svexlist-p lst)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (warrants-for-adder-pattern-match))
               (equal (sv::Svexlist-eval$ res-lst (rp-evlt env-term a))
                      (sv::Svexlist-eval$ lst (rp-evlt env-term a))))
      :fn global-zero-fa-c-chain-extra-arg-lst)
    :hints (("Goal"
             :do-not-induct t
             :expand ((global-zero-fa-c-chain-extra-arg svex)
                      (global-zero-fa-c-chain-extra-arg-lst lst)
                      (global-zero-fa-c-chain-extra-arg-lst nil))
             :in-theory (e/d () ()))))
  (memoize 'global-zero-fa-c-chain-extra-arg
           ;; :condition '(eq (sv::svex-kind svex) :call)
           )
  )


(define global-zero-fa-c-chain-extra-arg-alist ((alist sv::svex-alist-p)
                                                &key
                                                ((env) 'env)
                                                ((context rp-term-listp) 'context)
                                                ((config svl::svex-reduce-config-p) 'config))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
  (if (atom alist)
      nil
    (acons (caar alist)
           (global-zero-fa-c-chain-extra-arg (cdar alist))
           (global-zero-fa-c-chain-extra-arg-alist (cdr alist))))
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
             :induct (global-zero-fa-c-chain-extra-arg-alist alist)
             :in-theory (e/d (sv::svex-alist-eval$)
                             ())))))


(defsection fix-order-of-fa/ha-chain-args
  ;; After replacements,  ordered-ness of  arguments might change,  which might
  ;; prevent patterns  from being found  when looking more carefully.   So This
  ;; function goes around and reorders arguments in fa-s and ha-s arguments.

  (local
   (defthm nth-of-svex
     (implies (and (sv::svexlist-p x)
                   (natp i)
                   (< i (len x)))
              (sv::svex-p (nth i x)))))

  (local
   (defthm SVEX-COUNT-lemma
     (implies (and ;;(sv::Svex-p x)
               (or (EQUAL (CAR X) 'HA-S-CHAIN)
                   (EQUAL (CAR X) 'HA-c-CHAIN)
                   (EQUAL (CAR X) 'HA+1-S-CHAIN)
                   (EQUAL (CAR X) 'HA+1-c-CHAIN)))
              (and (< (SV::SVEX-COUNT (CADDR X))
                      (SV::SVEX-COUNT X))
                   (< (SV::SVEX-COUNT (CADR X))
                      (SV::SVEX-COUNT X))
                   (< (SV::SVEX-COUNT (CADddR X))
                      (SV::SVEX-COUNT X))))
     :hints (("Goal"
              :expand ((SV::SVEX-COUNT X))
              :in-theory (e/d (sv::svex-kind
                               SV::SVEX-CALL->ARGS)
                              ())))))

  (defines fix-order-of-fa/ha-chain-args
    :verify-guards nil

    (define fix-order-of-fa/ha-chain-args ((x sv::svex-p)
                                           &key
                                           ((env) 'env)
                                           ((context rp-term-listp) 'context)
                                           ((config svl::svex-reduce-config-p) 'config))
      :measure (sv::svex-count x)
      :returns (res)
      (sv::svex-case
       x
       :var x
       :quote x
       :call (case-match x
               (('fa-s-chain & & &)
                (b* ((lst1 (fix-order-of-fa/ha-chain-args-lst x.args))
                     (lst2 (acl2::merge-sort-lexorder lst1))
                     ((list first second third)
                      (list (nth 0 lst2) (nth 1 lst2) (nth 2 lst2)))
                     #|((when (and* (equal first 0)
                     (equal second 0)))
                     (create-unfloat-for-adder-fnc third))|#
                     ((when (integerp first))
                      ;; extract when one argument of fa-s-chain is 1 or 0.

                      (ex-adder-fnc-from-unfloat
                       (svl::bitand/or/xor-simple-constant-simplify
                        'sv::bitxor
                        first
                        (svl::bitand/or/xor-simple-constant-simplify 'sv::bitxor second third)))

                      #|(svl::svex-reduce-w/-env-apply
                      'sv::bitxor
                      (hons-list first
                      (svl::svex-reduce-w/-env-apply 'sv::bitxor
                      (hons-list second third))))|#))
                  (sv::svex-call x.fn lst2)))
               (('ha-s-chain a b)
                (b* (((when (or* (integerp a) (integerp b)))
                      (b* ((a (fix-order-of-fa/ha-chain-args a))
                           (b (fix-order-of-fa/ha-chain-args b)))
                        (ex-adder-fnc-from-unfloat
                         (svl::bitand/or/xor-simple-constant-simplify 'sv::bitxor a b))))
                     (lst1 (fix-order-of-fa/ha-chain-args-lst x.args))
                     (lst2 (acl2::merge-sort-lexorder lst1))
                     ((when (equal (nth 0 lst2) 0))
                      (create-unfloat-for-adder-fnc (nth 1 lst2))))
                  (sv::svex-call x.fn lst2)))
               (('ha-c-chain a b)
                (b* (((when (or* (integerp a) (integerp b)))
                      (b* ((a (fix-order-of-fa/ha-chain-args a))
                           (b (fix-order-of-fa/ha-chain-args b)))
                        (ex-adder-fnc-from-unfloat
                         (svl::bitand/or/xor-simple-constant-simplify 'sv::bitand a b))))
                     (lst1 (fix-order-of-fa/ha-chain-args-lst x.args))
                     (lst2 (acl2::merge-sort-lexorder lst1))
                     ((when (equal (nth 0 lst2) 0))
                      0))
                  (sv::svex-call x.fn lst2)))

               (('ha+1-c-chain a b)
                (b* (((when (or* (integerp a) (integerp b)))
                      (b* ((a (fix-order-of-fa/ha-chain-args a))
                           (b (fix-order-of-fa/ha-chain-args b)))
                        (ex-adder-fnc-from-unfloat
                         (svl::bitand/or/xor-simple-constant-simplify 'sv::bitor a b))))
                     (lst1 (fix-order-of-fa/ha-chain-args-lst x.args))
                     (lst2 (acl2::merge-sort-lexorder lst1)))
                  (sv::svex-call x.fn lst2)))

               (('ha+1-s-chain m a b)
                ;; first arg of ha+1-s-chain should be method, therefore, a constant at all times.
                (b* (((when (and*-exec (or* (integerp a)
                                            (integerp b))
                                       (natp m)))
                      (b* ((a (fix-order-of-fa/ha-chain-args a))
                           (b (fix-order-of-fa/ha-chain-args b)))
                        (cond ((= m 10) (ex-adder-fnc-from-unfloat
                                         (svl::bitand/or/xor-simple-constant-simplify 'sv::bitxor a b)))
                              ((= m 0) (sv::svex-call 'sv::bitnot
                                                      (hons-list
                                                       (ex-adder-fnc-from-unfloat
                                                        (svl::bitand/or/xor-simple-constant-simplify 'sv::bitxor a b)))))
                              (t (ex-adder-fnc-from-unfloat
                                  (svl::bitand/or/xor-simple-constant-simplify
                                   'sv::bitxor
                                   1
                                   (ex-adder-fnc-from-unfloat
                                    (svl::bitand/or/xor-simple-constant-simplify 'sv::bitxor a b))))))))
                     ((when (equal m 10))
                      (b* ((a (fix-order-of-fa/ha-chain-args a))
                           (b (fix-order-of-fa/ha-chain-args b))
                           (lst2 (acl2::merge-sort-lexorder (list a b))))
                        (svl::bitand/or/xor-simple-constant-simplify
                         'sv::bitxor 1 (sv::svex-call 'ha+1-s-chain (cons 1 lst2)))))
                     (lst1 (fix-order-of-fa/ha-chain-args-lst (cdr x.args)))
                     (lst2 (acl2::merge-sort-lexorder lst1)))
                  (sv::svex-call x.fn (cons (car x.args) lst2))))
               (('sv::bitxor & &)
                (b* ((first (fix-order-of-fa/ha-chain-args (first x.args)))
                     (second (fix-order-of-fa/ha-chain-args (second x.args))))
                  (svl::bitand/or/xor-simple-constant-simplify 'sv::bitxor first second)))
               (('sv::bitand & &)
                (b* ((first (fix-order-of-fa/ha-chain-args (first x.args)))
                     (second (fix-order-of-fa/ha-chain-args (second x.args))))
                  (svl::bitand/or/xor-simple-constant-simplify 'sv::bitand first second)))
               (&
                (b* ((res (sv::svex-call x.fn
                                         (fix-order-of-fa/ha-chain-args-lst x.args)))
                     (res (zero-fa-c-chain-extra-arg res))
                     (res (ex-adder-fnc-from-unfloat res)))
                  res)))))
    (define fix-order-of-fa/ha-chain-args-lst ((lst sv::svexlist-p)
                                               &key
                                               ((env) 'env)
                                               ((context rp-term-listp) 'context)
                                               ((config svl::svex-reduce-config-p) 'config))
      :measure (sv::svexlist-count lst)
      :returns (res )
      (if (atom lst)
          nil
        (hons (fix-order-of-fa/ha-chain-args (car lst))
              (fix-order-of-fa/ha-chain-args-lst (cdr lst)))))

    ///

    (defret len-of-<fn>
      (equal (len res)
             (len lst))
      :fn fix-order-of-fa/ha-chain-args-lst)

    (defret-mutual svex-p-of-<fn>
      (defret svex-p-of-<fn>
        (implies (sv::svex-p x)
                 (sv::svex-p res))
        :fn fix-order-of-fa/ha-chain-args)
      (defret svexlist-p-of-<fn>
        (implies (sv::svexlist-p lst)
                 (sv::svexlist-p res))
        :fn fix-order-of-fa/ha-chain-args-lst)
      :hints (("Goal"
               :in-theory (e/d (SV::SVEX-CALL->ARGS) ()))))

    (verify-guards fix-order-of-fa/ha-chain-args-fn
      :hints (("Goal"
               :in-theory (e/d (SV::SVEX-CALL->ARGS) ()))))

    (memoize 'fix-order-of-fa/ha-chain-args-fn
             ;; :condition '(eq (sv::svex-kind x) :call)
             )

    (local
     (defthm svex-eval$-of-natp
       (implies (natp x)
                (equal (SV::SVEX-EVAL$ x env)
                 x))
       :hints (("Goal"
                :in-theory (e/d (SV::SVEX-QUOTE->VAL) ())))))

    (defret-mutual <fn>-is-correct
      (defret <fn>-is-correct
        (implies (and (sv::svex-p x)
                      (rp::rp-term-listp context)
                      (rp::valid-sc env-term a)
                      (rp::eval-and-all context a)
                      (rp::falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (warrants-for-adder-pattern-match))
                 (equal (sv::svex-eval$ res (rp-evlt env-term a))
                        (sv::svex-eval$ x (rp-evlt env-term a))))
        :fn fix-order-of-fa/ha-chain-args)
      (defret <fn>-is-correct
        (implies (and (sv::svexlist-p lst)
                      (rp::rp-term-listp context)
                      (rp::valid-sc env-term a)
                      (rp::eval-and-all context a)
                      (rp::falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (warrants-for-adder-pattern-match))
                 (equal (sv::svexlist-eval$ res (rp-evlt env-term a))
                        (sv::svexlist-eval$ lst (rp-evlt env-term a))))
        :fn fix-order-of-fa/ha-chain-args-lst)
      :hints (("Goal"
               :do-not-induct t
               :expand (;;(warrants-for-adder-pattern-match)
                        (:free (fn args)
                               (sv::Svex-kind (cons fn args)))
                        (:free (args)
                               (sv::svex-apply$ 'ha-s-chain args))
                        (:free (args)
                               (sv::svex-apply$ 'ha+1-s-chain args))
                        (:free (args)
                               (sv::svex-apply$ 'ha+1-c-chain args))
                        (:free (args)
                               (sv::svex-apply$ 'ha-c-chain args))
                        (:free (args)
                               (sv::svex-apply$ 'fa-s-chain args))
                        (:free (args)
                               (sv::svex-apply 'sv::bitxor args))
                        (:free (args)
                               (sv::svex-apply 'sv::bitnot args))
                        (:free (args)
                               (sv::svex-apply 'sv::bitor args))
                        (:free (args)
                               (sv::svex-apply 'sv::bitand args))
                        (acl2::merge-sort-lexorder (cdr x))
                        (fix-order-of-fa/ha-chain-args-lst lst)
                        (fix-order-of-fa/ha-chain-args x))
               :in-theory (e/d (SV::SVEX-QUOTE->VAL
                                acl2::merge-lexorder
                                acl2::merge-sort-lexorder
                                ha-s-chain
                                ha+1-s-chain
                                ha+1-c-chain
                                fa-s-chain
                                HA-C-CHAIN
                                sv::svex-call->fn
                                sv::svex-call->args)
                               (nth
                                ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP
                                SV::SVEX-KIND$INLINE
                                ACL2::SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP
                                (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                                (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                                (:DEFINITION ACL2::APPLY$-BADGEP)
                                (:REWRITE ACL2::NATP-OF-CAR-WHEN-NAT-LISTP)
                                (:DEFINITION NAT-LISTP)
                                ACL2::INTEGERP-OF-CAR-WHEN-INTEGER-LISTP

                                warrants-for-adder-pattern-match
                                (:e warrants-for-adder-pattern-match)
                                ;;cons-equal
                                member-equal
                                VALID-SC
                                ;;evens
                                ;;cons-equal
                                ))))))

  (define fix-order-of-fa/ha-chain-args-alist ((alist sv::svex-alist-p)
                                               &key
                                               ((env) 'env)
                                               ((context rp-term-listp) 'context)
                                               ((config svl::svex-reduce-config-p) 'config))
    :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
    (if (atom alist)
        nil
      (acons (caar alist)
             (fix-order-of-fa/ha-chain-args (cdar alist))
             (fix-order-of-fa/ha-chain-args-alist (cdr alist))))
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
      :fn fix-order-of-fa/ha-chain-args-alist
      :hints (("Goal"
               :in-theory (e/d (SV::SVEX-ALIST-EVAL$) ()))))))
