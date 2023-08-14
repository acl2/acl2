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



(defsection simplify-to-find-fa-c-patterns

  ;; Goal is to attempting to simplify  svexes locally until they reveal a fa-c
  ;; pattern. If it does, then simplification  is left and the found pattern is
  ;; wrapped with "ID"  svex-op in order to prevent  other simplifications from
  ;; messing with it.

  (defconst *simplify-to-find-fa-c-patterns-limit*
    8)

  ;; memoizing this helps a little because of repetitive work
  (memoize 'svl::bitand/or/xor-cancel-repeated)

  (define simplify-to-find-fa-c-patterns-aux ((x sv::Svex-p)
                                              (limit natp)
                                              &key
                                              ((strength integerp) 'strength)
                                              (skip 'nil)
                                              ((skip-arg natp) '0)
                                              (inside-out 'inside-out)
                                              ((env) 'env)
                                              ((context rp-term-listp) 'context)
                                              ((config svl::svex-reduce-config-p) 'config))
    :returns (mv (res sv::svex-p :hyp (sv::svex-p x))
                 there-is-more)
    :guard (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config))
    :measure (acl2::nat-list-measure (list limit (if skip 0 1)))
    :verify-guards :after-returns
    :guard-debug t
    (if (zp limit)
        (mv x t)
      (sv::svex-case
       x
       :var (mv x nil)
       :quote (mv x nil)
       :call
       (cond ((and (or (equal x.fn 'sv::bitor)
                       (equal x.fn 'sv::bitand)
                       (equal x.fn 'sv::bitxor))
                   (svl::equal-len x.args 2))
              (b* (((when (and (not skip)
                               (not inside-out)
                               (= skip-arg 0)))
                    (let* ((new-x (svl::bitand/or/xor-cancel-repeated
                                   x.fn (first x.args) (second x.args)
                                   :leave-depth strength
                                   :nodes-to-skip-alist nil)))
                      (simplify-to-find-fa-c-patterns-aux new-x limit :skip t)))

                   ((mv arg1 there-is-more1)
                    (if (= skip-arg 1)
                        (mv (first x.args) nil)
                      (simplify-to-find-fa-c-patterns-aux (first x.args) (1- limit))))
                   ((mv arg2 there-is-more2)
                    (if (= skip-arg 2)
                        (mv (second x.args) nil)
                      (simplify-to-find-fa-c-patterns-aux (second x.args) (1- limit))))
                   (new-x (ex-adder-fnc-from-unfloat
                           (if (and inside-out
                                    (= skip-arg 0))
                               (svl::bitand/or/xor-cancel-repeated
                                x.fn arg1 arg2
                                :leave-depth strength
                                :nodes-to-skip-alist nil)
                             (svl::bitand/or/xor-simple-constant-simplify
                              x.fn arg1 arg2 :config config)))))
                (mv new-x (or there-is-more1
                              there-is-more2))))
             (t (mv x nil)))))
    ///
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
               (equal
                (sv::svex-eval$ res (rp-evlt env-term a))
                (sv::svex-eval$ x (rp-evlt env-term a))))
      :hints (("Goal"
               :in-theory (e/d (sv::svex-call->args
                                SV::SVEX-CALL->fn
                                SV::SVEX-APPLY)
                               (eval-and-all
                                rp::rp-term-listp
                                falist-consistent-aux))))))

  (define simplify-to-find-fa-c-patterns-iter ((x sv::Svex-p)
                                               (limit natp)
                                               &key
                                               ((strength integerp) 'strength)
                                               ((env) 'env)
                                               ((context rp-term-listp) 'context)
                                               ((config svl::svex-reduce-config-p) 'config))
    :guard (and (<= limit *simplify-to-find-fa-c-patterns-limit*)
                (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config)))
    :returns (mv (new-x sv::svex-p :hyp (sv::svex-p x))
                 (found))
    :prepwork ((local
                (use-arithmetic-5 t)))
    (if (zp limit)
        (mv x nil)
      (b* (((mv simplified there-is-more1)
            (simplify-to-find-fa-c-patterns-aux
             x (+ *simplify-to-find-fa-c-patterns-limit* (- limit) 1)
             :inside-out nil))
           ((when (equal simplified x)) ;; if the above simplification won't
            ;; change anything, then nothing below will (I guess?)
            (simplify-to-find-fa-c-patterns-iter x (1- limit)))
           (fa-c-patterns (look-for-fa-c-chain-pattern simplified))

           #|(- (and (case-match x (('sv::bitor
           ('sv::bitand
           ('sv::bitxor 1 ('sv::?* . &))
           ('sv::bitxor ('sv::bitxor . &) &))
           &)
           t))
           (cwe "x: ~p0, simplified: ~p1, fa-c-patterns: ~p2~%"
           x simplified fa-c-patterns)))|#

           ;; (- (and (not found)
           ;;         (case-match x
           ;;           (('sv::bitor ('sv::bitand ('sv::bitxor a b) c)
           ;;                        ('sv::bitand b ('sv::bitxor 1 ('sv::bitxor a b))))
           ;;            (list a b c)))
           ;;         (raise "WARNING!!! A known fa-c pattern is missed. For x: ~p0. New-x: ~p1" x new-x)))

           ((when fa-c-patterns)
            (mv simplified t))

           #|((unless (aggressive-find-adders-in-svex))
           (if there-is-more1
           (mv simplified nil)
           (simplify-to-find-fa-c-patterns-iter x (1- limit))))|#

           ;; Try also simplifying from inside-out
           ((mv simplified there-is-more2)
            (simplify-to-find-fa-c-patterns-aux
             x (+ *simplify-to-find-fa-c-patterns-limit* (- limit) 1)
             :inside-out t))
           (fa-c-patterns (look-for-fa-c-chain-pattern simplified))
           ((when fa-c-patterns)
            (mv simplified t))

           ;; Another attempt but this time skip one of the bitor args.
           ((mv simplified &)
            (simplify-to-find-fa-c-patterns-aux
             x (+ *simplify-to-find-fa-c-patterns-limit* (- limit) 1)
             :inside-out t
             :skip-arg 1))
           (fa-c-patterns (look-for-fa-c-chain-pattern simplified))
           ((when fa-c-patterns)
            (mv simplified t))

           ;;; Now skip simplification of the other arg.
           ((mv simplified &)
            (simplify-to-find-fa-c-patterns-aux
             x (+ *simplify-to-find-fa-c-patterns-limit* (- limit) 1)
             :inside-out t
             :skip-arg 2))
           (fa-c-patterns (look-for-fa-c-chain-pattern simplified))
           ((when fa-c-patterns)
            (mv simplified t))

           ((unless (or there-is-more1 there-is-more2))
            (mv simplified nil)))
        (simplify-to-find-fa-c-patterns-iter x (1- limit))))
    ///
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
               (equal
                (sv::svex-eval$ new-x (rp-evlt env-term a))
                (sv::svex-eval$ x (rp-evlt env-term a))))
      :fn simplify-to-find-fa-c-patterns-iter
      :hints (("Goal"
               :expand ((simplify-to-find-fa-c-patterns-iter x limit))
               :in-theory (e/d (simplify-to-find-fa-c-patterns-iter)
                               (eval-and-all
                                rp::rp-term-listp
                                falist-consistent-aux))))))

  (defines simplify-to-find-fa-c-patterns
    :verify-guards nil
    (define simplify-to-find-fa-c-patterns ((x sv::Svex-p)
                                            &key
                                            ((strength integerp) 'strength)
                                            ((env) 'env)
                                            ((context rp-term-listp) 'context)
                                            ((config svl::svex-reduce-config-p) 'config))
      :measure (sv::svex-count x)
      :guard (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config))
      :returns (res sv::svex-p :hyp (sv::svex-p x))
      (sv::svex-case
       x
       :var x
       :quote x
       :call
       (b* ((x.args (simplify-to-find-fa-c-patterns-list x.args))
            (x (sv::svex-call x.fn x.args))
            ((unless (equal x.fn 'sv::bitor)) ;; no need to look for fa-c patterns if x is not bitor.
             x)
            ((mv new-x found)
             (simplify-to-find-fa-c-patterns-iter x
                                                  *simplify-to-find-fa-c-patterns-limit*))

            
            (& (and (not found)
                    (case-match x
                      (('sv::bitor ('sv::bitand ('sv::bitxor a b) c)
                                   ('sv::bitand b ('sv::bitxor 1 ('sv::bitxor a b))))
                       (list a b c)))
                    (raise "WARNING!!! A known fa-c pattern is missed. For x: ~p0. New-x: ~p1" x new-x)))

            )
         ;; wrapping with id so that other simplification attempts do not corrupt this found pattern.
         (if found
             (sv::svex-call 'sv::id (hons-list new-x))
           x))))

    (define simplify-to-find-fa-c-patterns-list ((lst sv::Svexlist-p)
                                                 &key
                                                 ((strength integerp) 'strength)
                                                 ((env) 'env)
                                                 ((context rp-term-listp) 'context)
                                                 ((config svl::svex-reduce-config-p) 'config))
      :guard (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config))
      :measure (sv::svexlist-count lst)
      :returns (res sv::svexlist-p :hyp (sv::svexlist-p lst))
      (if (atom lst)
          nil
        (hons (simplify-to-find-fa-c-patterns (car lst))
              (simplify-to-find-fa-c-patterns-list (cdr lst)))))
    ///
    (verify-guards simplify-to-find-fa-c-patterns-fn)

    (memoize 'simplify-to-find-fa-c-patterns-fn
             ;; :condition '(eq (sv::svex-kind x) :call)
             )

    (local
     (defthm id-of-bitor-lemma
       (equal (sv::svex-apply 'id (list (sv::svex-apply 'sv::bitor args)))
              (sv::svex-apply 'sv::bitor args))
       :hints (("Goal"
                :in-theory (e/d (sv::svex-apply) ())))))

    (defret-mutual svex-eval$-correctness
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
                 (equal
                  (sv::svex-eval$ res (rp-evlt env-term a))
                  (sv::svex-eval$ x (rp-evlt env-term a))))
        :fn simplify-to-find-fa-c-patterns)
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
                 (equal
                  (sv::svexlist-eval$ res (rp-evlt env-term a))
                  (sv::svexlist-eval$ lst (rp-evlt env-term a))))
        :fn simplify-to-find-fa-c-patterns-list)
      :mutual-recursion simplify-to-find-fa-c-patterns
      :hints (("Goal"
               :in-theory (e/d ()
                               (eval-and-all
                                rp::rp-term-listp
                                falist-consistent-aux))))))

  (define simplify-to-find-fa-c-patterns-alist ((alist sv::Svex-alist-p)
                                                &key
                                                ((strength integerp) 'strength)
                                                ((env) 'env)
                                                ((context rp-term-listp) 'context)
                                                ((config svl::svex-reduce-config-p) 'config))
    :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
    :guard (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config))
    (if (atom alist)
        nil
      (acons (caar alist)
             (simplify-to-find-fa-c-patterns (hons-copy (cdar alist)))
             (simplify-to-find-fa-c-patterns-alist (cdr alist))))
    ///
    (defret <fn>-is-correct
      (implies (and (sv::svex-alist-p alist)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (warrants-for-adder-pattern-match))
               (equal
                (sv::svex-alist-eval$ res (rp-evlt env-term a))
                (sv::svex-alist-eval$ alist (rp-evlt env-term a))))
      :fn simplify-to-find-fa-c-patterns-alist
      :hints (("Goal"
               :in-theory (e/d (sv::svex-alist-eval$)
                               (eval-and-all
                                rp::rp-term-listp
                                falist-consistent-aux)))))))


;; (rp::simplify-to-find-fa-c-patterns #!SV'(bitxor other
;;                                                  (bitor (bitor (bitand x y) (bitor (bitand x y) (bitand y z)))
;;                                                         (bitand x z)))
;;                                     :context nil
;;                                     :env nil
;;                                     :strength 10
;;                                     :config nil)
;; returns:
;; (BITXOR OTHER
;;         (ID (BITOR (BITOR (BITAND X Y) (BITAND Y Z))
;;                    (BITAND X Z))))
