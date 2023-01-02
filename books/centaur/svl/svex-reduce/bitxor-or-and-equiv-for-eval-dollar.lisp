; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
; Copyright (C) 2022 Intel Corporation
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
; Original author: Mertcan Temel <mert@centtech.com>

(in-package "SVL")

(include-book "centaur/sv/svex/eval-dollar" :dir :system)
(include-book "simplify-bitand-or-xor")

(include-book "projects/rp-rewriter/top" :dir :system)

(include-book "../fnc-defs")

(include-book "svex-reduce-apply")
(include-book "integerp-of-svex")
(include-book "width-of-svex")

(local
 (include-book "../4vec-lemmas"))

(local
 (include-book "../bits-sbits"))

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

(local
 (rp::fetch-new-events
  (include-book "ihs/quotient-remainder-lemmas" :dir :system)
  use-qr-lemmas
  ))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/equal-by-logbitp" :dir :system)
  use-equal-by-logbitp
  :disabled t))

(local
 (defthm svex-p-of-consed
   (implies (and (not (equal fn ':var))
                 (not (integerp fn)))
            (equal (svex-p (cons fn args))
                   (and (FNSYM-P fn)
                        (SVEXLIST-P args))))
   :hints (("Goal"
            :in-theory (e/d (svex-p) ())))))

(local
 (defthm svex-p-of-4vec-p
   (implies (4vec-p x)
            (svex-p x))
   :rule-classes :rewrite
   :hints (("Goal"
            :in-theory (e/d (svex-p 4vec-p) ())))))

(local
 (defthm sv::svex-eval$-opener-when-call
   (implies (and (syntaxp (and (consp fn)
                               (quotep fn)))
                 (fnsym-p fn))
            (equal (sv::svex-eval$ (cons fn args) env)
                   (SV::SVEX-APPLY$ fn
                                    (SVEXLIST-EVAL$ args env))))
   :hints (("Goal"
            :expand (sv::svex-eval$ (cons fn args) env)
            :in-theory (e/d (SVEX-CALL->FN
                             SVEX-VAR->NAME
                             SVEX-KIND
                             SVEX-CALL->ARGS)
                            ())))))

(local
 (defthm 4VEC-BITOR-of-1
   (equal (4VEC-BITOR -1 then)
          -1)
   :hints (("Goal"
            :expand (4VEC-BITOR -1 then)
            :in-theory (e/d (SV::3VEC-BITOR) ())))))

(defun svex-eval$-bitand-lst (lst env)
  (if (atom lst)
      -1
    (4vec-bitand (sv::svex-eval$ (car lst) env)
                 (svex-eval$-bitand-lst (cdr lst) env))))

(defun svex-eval$-bitxor-lst (lst env)
  (if (atom lst)
      0
    (sv::4vec-bitxor (sv::svex-eval$ (car lst) env)
                     (svex-eval$-bitxor-lst (cdr lst) env))))

(defun svex-eval$-bitor-lst (lst env)
  (if (atom lst)
      0
    (4vec-bitor (sv::svex-eval$ (car lst) env)
                (svex-eval$-bitor-lst (cdr lst) env))))

(local
 (defthm 3VEC-P-of-svex-eval$-BITOR-LST
   (sv::3vec-p (svex-eval$-bitor-lst lst env))))

(local
 (defthm 3VEC-P-of-Svex-Eval$-Bitand-Lst
   (sv::3vec-p (svex-eval$-bitand-lst lst env))))

(local
 (defthm 4VEC-P-of-svex-eval$-BITOR-LST
   (sv::4vec-p (svex-eval$-bitor-lst lst env))))

(local
 (defthm 4VEC-P-of-Svex-Eval$-Bitand-Lst
   (sv::4vec-p (svex-eval$-bitand-lst lst env))))

(local
 (defthm svex-eval$-bitor-lst-ored-with-a-member
   (implies (member-equal svex leaves)
            (equal (4vec-bitor (svex-eval$-bitor-lst leaves env)
                               (sv::svex-eval$ svex env))
                   (svex-eval$-bitor-lst leaves env)))
   :hints (("goal"
            :in-theory (e/d (svex-eval$-bitor-lst) ())))))

(defthm 4vec-bitand-of-the-same-2
  (equal (4vec-bitand x (4vec-bitand x a))
         (4vec-bitand x a)))

(local
 (defthm svex-eval$-bitand-lst-anded-with-a-member
   (implies (member-equal svex leaves)
            (equal (4vec-bitand (svex-eval$-bitand-lst leaves env)
                                (sv::svex-eval$ svex env))
                   (svex-eval$-bitand-lst leaves env)))
   :hints (("goal"
            :in-theory (e/d (svex-eval$-bitand-lst) ())))))

(defthm eval-bitor/bitand/bitxor-lst-of-append
  (and (equal (svex-eval$-bitor-lst (append x y) env)
              (4vec-bitor (svex-eval$-bitor-lst x env)
                          (svex-eval$-bitor-lst y env)))
       (equal (svex-eval$-bitand-lst (append x y) env)
              (4vec-bitand (svex-eval$-bitand-lst x env)
                           (svex-eval$-bitand-lst y env)))
       (equal (svex-eval$-bitxor-lst (append x y) env)
              (sv::4vec-bitxor (svex-eval$-bitxor-lst x env)
                               (svex-eval$-bitxor-lst y env))))
  :otf-flg t
  :hints (("goal"
           :induct (svex-eval$-bitor-lst x env)
           :do-not-induct t
           :expand ((svex-eval$-bitor-lst y env)
                    (svex-eval$-bitand-lst y env)
                    (svex-eval$-bitxor-lst y env))
           :in-theory (e/d (svex-eval$-bitxor-lst
                            svex-eval$-bitor-lst
                            svex-eval$-bitand-lst)
                           ()))))

(local
 (defthm svex-eval$-of-call-of-known-fncs
   (implies (assoc-equal (car svex) sv::*svex-op-table*)
            (equal (svex-eval$ svex env)
                   (svex-apply (car svex)
                               (svexlist-eval$ (cdr svex) env))))))
(local
 (in-theory (disable assoc-equal)))

(local
 (defthm svex-eval$-bitor-lst-of-bitand/or/xor-collect-leaves
   (and
    (equal
     (svex-eval$-bitor-lst (bitand/or/xor-collect-leaves svex 'sv::bitor) env)
     (sv::3vec-fix (sv::svex-eval$ svex env))))
   :hints (("goal"
            :expand ((:free (x)
                            (svex-apply 'bitor x)))
            :in-theory (e/d (svex-eval$-bitor-lst
                             svex-eval$-bitand-lst
                             bitand/or/xor-collect-leaves
                             SVEXLIST-EVAL$
                             )
                            ())))))

(local
 (defthm svex-eval$-bitand-lst-of-bitand/or/xor-collect-leaves
   (equal
    (svex-eval$-bitand-lst (bitand/or/xor-collect-leaves svex 'sv::bitand) env)
    (sv::3vec-fix (sv::svex-eval$ svex env)))
   :hints (("goal"
            :expand ((:free (x)
                            (svex-apply 'bitand x)))
            :in-theory (e/d (svex-eval$-bitor-lst
                             svex-eval$-bitand-lst
                             SVEXLIST-EVAL$
                             bitand/or/xor-collect-leaves)
                            ())))))
(local
 (defthm svex-eval$-bitor-lst-of-bitand/or/xor-collect-leaves-2
   (and (equal
         (sv::4vec-bitor other
                         (svex-eval$-bitor-lst (bitand/or/xor-collect-leaves svex 'sv::bitor) env)
                         )
         (sv::4vec-bitor (sv::svex-eval$ svex env)
                         other))
        (equal
         (sv::4vec-bitor (svex-eval$-bitor-lst (bitand/or/xor-collect-leaves svex 'sv::bitor) env)
                         other)
         (sv::4vec-bitor (sv::svex-eval$ svex env)
                         other)))
   :hints (("goal"
            :use ((:instance svex-eval$-bitor-lst-of-bitand/or/xor-collect-leaves))
            :in-theory (e/d ()
                            (svex-eval$-bitor-lst-of-bitand/or/xor-collect-leaves))))))

(local
 (defthm svex-eval$-bitand-lst-of-bitand/or/xor-collect-leaves-2
   (and (equal
         (sv::4vec-bitand other
                          (svex-eval$-bitand-lst (bitand/or/xor-collect-leaves svex 'sv::bitand) env)
                          )
         (sv::4vec-bitand (sv::svex-eval$ svex env)
                          other))
        (equal
         (sv::4vec-bitand (svex-eval$-bitand-lst (bitand/or/xor-collect-leaves svex 'sv::bitand) env)
                          other)
         (sv::4vec-bitand (sv::svex-eval$ svex env)
                          other)))
   :hints (("goal"
            :use ((:instance svex-eval$-bitand-lst-of-bitand/or/xor-collect-leaves))
            :in-theory (e/d ()
                            (svex-eval$-bitand-lst-of-bitand/or/xor-collect-leaves))))))

(local
 (defthm 4vec-p-of-EVAL-BITOR/and-LST
   (and (sv::4vec-p (svex-eval$-bitor-lst lst env))
        (sv::4vec-p (svex-eval$-bitand-lst lst env)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; bitxor/or/and-equiv

(defret <fn>-is-correct-for-eval$
  (and (implies (equal fn 'bitand)
                (equal (svex-eval$-bitand-lst leaves env)
                       (sv::3vec-fix (sv::svex-eval$ svex env))))
       (implies (equal fn 'bitor)
                (equal (svex-eval$-bitor-lst leaves env)
                       (sv::3vec-fix (sv::svex-eval$ svex env))))
       (implies (equal fn 'bitxor)
                (equal (svex-eval$-bitxor-lst leaves env)
                       (sv::3vec-fix (sv::svex-eval$ svex env)))))
  :fn bitand/or/xor-collect-leaves2
  :hints (("Goal"
           :in-theory (e/d (svex-apply
                            bitand/or/xor-collect-leaves2) ()))))

;; This is to append l1 and l2 in the same order as given in leaves.
(defret <fn>-is-correct-for-eval$
  (and (equal (svex-eval$-bitand-lst res env)
              (4vec-bitand (svex-eval$-bitand-lst l1 env)
                           (svex-eval$-bitand-lst l2 env)))
       (equal (svex-eval$-bitor-lst res env)
              (4vec-bitor (svex-eval$-bitor-lst l1 env)
                          (svex-eval$-bitor-lst l2 env)))
       (equal (svex-eval$-bitxor-lst res env)
              (sv::4vec-bitxor (svex-eval$-bitxor-lst l1 env)
                               (svex-eval$-bitxor-lst l2 env))))
  :fn bitxor/or/and-equiv-aux-append
  :hints (("goal"
           :expand ((svex-eval$-bitand-lst l2 env)
                    (svex-eval$-bitxor-lst l1 env)
                    (svex-eval$-bitxor-lst l2 env))
           :induct (bitxor/or/and-equiv-aux-append l1 l2 leaves)
           :in-theory (e/d (bitxor/or/and-equiv-aux-append
                            svex-eval$-bitand-lst
                            svex-eval$-bitxor-lst)
                           ()))))

;; (defund remove-pair-equal (lst)
;;   (declare (xargs :guard (true-listp lst)))
;;   (cond
;;    ((endp lst) nil)
;;    ((member-equal (car lst) (cdr lst))
;;     (remove-pair-equal (remove-equal (car lst) (cdr lst))))
;;    (t (cons-with-hint (car lst)
;;                       (remove-pair-equal (cdr lst))
;;                       lst))))

;; (local
;;  (defthm eval-bitxor-lst-of-remove-pair-equal-lemma
;;    (implies (MEMBER-EQUAL x lst)
;;             (EQUAL (svex-eval$-bitxor-lst (REMOVE-EQUAL x lst) ENV)
;;                    (SV::4VEC-BITXOR (sv::svex-eval$ x ENV)
;;                                     (svex-eval$-bitxor-lst lst ENV))))
;;    :hints (("Goal"
;;             :in-theory (e/d (remove-pair-equal) ())))))

;; (local
;;  (defthm eval-bitxor-lst-of-remove-pair-equal
;;    (equal (svex-eval$-bitxor-lst (remove-pair-equal lst) env)
;;           (svex-eval$-bitxor-lst lst env))
;;    :hints (("Goal"
;;             :in-theory (e/d (remove-pair-equal) ())))))

(local
 (defthm eval-bitor/and-lst-of-remove-duplicates-equal-lemma
   (implies (member-equal x lst)
            (and (equal (4VEC-BITAND (sv::svex-eval$ x ENV)
                                     (svex-eval$-bitand-lst lst ENV))
                        (svex-eval$-bitand-lst lst ENV))
                 (equal (4VEC-BITOR (sv::svex-eval$ x ENV)
                                    (svex-eval$-bitor-lst lst ENV))
                        (svex-eval$-bitor-lst lst ENV))))))

(local
 (defthm eval-bitor/and-lst-of-remove-duplicates-equal
   (and (equal (svex-eval$-bitor-lst (remove-duplicates-equal lst) env)
               (svex-eval$-bitor-lst lst env))
        (equal (svex-eval$-bitand-lst (remove-duplicates-equal lst) env)
               (svex-eval$-bitand-lst lst env)))
   :hints (("Goal"
            :in-theory (e/d (svex-eval$-bitor-lst
                             svex-eval$-bitand-lst
                             remove-duplicates-equal)
                            ())))))
(local
 (encapsulate
   nil
   (local
    (defthm eval$-bitxor-lst-of-remove-pair-equal-lemma
      (implies (member-equal x lst)
               (equal (sv::4vec-bitxor (svex-eval$ x env)
                                       (svex-eval$-bitxor-lst (remove-equal-once x lst) env))
                      (svex-eval$-bitxor-lst lst env)))
      :hints (("goal"
               :in-theory (e/d (remove-equal-once) ())))))
   (local
    (defthm eval$-bitxor-lst-of-remove-pair-equal-lemma-2
      (implies (member-equal x lst)
               (equal (svex-eval$-bitxor-lst lst env)
                      (sv::4vec-bitxor (svex-eval$ x env)
                                       (svex-eval$-bitxor-lst (remove-equal-once x lst) env))))
      :hints (("goal"
               :in-theory (e/d (remove-equal-once) ())))))

   (local
    (defthmd svex-eval$-when-integerp
      (implies (integerp x)
               (equal (sv::svex-eval$ x env)
                      x))
      :hints (("Goal"
               :in-theory (e/d (sv::svex-eval
                                sv::svex-kind
                                SV::SVEX-QUOTE->VAL
                                )
                               ())))))

   (defthm eval$-bitxor-lst-of-remove-pair-equal
     (equal (svex-eval$-bitxor-lst (remove-pair-equal lst) env)
            (svex-eval$-bitxor-lst lst env))
     :hints (("Goal"
              :in-theory (e/d (svex-eval$-when-integerp
                               remove-pair-equal)
                              (eval$-bitxor-lst-of-remove-pair-equal-lemma)))
             ))))

(defret <fn>-is-correct-for-eval$
  (and (implies (and (equal fn 'bitand)
                     valid)
                (and (equal (svex-eval$-bitand-lst leaves2 env)
                            (sv::3vec-fix (sv::svex-eval$ svex env)))
                     (equal (svex-eval$-bitand-lst (remove-duplicates-equal leaves2) env)
                            (sv::3vec-fix (sv::svex-eval$ svex env)))))
       (implies (and (equal fn 'bitor)
                     valid)
                (and (equal (svex-eval$-bitor-lst leaves2 env)
                            (sv::3vec-fix (sv::svex-eval$ svex env)))
                     (equal (svex-eval$-bitor-lst (remove-duplicates-equal leaves2) env)
                            (sv::3vec-fix (sv::svex-eval$ svex env)))))
       (implies (and (equal fn 'bitxor)
                     valid)
                (and (equal (svex-eval$-bitxor-lst leaves2 env)
                            (sv::3vec-fix (sv::svex-eval$ svex env)))
                     (equal (svex-eval$-bitxor-lst (remove-pair-equal leaves2) env)
                            (sv::3vec-fix (sv::svex-eval$ svex env))))))
  :fn bitxor/or/and-equiv-aux
  :hints (("Goal"
           :in-theory (e/d (SVEX-APPLY
                            bitxor/or/and-equiv-aux)
                           (ASSOC-EQUAL
                            true-listp))))
  )

(encapsulate
  nil
  (local
   (defthm eval-bitor/and-lst-of-remove-duplicates-equal-2
     (implies (syntaxp (and (consp lst)
                            (equal (car lst) 'binary-append)))
              (and (equal (svex-eval$-bitor-lst (remove-duplicates-equal lst) env)
                          (svex-eval$-bitor-lst lst env))
                   (equal (svex-eval$-bitand-lst (remove-duplicates-equal lst) env)
                          (svex-eval$-bitand-lst lst env))
                   (equal (svex-eval$-bitxor-lst (remove-pair-equal lst) env)
                          (svex-eval$-bitxor-lst lst env))))))

  (local
   (in-theory (e/d (svex-apply
                    bitxor/or/and-equiv-iter)
                   (eval-bitor/and-lst-of-remove-duplicates-equal
                    eval$-bitxor-lst-of-remove-pair-equal
                    bitxor/or/and-equiv-aux-is-correct))))

  (defret <fn>-is-correct-for-eval$
    (and (implies (and (or (equal fn 'bitand)
                           (equal fn 'bitor)
                           (equal fn 'bitxor))
                       equiv)
                  (equal (sv::svex-eval$ `(,fn ,arg1 ,arg2) env)
                         (sv::3vec-fix (sv::svex-eval$ other-svex env))))
         )
    :fn bitxor/or/and-equiv-iter
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance bitxor/or/and-equiv-aux-is-correct-for-eval$
                                    (svex other-svex)
                                    (fn 'bitand)
                                    (leaves (remove-duplicates-equal
                                             (append (mv-nth 0
                                                             (bitand/or/xor-collect-leaves2 arg1 'bitand
                                                                                            cnt))
                                                     (mv-nth 0
                                                             (bitand/or/xor-collect-leaves2 arg2 'bitand
                                                                                            cnt))))))
                         (:instance bitxor/or/and-equiv-aux-is-correct-for-eval$
                                    (svex other-svex)
                                    (fn 'bitxor)
                                    (leaves (remove-pair-equal
                                             (append (mv-nth 0
                                                             (bitand/or/xor-collect-leaves2 arg1 'bitxor
                                                                                            cnt))
                                                     (mv-nth 0
                                                             (bitand/or/xor-collect-leaves2 arg2 'bitxor
                                                                                            cnt))))))
                         (:instance bitxor/or/and-equiv-aux-is-correct-for-eval$
                                    (svex other-svex)
                                    (fn 'bitor)
                                    (leaves (remove-duplicates-equal
                                             (append (mv-nth 0
                                                             (bitand/or/xor-collect-leaves2 arg1 'bitor
                                                                                            cnt))
                                                     (mv-nth 0
                                                             (bitand/or/xor-collect-leaves2 arg2 'bitor
                                                                                            cnt))))))
                         ))))))

(defret <fn>-is-correct-for-eval$
  (implies (and equiv
                (or (equal fn 'bitand)
                    (equal fn 'bitor)
                    (equal fn 'bitxor)))
           (equal (sv::svex-eval$ other-svex env)
                  (sv::svex-eval$ `(,fn ,arg1 ,arg2) env)))
  :fn bitxor/or/and-equiv
  :hints (("Goal"
           :in-theory (e/d (svex-apply
                            bitxor/or/and-equiv) ())))
  :rule-classes (:rewrite))

;; (bitxor/or/and-equiv 'bitor 'e '(bitor f (bitor d (bitor a (bitor c b))))
;;                      '(bitor (bitor (bitor a b) c) (bitor d (bitor e f))))

;; (bitxor/or/and-equiv 'bitor '(bitor a b) 'c
;;                      '(bitor (bitor a c) b))

;; (bitxor/or/and-equiv 'bitor '(bitor a b) '(bitor a c)
;;                      '(bitor (bitor a (bitor a (bitor a c))) b))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
