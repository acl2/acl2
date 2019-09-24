; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>

(in-package "SVL")

(include-book "svex-eval2")

(def-rw-opener-error
  svex-eval2_opener-error
  (svex-eval2 x env))

#|(local
 (defthm svex-eval-of-var-lemma
   (implies (and (sv::svex-env-p env-wires)
                 (hons-get x env-wires))
            (sv::4vec-p (cdr (hons-get x env-wires))))))||#

(encapsulate
  nil

  (defun svex-kind2-is-var (x)
    (declare (xargs :guard t))
    (and
     (eq (svex-kind2 x) ':var)))

  (defthm svex-eval2-of-var
    (implies (and (svex-kind2-is-var x))
             (equal (svex-eval2 x env-wires)
                    (let ((entry (hons-get x env-wires)))
                      (if entry (cdr entry)
                        (sv::4vec-x)))))
    :hints (("Goal"
             :in-theory (e/d (;;svex-env-lookup
                              svex-eval2
                              SVEX-ENV-FASTLOOKUP2)
                             (hons-get))))))

(encapsulate
  nil

  (defun svex-kind2-is-quote (x)
    (declare (xargs :guard t))
    (and
     (eq (svex-kind2 x) ':quote)))

  (defthm svex-eval2-of-quoted
    (implies (svex-kind2-is-quote x)
             (equal (svex-eval2 x env)
                    (COND ((ATOM X) X)
                          ((ATOM (CDR X)) (SV::4VEC-X))
                          (T (CADR X)))))
    :hints (("goal"
             :expand ((svex-eval2 x env)
                      (SVEX-EVAL2 NIL ENV))
             :in-theory (e/d (sv::svex-quote->val
                              sv::4vec-p
                              svex-kind2
                              sv::svex-p
                              sv::svar-p
                              sv::4vec-fix) ())))))

(encapsulate
  nil

  (defthm svexlist-eval2-cons-def
    (equal (svexlist-eval2 (cons car-x cdr-x) env)
           (cons (svex-eval2 car-x env)
                 (svexlist-eval2 cdr-x
                                 env)))
    :hints (("Goal"
             :in-theory (e/d (svexlist-eval2) ()))))

  (defthm svexlist-eval2-nil-def
    (equal (svexlist-eval2 nil env)
           nil)
    :hints (("Goal"
             :in-theory (e/d (svexlist-eval2) ())))))

(encapsulate
  nil

  ;; create rewrite rules for svex expressions..

  (local
   (defthm svex-eval2-of-expression-lemma
     (implies (eq (svex-kind2 x) ':call)
              (equal (svex-eval2 x env)
                     (SVEX-APPLY2 (car x)
                                  (svexlist-eval2 (cdr x)
                                                  env))))
     :hints (("Goal"
              :in-theory (e/d (
                               SVEX-EVAL2
                               4VECLIST-NTH-SAFE
                               SV::SVEX-APPLY
                               SVEX-KIND
                               SVEX-EVAL2

                               svexlist-eval2)
                              (SVEX-APPLY2-IS-SVEX-APPLY))))))

  #|(local
  (defthm svex-call2->fn-is-car-x
  (implies (and (eq (svex-kind2 x) ':call))
  (equal (sv::svex-call->fn x)
  (car x)))
  :hints (("Goal"
  :in-theory (e/d (svex-kind2
  sv::SVEX-P
  sv::FNSYM-FIX
  sv::FNSYM-P
  sv::SVEX-CALL->FN) ())))))||#

  #|(local
   (defthm svex-call->args-is-cdr-x
     (implies (and (eq (svex-kind2 x) ':call)
                   (sv::svex-p x))
              (equal (sv::svex-call->args x)
                     (cdr x)))
     :hints (("Goal"
              :in-theory (e/d (svex-kind2
                               sv::SVEX-CALL->ARGS
                               sv::SVEX-P
                               sv::FNSYM-FIX
                               sv::FNSYM-P
                               sv::SVEX-CALL->FN) ())))))||#

  #|(local
   (defthm svex-eval-of-expression-lemma2
     (implies (and (eq (svex-kind x) ':call)
                   (svex-p x))
              (equal (svex-eval x env)
                     (svex-apply-cases
                      (car x)
                      (svexlist-eval (cdr x)
                                     env))))
     :hints (("Goal"
              :use ((:instance svex-eval2-of-expression-lemma))
              :in-theory (e/d (sv::svex-call->fn)
                              (sv::SVEX-APPLY-CASES-FN
                               svexlist-eval2
                               svex-eval2-of-expression-lemma))))))||#

  (local
   (defun svex-apply-cases-rw-fn-aux1 (args)
     (if (atom args)
         nil
       (cons `(4vec-fix2 (svex-eval2 ,(car args) env))
             (svex-apply-cases-rw-fn-aux1 (cdr args))))))

  (local
   (defun svex-apply-cases-rw-fn (svex-op-table)
     (if (atom svex-op-table)
         nil
       (cons
        (b* ((cur (car svex-op-table))
             (sv-fnc-name (car cur))
             (fnc-name (cadr cur))
             (args (caddr cur)))
          `(defthm ,(sa 'svex-apply2 sv-fnc-name 'rw)
             (implies t #|(and ,@(pairlis$ (repeat (len args) 'sv::svex-p)
                                       (pairlis$  args nil)))||#
                      (equal (svex-eval2 (list ',sv-fnc-name ,@args) env)
                             (,fnc-name ,@(svex-apply-cases-rw-fn-aux1 args))))
             :hints (("Goal"
                      :in-theory '(;SVEX-EVAL-OF-EXPRESSION-LEMMA2
                                   (:e KEYWORDP)
                                   CAR-CONS
                                   (:e zp)
                                   (:e FNSYM-FIX)
                                   sv::svex-p
                                   sv::FNSYM-P
                                   sv::SVEXLIST-P
                                   svexlist-eval2
                                   sv::4VECLIST-NTH-SAFE
                                   svex-eval2-of-expression-lemma
                                   nth
                                   SVEX-APPLY2
                                   4vec-fix2-is-4vec-fix
                                   cdr-cons
                                   (:e eq)
                                   svex-kind2)))))
        (svex-apply-cases-rw-fn (cdr svex-op-table))))))

  (make-event
   ;; create rewrite rules for all the svex operations rewriting them to 4vec
   ;; functions. Example:
   ;; (defthm
   ;;   svex-apply_partinst_rw
   ;;   (implies
   ;;    (and (sv::svex-p sv::lsb)
   ;;         (sv::svex-p sv::width)
   ;;         (sv::svex-p set::in)
   ;;         (sv::svex-p sv::val))
   ;;    (equal
   ;;     (sv::svex-eval (list 'sv::partinst
   ;;                          sv::lsb sv::width set::in sv::val)
   ;;                    env)
   ;;     (sv::4vec-part-install
   ;;      (sv::4vec-fix (sv::svex-eval sv::lsb env))
   ;;      (sv::4vec-fix (sv::svex-eval sv::width env))
   ;;      (sv::4vec-fix (sv::svex-eval set::in env))
   ;;      (sv::4vec-fix (sv::svex-eval sv::val env))))))
   `(with-output
      :gag-mode nil
      :off :all
      (progn
        ,@(svex-apply-cases-rw-fn sv::*svex-op-table*)))))
