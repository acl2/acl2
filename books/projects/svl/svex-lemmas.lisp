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

(include-book "svl")

(def-rw-opener-error
  svex-eval_opener-error
  (svex-eval x env))

(local
 (defthm svex-eval-of-var-lemma
   (implies (and (sv::svex-env-p env-wires)
                 (hons-get x env-wires))
            (sv::4vec-p (cdr (hons-get x env-wires))))))

(encapsulate
  nil

  (defun svex-kind-is-var (x)
    (declare (xargs :guard t))
    (and
     (svex-p x)
     (eq (svex-kind x) ':var)))

  (memoize 'svex-kind-is-var)

  (rp::defthm-lambda
   svex-eval-of-var
   (implies (and (svex-kind-is-var x);(equal (svex-kind x) ':var)
                 (svex-env-p env-wires))
            (equal (svex-eval x env-wires)
                   (let ((entry (hons-get (svex-var->name x) env-wires)))
                     (if entry
                         (cdr (hons-get (svex-var->name x) env-wires))
                       (sv::4vec-x)))))
   :hints (("Goal"
            :in-theory (e/d (sv::svex-env-lookup
                             sv::svex-eval)
                            (hons-get)))))

  (defthmd svex-eval-of-var-side-cond
    (implies (and (svex-kind-is-var x)
                  (sv::svex-env-p env-wires))
             (sv::4vec-p
              (RP::SVEX-EVAL-OF-VAR_LAMBDA-FNC_0
               (HONS-GET (SV::SVEX-VAR->NAME$INLINE X)
                         ENV-WIRES)
               ENV-WIRES X)))
    :hints (("Goal"
             :in-theory (e/d (sv::svex-env-lookup
                              sv::svex-eval)
                             (hons-get)))))

  (rp-attach-sc svex-eval-of-var
                svex-eval-of-var-side-cond))

(defun svex-kind-is-quote (x)
  (declare (xargs :guard t))
  (and
   (svex-p x)
   (eq (svex-kind x) ':quote)))

(memoize 'svex-kind-is-quote)

(defthm svex-eval-of-quoted
  (implies (svex-kind-is-quote x)
           (equal (sv::svex-eval x env)
                  (if (consp x) (cadr x) x)))
  :hints (("goal"
           :in-theory (e/d (sv::svex-quote->val
                            sv::4vec-p
                            sv::svex-kind
                            sv::svex-p
                            sv::svar-p
                            sv::4vec-fix) ()))))

(defthm svexlist-eval-cons-def
  (equal (sv::svexlist-eval (cons car-x cdr-x) env)
         (cons (sv::svex-eval car-x env)
               (sv::svexlist-eval cdr-x
                                  env))))

(defthm svexlist-eval-nil-def
  (equal (sv::svexlist-eval nil env)
         nil))

(encapsulate
  nil

  ;; create rewrite rules for svex expressions..

  (local
   (defthm svex-eval-of-expression-lemma
     (implies (eq (sv::svex-kind x) ':call)
              (equal (sv::svex-eval x env)
                     (sv::svex-apply-cases
                      (sv::svex-call->fn x)
                      (sv::svexlist-eval (sv::svex-call->args x)
                                         env))))
     :hints (("Goal"
              :in-theory (e/d (sv::svex-apply) ())))))

  (local
   (defthm svex-call->fn-is-car-x
     (implies (and (eq (sv::svex-kind x) ':call)
                   (sv::svex-p x))
              (equal (sv::svex-call->fn x)
                     (car x)))
     :hints (("Goal"
              :in-theory (e/d (sv::SVEX-KIND
                               sv::SVEX-P
                               sv::FNSYM-FIX
                               sv::FNSYM-P
                               sv::SVEX-CALL->FN) ())))))

  (local
   (defthm svex-call->args-is-cdr-x
     (implies (and (eq (sv::svex-kind x) ':call)
                   (sv::svex-p x))
              (equal (sv::svex-call->args x)
                     (cdr x)))
     :hints (("Goal"
              :in-theory (e/d (sv::SVEX-KIND
                               sv::SVEX-CALL->ARGS
                               sv::SVEX-P
                               sv::FNSYM-FIX
                               sv::FNSYM-P
                               sv::SVEX-CALL->FN) ())))))

  (local
   (defthm svex-eval-of-expression-lemma2
     (implies (and (eq (svex-kind x) ':call)
                   (svex-p x))
              (equal (svex-eval x env)
                     (svex-apply-cases
                      (car x)
                      (svexlist-eval (cdr x)
                                     env))))
     :hints (("Goal"
              :use ((:instance svex-eval-of-expression-lemma))
              :in-theory (e/d (sv::svex-call->fn)
                              (sv::SVEX-APPLY-CASES-FN
                               sv::svexlist-eval
                               svex-eval-of-expression-lemma))))))

  (local
   (defun svex-apply-cases-rw-fn-aux1 (args)
     (if (atom args)
         nil
       (cons `(sv::4vec-fix (sv::svex-eval ,(car args) env))
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
          `(defthm ,(sa 'svex-apply sv-fnc-name 'rw)
             (implies (and ,@(pairlis$ (repeat (len args) 'sv::svex-p)
                                         (pairlis$  args nil)))
                      (equal (sv::svex-eval (list ',sv-fnc-name ,@args) env)
                             (,fnc-name ,@(svex-apply-cases-rw-fn-aux1 args))))
             :hints (("Goal"
                      :in-theory '(SVEX-EVAL-OF-EXPRESSION-LEMMA2
                                   (:e KEYWORDP)
                                   CAR-CONS
                                   (:e zp)
                                   sv::svex-p
                                   sv::FNSYM-P
                                   sv::SVEXLIST-P
                                   sv::SVEXLIST-EVAL
                                   sv::4VECLIST-NTH-SAFE
                                   nth
                                   cdr-cons
                                   (:e eq)
                                   sv::svex-kind)))))
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

(in-theory (disable sv::4VEC-P-WHEN-MAYBE-4VEC-P
                    sv::SVEX-P-WHEN-MAYBE-SVEX-P))

(in-theory (enable svex-eval_opener-error))
