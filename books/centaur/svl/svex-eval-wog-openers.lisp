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

(include-book "svex-eval-wog")

(local
 (in-theory (enable hons-get)))

(def-rw-opener-error
  svex-eval-wog_opener-error
  (svex-eval-wog x env))

(def-rp-rule
 svex-env-fastlookup-wog-def
 (implies (syntaxp (consp (rp::ex-from-rp env)))
          (equal (svex-env-fastlookup-wog var env)
                 (let* ((look (hons-get var env)))
                   (if look (cdr look) (sv::4vec-x)))))
 :hints (("Goal"
          :in-theory (e/d (svex-env-fastlookup-wog) ()))))

(encapsulate
  nil

  (defun svex-kind-wog-is-var (x)
    (declare (xargs :guard t))
    (and
     (eq (svex-kind-wog x) ':var)))

  (def-rp-rule svex-eval-wog-of-var
    (implies (and (svex-kind-wog-is-var x))
             (equal (svex-eval-wog x env-wires)
                    (let ((entry (hons-get x env-wires)))
                      (if entry (cdr entry)
                        (sv::4vec-x)))))
    :hints (("Goal"
             :in-theory (e/d (;;svex-env-lookup
                              svex-eval-wog
                              hons-get
                              svex-env-fastlookup-wog)
                             (hons-assoc-equal))))))

(encapsulate
  nil

  (defun svex-kind-wog-is-quote (x)
    (declare (xargs :guard t))
    (and
     (eq (svex-kind-wog x) ':quote)))

  (def-rp-rule svex-eval-wog-of-quoted
    (implies (svex-kind-wog-is-quote x)
             (equal (svex-eval-wog x env)
                    x))
    :hints (("goal"
             :expand ((svex-eval-wog x env)
                      (svex-eval-wog nil env))
             :in-theory (e/d (sv::svex-quote->val
                              sv::4vec-p
                              svex-kind-wog
                              sv::svex-p
                              sv::svar-p
                              sv::4vec-fix) ())))))

(encapsulate
  nil

  (def-rp-rule svexlist-eval-wog-cons-def
    (equal (svexlist-eval-wog (cons car-x cdr-x) env)
           (cons (svex-eval-wog car-x env)
                 (svexlist-eval-wog cdr-x
                                    env)))
    :hints (("Goal"
             :in-theory (e/d (svexlist-eval-wog) ()))))

  (def-rp-rule svexlist-eval-wog-nil-def
    (equal (svexlist-eval-wog nil env)
           nil)
    :hints (("Goal"
             :in-theory (e/d (svexlist-eval-wog) ())))))

(encapsulate
  nil

  ;; create rewrite rules for svex expressions..

  (local
   (defthm svex-eval-wog-of-expression-lemma
     (implies (eq (svex-kind-wog x) ':call)
              (equal (svex-eval-wog x env)
                     (svex-apply-wog (car x)
                                     (svexlist-eval-wog (cdr x)
                                                        env))))
     :hints (("goal"
              :in-theory (e/d (
                               svex-eval-wog
                               4veclist-nth-safe
                               sv::svex-apply
                               svex-kind
                               svex-eval-wog

                               svexlist-eval-wog)
                              (svex-apply-is-svex-apply-wog))))))

  (local
   (defun svex-apply-cases-rw-fn-aux1 (args)
     (if (atom args)
         nil
       (cons `(4vec-fix-wog (svex-eval-wog ,(car args) env))
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
          `(def-rp-rule ,(sa 'svex-apply-wog sv-fnc-name 'rw)
             (implies t #|(and ,@(pairlis$ (repeat (len args) 'sv::svex-p)
                      (pairlis$  args nil)))||#
                      (equal (svex-eval-wog (list ',sv-fnc-name ,@args) env)
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
                                   svexlist-eval-wog
                                   sv::4VECLIST-NTH-SAFE
                                   svex-eval-wog-of-expression-lemma
                                   nth
                                   SVEX-APPLY-WOG
                                   4vec-fix-wog-is-4vec-fix
                                   cdr-cons
                                   (:e eq)
                                   svex-kind-wog)))))
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




(progn
  (def-rw-opener-error
    svexlist-list-eval-wog-opener-error
    (svexlist-list-eval-wog x env)
    :do-not-print (env))

  (def-rp-rule svexlist-list-eval-wog-opener-nil
    (equal (svexlist-list-eval-wog nil env)
           nil)
    :hints (("Goal"
             :in-theory (e/d (svexlist-list-eval-wog) ()))))

  (def-rp-rule svexlist-list-eval-wog-opener-cons
    (equal (svexlist-list-eval-wog (cons x rest) env)
           (cons (svexlist-eval-wog x env)
                 (svexlist-list-eval-wog rest env)))
    :hints (("Goal"
             :in-theory (e/d (svexlist-list-eval-wog) ())))))


(rp::def-rp-rule$
 t nil
 svex-alist-eval-opener-nil
 (implies t
          (equal (sv::svex-alist-eval nil env)
                 nil))
 :hints (("Goal"
          :Expand (sv::svex-alist-eval nil env)
          :in-theory (e/d () ()))))

(rp::def-rp-rule$
 t nil
 svex-alist-eval-opener-cons
 (implies (force (sv::svar-p key))
          (equal (sv::svex-alist-eval (cons (cons key svex) rest) env)
                 (cons (cons key
                             (sv::svex-eval svex env))
                       (sv::svex-alist-eval rest env))))
 :hints (("Goal"
          :Expand (sv::svex-alist-eval (cons (cons key svex) rest) env)
          :in-theory (e/d () ()))))
