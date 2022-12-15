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

(include-book "svex-eval-dollar-wog")
(include-book "svex-eval-wog-openers")


(local
 (in-theory (enable hons-get)))

;;;;; svex-eval$-wog




(def-rw-opener-error
  svex-eval$-wog_opener-error
  (svex-eval$-wog x env))


(def-rp-rule svex-eval$-wog-of-var
    (implies (and (svex-kind-wog-is-var x))
             (equal (svex-eval$-wog x env-wires)
                    (let ((entry (hons-get x env-wires)))
                      (if entry (cdr entry)
                        (sv::4vec-x)))))
    :hints (("Goal"
             :in-theory (e/d (;;svex-env-lookup
                              svex-eval$-wog
                              hons-get
                              svex-env-fastlookup-wog)
                             (hons-assoc-equal)))))

(progn

  (defun svex-kind-wog-is-quote (x)
    (declare (xargs :guard t))
    (and
     (eq (svex-kind-wog x) ':quote)))

  (def-rp-rule svex-eval$-wog-of-quoted
    (implies (svex-kind-wog-is-quote x)
             (equal (svex-eval$-wog x env)
                    x))
    :hints (("goal"
             :expand ((svex-eval$-wog x env)
                      (svex-eval$-wog nil env))
             :in-theory (e/d (sv::svex-quote->val
                              sv::4vec-p
                              svex-kind-wog
                              sv::svex-p
                              sv::svar-p
                              sv::4vec-fix) ())))))

(progn

  (def-rp-rule svexlist-eval$-wog-cons-def
    (equal (svexlist-eval$-wog (cons car-x cdr-x) env)
           (cons (svex-eval$-wog car-x env)
                 (svexlist-eval$-wog cdr-x
                                    env)))
    :hints (("Goal"
             :in-theory (e/d (svexlist-eval$-wog) ()))))

  (def-rp-rule svexlist-eval$-wog-nil-def
    (equal (svexlist-eval$-wog nil env)
           nil)
    :hints (("Goal"
             :in-theory (e/d (svexlist-eval$-wog) ())))))

(encapsulate
  nil

  ;; create rewrite rules for svex expressions..

  (local
   (defthm svex-eval$-wog-of-expression-lemma
     (implies (eq (svex-kind-wog x) ':call)
              (equal (svex-eval$-wog x env)
                     (svex-apply$-wog (car x)
                                     (svexlist-eval$-wog (cdr x)
                                                        env))))
     :hints (("goal"
              :in-theory (e/d (
                               svex-eval$-wog
                               4veclist-nth-safe
                               sv::svex-apply$
                               svex-kind
                               svex-eval$-wog

                               svexlist-eval$-wog)
                              (svex-apply$-is-svex-apply$-wog))))))


  (local
   (defthm 4vec-fix-of-4vec-fix
       (equal (4vec-fix (4vec-fix x))
              (4vec-fix x))
     :hints (("Goal"
              :in-theory (e/d (4vec-fix) ())))))

  (local
   (defun svex-apply$-cases-rw-fn-aux1 (args)
     (if (atom args)
         nil
       (cons `(svex-eval$-wog ,(car args) env)
             (svex-apply$-cases-rw-fn-aux1 (cdr args))))))

  (local
   (defun svex-apply$-cases-rw-fn-aux2 (args)
     (if (atom args)
         nil
         (cons `,(car args)
               (svex-apply$-cases-rw-fn-aux2 (cdr args))))))

  (local
   (defun svex-apply$-cases-rw-fn (svex-op-table)
     (if (atom svex-op-table)
         nil
       (cons
        (b* ((cur (car svex-op-table))
             (sv-fnc-name (car cur))
             (fnc-name (cadr cur))
             (args (caddr cur)))
          `(def-rp-rule ,(sa 'svex-apply$-wog sv-fnc-name 'rw)
               (implies t #|(and ,@(pairlis$ (repeat (len args) 'sv::svex-p)
                        (pairlis$  args nil)))||#
                        (and (equal (svex-eval$-wog (list ',sv-fnc-name ,@args) env)
                                    (,fnc-name ,@(svex-apply$-cases-rw-fn-aux1 args)))
                             (equal (svex-apply$-wog ',sv-fnc-name (list ,@args))
                                    (,fnc-name ,@(svex-apply$-cases-rw-fn-aux2 args)))))
             :hints (("Goal"
                      :in-theory (e/d ( ;SVEX-EVAL$-OF-EXPRESSION-LEMMA2
                                       (:e KEYWORDP)
                                       ,fnc-name
                                       4vec-fix-of-4vec-fix
                                       SV::4VEC-ONEHOT0
                                       CAR-CONS
                                       (:e zp)
                                       (:e FNSYM-FIX)
                                       sv::svex-p
                                       sv::FNSYM-P
                                       sv::SVEXLIST-P
                                       svexlist-eval$-wog
                                       sv::4VECLIST-NTH-SAFE
                                       svex-eval$-wog-of-expression-lemma
                                       nth
                                       svex-apply$-wog
                                       4vec-fix-wog-is-4vec-fix
                                       cdr-cons
                                       (:e eq)
                                       svex-kind-wog)
                                      ())))))
        (svex-apply$-cases-rw-fn (cdr svex-op-table))))))

  (def-rp-rule svex-apply$-wog_of-foreign-op
    (implies (and (fnsym-p fn)
                  (not (assoc-equal fn sv::*svex-op-table*)))
             (equal (svex-apply$-wog fn args)
                    (b* ((res (apply$ fn (SV::4VECLIST-FIX ARGS)))
                         (res (if (sv::4vec-p res) res (sv::4vec-x))))
                      res)))
    :lambda-opt t
    :hints
    (("goal"
      :in-theory (e/d (4vec-part-install 4vec-fix-of-4vec-fix
                       sv::4vec-onehot0 car-cons (:e zp)
                       (:e fnsym-fix)
                       svex-kind-wog
                       svex-p fnsym-p svexlist-p
                       svexlist-eval$-wog 4veclist-nth-safe
                       svex-eval$-wog-of-expression-lemma nth
                       svex-apply$-wog 4vec-fix-wog-is-4vec-fix
                       cdr-cons (:e eq)
                       svex-kind-wog
                       FNSYM-FIX)
                      nil)))
    :rule-classes :rewrite)

  (make-event
   ;; create rewrite rules for all the svex operations rewriting them to 4vec
   ;; functions. Example:
   ;; (defthm svex-apply$-wog_partinst_rw
   ;;   (implies
   ;;    t
   ;;    (and
   ;;     (equal
   ;;      (svex-eval$-wog (list 'sv::partinst
   ;;                            sv::lsb sv::width set::in sv::val)
   ;;                      env)
   ;;      (4vec-part-install (svex-eval$-wog sv::lsb env)
   ;;                         (svex-eval$-wog sv::width env)
   ;;                         (svex-eval$-wog set::in env)
   ;;                         (svex-eval$-wog sv::val env)))
   ;;     (equal
   ;;      (svex-apply$-wog 'sv::partinst
   ;;                       (list sv::lsb sv::width set::in sv::val))
   ;;      (4vec-part-install sv::lsb sv::width set::in sv::val)))))
   `(with-output
      :gag-mode nil
      :off :all
      :on (error)
      (progn
        ,@(svex-apply$-cases-rw-fn sv::*svex-op-table*)))))



  





(progn
  (def-rw-opener-error
    svexlist-list-eval$-wog-opener-error
    (svexlist-list-eval$-wog x env)
    :do-not-print (env))

  (def-rp-rule svexlist-list-eval$-wog-opener-nil
    (equal (svexlist-list-eval$-wog nil env)
           nil)
    :hints (("Goal"
             :in-theory (e/d (svexlist-list-eval$-wog) ()))))

  (def-rp-rule svexlist-list-eval$-wog-opener-cons
    (equal (svexlist-list-eval$-wog (cons x rest) env)
           (cons (svexlist-eval$-wog x env)
                 (svexlist-list-eval$-wog rest env)))
    :hints (("Goal"
             :in-theory (e/d (svexlist-list-eval$-wog) ())))))


(rp::def-rp-rule :disabled-for-acl2 t
 svex-alist-eval$-opener-nil
 (implies t
          (equal (sv::svex-alist-eval$ nil env)
                 nil))
 :hints (("Goal"
          :Expand (sv::svex-alist-eval$ nil env)
          :in-theory (e/d (SVEX-ALIST-EVAL) ()))))

(rp::def-rp-rule :disabled-for-acl2 t
 svex-alist-eval$-opener-cons
 (implies (force (sv::svar-p key))
          (equal (sv::svex-alist-eval$ (cons (cons key svex) rest) env)
                 (cons (cons key
                             (sv::svex-eval$ svex env))
                       (sv::svex-alist-eval$ rest env))))
 :hints (("Goal"
          :Expand (sv::svex-alist-eval$ (cons (cons key svex) rest) env)
          :in-theory (e/d () ()))))
