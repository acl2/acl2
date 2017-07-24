; ACL2 interface to the ZZ system
; Copyright (C) 2011-2017 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")


(include-book "centaur/aig/eval-restrict" :dir :system)
(include-book "centaur/misc/fast-alists" :dir :system)
(include-book "zz-induction")


;; ZZV-SAT-FN -- constrained function that checks SAT on an AIG with optional
;; timeout.  Attach either ZZV-SAT-RAW, to just check SAT; ZZV-SAT-RECORD,
;; to check SAT and record proofs; or ZZV-SAT-VALIDATE to check recorded
;; proofs.
(encapsulate
  (((zzv-sat-fn * *) => *))
  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)
  (local (defun zzv-sat-fn (aig timeout)
           '(failed)))

  (defthm zzv-sat-fn-consp
    (consp (zzv-sat-fn aig timeout))
    :rule-classes :type-prescription)

  (defthm zzv-sat-fn-sat
    (implies (equal (car (zzv-sat-fn aig timeout)) 'sat)
             (aig-eval aig (cdr (zzv-sat-fn aig timeout)))))

  (defthm zzv-sat-fn-unsat
    (implies (equal (car (zzv-sat-fn aig timeout)) 'unsat)
             (not (aig-eval aig env)))))

;; Convenience macro to call ZZV-SAT-FN with the timeout optional.
(defmacro zzv-sat (aig &optional timeout)
  `(zzv-sat-fn ,aig ,timeout))

(add-macro-alias zzv-sat zzv-sat-fn)






;; ZZV-BATCH-SAT-FN -- constrained function that checks SAT on some AIGs with
;; optional timeout.  Attach either ZZV-BATCH-SAT-RAW-FN, to just check SAT;
;; ZZV-BATCH-SAT-RECORD-FN, to check SAT and record proofs; or
;; ZZV-BATCH-SAT-VALIDATE-FN to check recorded proofs.
(encapsulate
  (((zzv-batch-sat-fn * *) => *))
  (local (defun zzv-batch-sat-fn (aigs timeout)
           (if (atom aigs)
               nil
             (cons (zzv-sat-fn (car aigs) timeout)
                   (zzv-batch-sat-fn (cdr aigs) timeout)))))

  (defthm zzv-batch-sat-len
    (equal (len (zzv-batch-sat-fn aigs timeout))
           (len aigs)))

  (defthm zzv-batch-sat-fn-entries-consp
    (implies (member-equal entry (zzv-batch-sat-fn aigs timeout))
             (consp entry)))

  (defthm zzv-batch-sat-fn-entry-sat
    (implies (equal (car (nth n (zzv-batch-sat-fn aigs timeout))) 'sat)
             (aig-eval (nth n aigs)
                       (cdr (nth n (zzv-batch-sat-fn
                                    aigs timeout))))))

  (defthm zzv-batch-sat-fn-entry-unsat
    (implies (equal (car (nth n (zzv-batch-sat-fn aigs timeout))) 'unsat)
             (not (aig-eval (nth n aigs) env)))))

;; Convenience macro to call ZZV-SAT-FN with the timeout optional.
(defmacro zzv-batch-sat (aigs &optional timeout)
  `(zzv-batch-sat-fn ,aigs ,timeout))

(add-macro-alias zzv-batch-sat zzv-batch-sat-fn)





;; ZZV-MODELCHECK-FN -- constrained function that model-checks an FSM.  Attach
;; either ZZV-MODELCHECK-RAW-FN, to just modelcheck; ZZV-MODELCHECK-RECORD-FN,
;; to modelcheck and record proofs; or ZZV-MODELCHECK-VALIDATE-FN to check
;; recorded proofs.

(encapsulate
  (((zzv-modelcheck * * * * * *) => *))
  
  (local (defun zzv-modelcheck (stepfns prop initsts timeout max-depth engine)
           (declare (ignorable stepfns prop initsts timeout max-depth engine))
           '(aborted)))

  (defthm consp-zzv-modelcheck
    (consp (zzv-modelcheck stepfns prop initsts timeout max-depth engine)))
  
  (defthm consp-zzv-modelcheck-trace-when-refuted
    (let ((res (zzv-modelcheck stepfns prop initsts timeout max-depth engine)))
      (implies (equal (car res) 'refuted)
               (and (consp (cdr res))
                    (consp (cddr res))))))

  (defthm zzv-modelcheck-when-refuted
    (let ((res (zzv-modelcheck stepfns prop initsts timeout max-depth engine)))
      (implies (equal (car res) 'refuted)
               (and (equal (check-property stepfns prop (cadr res) (cddr res))
                           nil)
                    (alists-agree (alist-keys initsts) initsts (cadr res))))))

  (defthm zzv-modelcheck-when-proved
    (implies
     (and (equal (car (zzv-modelcheck stepfns prop initsts timeout max-depth engine))
                 'proved)
          (alists-agree (alist-keys initsts) initsts ctrex-initst))
     (check-property stepfns prop ctrex-initst ctrex-frames))))

