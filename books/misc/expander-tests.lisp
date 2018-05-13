; Copyright (C) 2013, Regents of the University of Texas
; Originally written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book could benefit from additional tests.  Initially we include a test
; for the fix to pass along hints to forcing rounds.

(in-package "ACL2")

(include-book "expander")

(encapsulate () (local (progn

(defun f1 (x) (declare (ignore x)) t)
(defun f2 (x) (declare (ignore x)) t)
(defthm f1->f2
  (implies (force (f1 x))
           (equal (f2 x) t)))
(defthm f1-true
  (f1 x))
(in-theory (disable f1 (:t f1) f2 (:t f2) f1-true (:e tau-system)))
(make-event
 (er-let* ((val
            (defthm? foo
              (equal (cons (f2 x) x) ?)
              :hints (("[1]Goal" :in-theory (enable f1-true))))))
   (cond (val (value '(value-triple t)))
         (t (er soft 'expander-tests
                "Test failed!")))))
; Here is a low-level test:
(make-event (mv-let (erp val state)
              (tool2-fn '(cons (f2 x) x)
                        nil nil state
                        '(("[1]Goal" :in-theory (enable f1-true)))
                        t :all nil nil t 'top)
              (cond ((and (eq erp nil)
                          (equal val '(((:REWRITE F1-TRUE)
                                        (:REWRITE F1->F2)
                                        (:EXECUTABLE-COUNTERPART FORCE))
                                       (CONS 'T X))))
                     (value '(value-triple t)))
                    (t
                     (er soft 'top
                         "Test failed!")))))
)))
