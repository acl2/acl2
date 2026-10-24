; Tests of the irrelevance elimination clause processor
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "irrelevance-clause-processor")

(defstub p (y) t)
(defstub q (x) t)

;; The literal (not (p y)) shares no variables with the rest of the clause.
;; It looks unlikely to be valid on its own, since it is the negation of a call
;; of a function on distinct variables (that is, the hypothesis (p y) is
;; presumably satisfiable), so it is dropped.
(assert-event
 (mv-let (signal clauses ttree pspv)
   (eliminate-irrelevance-clause '((not (p y)) (q (car x)))
                                 nil
                                 *irrelevance-clause-processor-pspv*
                                 nil
                                 state)
   (declare (ignore ttree pspv))
   (and (eq signal 'hit)
        (equal clauses '(((q (car x))))))))

(defun my-rev (x)
  (if (consp x)
      (append (my-rev (cdr x)) (list (car x)))
    nil))

;; The hint applies to the induction step, from which the irrelevant
;; hypothesis (p y) is dropped.
(defthm irrelevance-clause-processor-test
  (implies (p y)
           (equal (len (my-rev x)) (len x)))
  :hints (("Subgoal *1/1" :clause-processor (irrelevance-clause-processor clause nil state)))
  :rule-classes nil)
