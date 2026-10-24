; A verified clause processor that calls eliminate-irrelevance-clause
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; As a sanity check on the form of the main theorem, we use it to verify a
;; clause processor that eliminates irrelevant literals by calling the actual
;; ACL2 function eliminate-irrelevance-clause.

(include-book "irrelevance-proofs")

;; Irrelevance elimination applies only to goals being proved by induction,
;; as indicated by the pool of the prove-spec-var.
(defconst *irrelevance-clause-processor-pspv*
  (make prove-spec-var :pool '((being-proved-by-induction))))

(defund irrelevance-clause-processor (cl hint state)
  (declare (xargs :stobjs state
                  :verify-guards nil)
           (ignore hint))
  (mv-let (signal clauses ttree pspv)
    (eliminate-irrelevance-clause cl nil *irrelevance-clause-processor-pspv* nil state)
    (declare (ignore ttree pspv))
    (mv nil
        (if (eq signal 'hit)
            clauses
          (list cl))
        state)))

(defthm irrelevance-clause-processor-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (irrelevance-ev (conjoin-clauses (clauses-result (irrelevance-clause-processor cl hint state)))
                                a))
           (irrelevance-ev (disjoin cl) a))
  :rule-classes :clause-processor
  :hints (("Goal" :use (:instance irrelevance-ev-when-eliminate-irrelevance-clause
                                  (hist nil)
                                  (pspv *irrelevance-clause-processor-pspv*)
                                  (wrld nil))
           :in-theory (e/d (irrelevance-clause-processor)
                           (irrelevance-ev-when-eliminate-irrelevance-clause
                            eliminate-irrelevance-clause)))))

;; Examples:

(defstub p (y) t)
(defstub q (x) t)

;; The hypothesis (p y) shares no variables with the rest of the clause and
;; looks unlikely to be valid on its own (since it is a call of a function on
;; distinct variables), so it is dropped.
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
