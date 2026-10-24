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

;; For examples, see irrelevance-clause-processor-tests.lisp.
