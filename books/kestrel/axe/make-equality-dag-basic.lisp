; The tactic-based prover
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This version uses dag-or-term-to-dag-basic, so, for term inputs, it
;; - uses the basic evaluator to evaluate ground terms
;; - does attempt to resolve IFs.
;; - does not handle embedded dags.

(include-book "make-equality-dag")
(include-book "dag-or-term-to-dag-basic")

;; Returns (mv erp dag).
(defund make-equality-dag-basic (dag-or-term1 dag-or-term2 different-vars-ok wrld)
  (declare (xargs :mode :program ; because dag-or-term-to-dag-basic calls translate
                  ))
  (b* (((mv erp dag1) (dag-or-term-to-dag-basic dag-or-term1 wrld))
       ((when erp) (mv erp nil))
       ((mv erp dag2) (dag-or-term-to-dag-basic dag-or-term2 wrld))
       ((when erp) (mv erp nil))
       (vars1 (dag-vars dag1)) ; todo: use a sort that does better with numbered vars
       (- (cw "Variables in DAG1: ~x0~%." vars1))
       (vars2 (dag-vars dag2))
       (- (cw "Variables in DAG2: ~x0~%." vars2))
       (dag1-only-vars (set-difference-eq vars1 vars2)) ;todo: optimize since sorted
       (dag2-only-vars (set-difference-eq vars2 vars1)) ;todo: optimize since sorted
       (- (and dag1-only-vars
               (cw "Variables in DAG1 only: ~X01.~%" dag1-only-vars nil)))
       (- (and dag2-only-vars
               (cw "Variables in DAG2 only: ~X01.~%" dag2-only-vars nil)))
       (different-varsp (not (perm vars1 vars2)))
       (- (and different-varsp
               different-vars-ok
               (cw "NOTE: The two dags have different variables.~%")))
       ((when (and different-varsp
                   (not different-vars-ok)))
        (mv (er hard? 'make-equality-dag-basic "The two dags have different variables.  Consider supplying :DIFFERENT-VARS-OK t." nil)
            nil)))
    (make-equality-dag dag1 dag2)))

(defund make-equality-dag-basic! (dag-or-term1 dag-or-term2 different-vars-ok wrld)
  (declare (xargs :mode :program ; todo
                  ))
  (mv-let (erp dag)
    (make-equality-dag-basic dag-or-term1 dag-or-term2 different-vars-ok wrld)
    (if erp
        (er hard? 'make-equality-dag-basic! "Error: ~x0." erp)
      dag)))
