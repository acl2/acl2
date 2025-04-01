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

;; See also make-equality-dag-basic

(include-book "make-equality-dag")
(include-book "dagify0") ; reduce?, for dag-or-term-to-dag

;; Returns (mv erp dag).
;; todo: make and use a make-equality-dag-basic that doesn't depend on skip-proofs
(defun make-equality-dag-gen (dag-or-term1 ; may be an untranslated term
                              dag-or-term2 ; may be an untranslated term
                              different-vars-ok
                              wrld)
  (declare (xargs :guard (booleanp different-vars-ok)
                  :mode :program ; because dag-or-term-to-dag translates
                  ))
  (b* (((mv erp dag1) (dag-or-term-to-dag dag-or-term1 wrld))
       ((when erp) (mv erp nil))
       ((mv erp dag2) (dag-or-term-to-dag dag-or-term2 wrld))
       ((when erp) (mv erp nil))
       (vars1 (merge-sort-symbol< (dag-vars dag1)))
       (- (cw "Variables in DAG1: ~x0~%" vars1))
       (vars2 (merge-sort-symbol< (dag-vars dag2)))
       (- (cw "Variables in DAG2: ~x0~%" vars2))
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
        (mv (er hard? 'make-equality-dag-gen "The two dags have different variables.  Consider supplying :DIFFERENT-VARS-OK t." nil)
            nil)))
    (make-equality-dag dag1 dag2)))

(defun make-equality-dag-gen! (dag-or-term1 dag-or-term2 different-vars-ok wrld)
  (declare (xargs :mode :program ; because ultimately calls translate
                  ))
  (mv-let (erp dag)
    (make-equality-dag-gen dag-or-term1 dag-or-term2 different-vars-ok wrld)
    (if erp
        (er hard? 'make-equality-dag-gen! "Error: ~x0." erp)
      dag)))
