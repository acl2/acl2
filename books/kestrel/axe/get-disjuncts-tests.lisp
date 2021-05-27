; Tests for get-disjuncts
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "get-disjuncts")
(include-book "make-term-into-dag-array-basic")
(include-book "dag-to-term")
(include-book "dag-array-printing")

(defund get-disjuncts-tester (term state)
  (declare (xargs :stobjs state
                  :mode :program))
  (b* ((term (translate-term term 'get-disjuncts-tester (w state)))
       ((mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (make-term-into-dag-array-basic term 'dag-array 'dag-parent-array nil))
       ((when erp) (er hard? 'get-disjuncts-tester "Error making term."))
       ((mv erp provedp disjuncts dag-array
            & ; dag-len
            & & & ;dag-parent-array dag-constant-alist dag-variable-alist
            )
        (get-disjuncts nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                       nil ;acc
                       nil ;negated-flg
                       t ;print
                       ))
       ((when erp) (er hard? 'get-disjuncts-tester "Error getting disjuncts.")))
    (if provedp
        :proved
      ;; todo: return these, as terms, instead of printing them:
      (print-dag-only-supporters-lst disjuncts 'dag-array dag-array))))

;; TODO: Get these into the build:
;; (get-disjuncts-tester 'x state)
;; (get-disjuncts-tester '(boolor x y) state)
;; (get-disjuncts-tester '(boolor x t) state)
;; (get-disjuncts-tester '(boolor t y) state)
;; (get-disjuncts-tester '(boolor x nil) state)
;; (get-disjuncts-tester '(boolor nil y) state)
;; (get-disjuncts-tester '(not x) state)
;; (get-disjuncts-tester '(not (not x)) state)
;; (get-disjuncts-tester '(not (booland x y)) state)
;; (get-disjuncts-tester '(not (booland nil y)) state)
;; (get-disjuncts-tester '(not (booland x nil)) state)
;; (get-disjuncts-tester '(not (booland t y)) state)
;; (get-disjuncts-tester '(not (booland x t)) state)
;; (get-disjuncts-tester '(not (boolor x y)) state) ;nothing to do
;; (get-disjuncts-tester '(not (booland (not x) (not y))) state)
;; (get-disjuncts-tester '(not (not t)) state)
;; (get-disjuncts-tester '(not (not nil)) state)
