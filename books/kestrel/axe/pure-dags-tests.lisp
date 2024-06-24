; Tests of DAG purity checking
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pure-dags")
(include-book "make-term-into-dag-simple")

;; Just used for testing?
(defund term-is-purep (term)
  (declare (xargs :guard (pseudo-termp term)))
  (b* (((mv erp dag-or-quotep) (make-term-into-dag-simple term)))
    (if erp
        (er hard? 'term-is-purep "Error making term into dag.")
      (if (quotep dag-or-quotep)
          (er hard? 'term-is-purep "Unexpected constant: ~x0." dag-or-quotep)
        (dag-is-purep dag-or-quotep)))))

(assert-event (term-is-purep '(bvxor '32 x y)))

;; size not known:
(assert-event (not (term-is-purep '(bvxor size x y))))

;; todo: should this not be pure?!:
;; (term-is-purep '(equal x y))
