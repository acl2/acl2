; Keeping a subset of the formals, and their actuals
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See proofs in filter-formals-and-actuals-proofs.lisp

;; Returns (mv new-formals new-actuals) where the NEW-FORMALS are those members
;; of FORMALS that are also in FORMALS-TO-KEEP and the NEW-ACTUALS are their
;; corresponding actuals.  The order of the FORMALS is not changed.
(defund filter-formals-and-actuals (formals actuals formals-to-keep)
  (declare (xargs :guard (and (symbol-listp formals)
                              (true-listp actuals) ;; actuals is a list of terms (often pseudo-terms)
                              (equal (len formals) (len actuals))
                              (symbol-listp formals-to-keep))))
  (if (endp formals)
      (mv nil nil)
    (mv-let (formals-res actuals-res)
      (filter-formals-and-actuals (rest formals) (rest actuals) formals-to-keep)
      (if (member-eq (first formals) formals-to-keep)
          (mv (cons-with-hint (first formals) formals-res formals)
              (cons-with-hint (first actuals) actuals-res actuals))
        (mv formals-res
            actuals-res)))))
