; Keeping a subset of the formals, and their actuals
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "no-nils-in-termp") ; or make a separate proofs book
(include-book "lambdas-closed-in-termp")
(include-book "no-duplicate-lambda-formals-in-termp")
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))

(in-theory (disable mv-nth))

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

(defthm true-listp-of-mv-nth-0-of-filter-formals-and-actuals
  (true-listp (mv-nth 0 (filter-formals-and-actuals formals actuals formals-to-keep)))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm true-listp-of-mv-nth-1-of-filter-formals-and-actuals
  (true-listp (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep)))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm symbol-listp-of-mv-nth-0-of-filter-formals-and-actuals
  (implies (symbol-listp formals)
           (symbol-listp (mv-nth 0 (filter-formals-and-actuals formals actuals formals-to-keep))))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm pseudo-term-listp-of-mv-nth-1-of-filter-formals-and-actuals
  (implies (pseudo-term-listp actuals)
           (pseudo-term-listp (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep))))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm len-of-mv-nth-1-of-filter-formals-and-actuals
  (equal (len (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep)))
         (len (mv-nth 0 (filter-formals-and-actuals formals actuals formals-to-keep))))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm subsetp-equal-of-mv-nth-0-of-filter-formals-and-actuals
  (subsetp-equal (mv-nth 0 (filter-formals-and-actuals formals actuals vars)) formals)
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

;; strong
(defthm mv-nth-0-of-filter-formals-and-actuals
  (equal (mv-nth 0 (filter-formals-and-actuals formals actuals formals-to-keep))
         (intersection-equal formals formals-to-keep))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals) )))

(defthm no-nils-in-termsp-of-mv-nth-1-of-filter-formals-and-actuals
  (implies (and (no-nils-in-termsp actuals)
                (equal (len formals) (len actuals)))
           (no-nils-in-termsp (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep))))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm lambdas-closed-in-termsp-of-mv-nth-1-of-filter-formals-and-actuals
  (implies (lambdas-closed-in-termsp actuals)
           (lambdas-closed-in-termsp (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep))))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm no-duplicate-lambda-formals-in-termsp-of-mv-nth-1-of-filter-formals-and-actuals
  (implies (no-duplicate-lambda-formals-in-termsp actuals)
           (no-duplicate-lambda-formals-in-termsp (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep))))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm no-duplicatesp-equal-of-mv-nth-0-of-filter-formals-and-actuals
  (implies (no-duplicatesp-equal formals)
           (no-duplicatesp-equal (mv-nth 0 (filter-formals-and-actuals formals actuals formals-to-keep))))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm filter-formals-and-actuals-of-nil-arg1
  (equal (filter-formals-and-actuals nil actuals formals-to-keep)
         (mv nil nil))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))
