; Proofs about filter-formals-and-actuals
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "filter-formals-and-actuals") ; brings in the defintion
(include-book "no-nils-in-termp")
(include-book "lambdas-closed-in-termp")
(include-book "no-duplicate-lambda-formals-in-termp")
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))

(in-theory (disable mv-nth))

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
