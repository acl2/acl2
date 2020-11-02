; A function to count occurrences of an item in a list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A function to count occurrences of an item in a list.

;; There is a function called duplicity in std/, but it has a different guard
;; and a terrible (!) name.

(defun count-occs (item lst)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst)
      0
    (if (equal item (first lst))
        (+ 1 (count-occs item (rest lst)))
      (count-occs item (rest lst)))))

(defthm count-occs-of-append
  (equal (count-occs item (append x y))
         (+ (count-occs item x)
            (count-occs item y))))

(defthm natp-of-count-occs
  (natp (count-occs item lst))
  :rule-classes :type-prescription)

(defthm count-occs-of-true-list-fix
  (equal (count-occs item (true-list-fix lst))
         (count-occs item lst))
  :hints (("Goal" :in-theory (enable count-occs))))

(defthm count-occs-of-cons
  (equal (count-occs x1 (cons x2 lst))
         (if (equal x1 x2)
             (+ 1 (count-occs x1 lst))
           (count-occs x1 lst)))
  :hints (("goal" :in-theory (enable count-occs))))

(defthm count-occs-of-nil
  (equal (count-occs x nil)
         0)
  :hints (("goal" :in-theory (enable count-occs)))  )

(defthm count-occs-equal-0-rewrite
  (equal (equal (count-occs x l) 0)
         (not (member-equal x l)))
  :hints (("goal" :in-theory (enable count-occs))))
