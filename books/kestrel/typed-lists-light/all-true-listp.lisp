; A function to check that all elements of a list are true-lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also true-list-listp, but that one requires the final cdr to be nil.
(defun all-true-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (true-listp (first x))
         (all-true-listp (rest x)))))

(defthm all-true-listp-of-cdr
  (implies (all-true-listp x)
           (all-true-listp (cdr x))))

;; Disabled since this might be tried often.
(defthmd true-listp-of-car-when-all-true-listp
  (implies (all-true-listp x)
           (true-listp (car x))))

;; Disabled since this might be tried often.
(defthmd true-listp-of-nth-when-all-true-listp
  (implies (all-true-listp x)
           (true-listp (nth n x)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm all-true-listp-of-update-nth
  (implies (and (true-listp val)
                (all-true-listp x))
           (all-true-listp (update-nth m val x)))
  :hints (("Goal" :in-theory (enable update-nth all-true-listp))))

(defthm all-true-listp-of-cons
  (equal (all-true-listp (cons item x))
         (and (true-listp item)
              (all-true-listp x)))
  :hints (("Goal" :in-theory (enable all-true-listp))))

(defthmd true-listp-when-member-equal-and-all-true-listp
  (implies (and (member-equal a x) ; x is a free var
                (all-true-listp x))
           (true-listp a))
  :hints (("Goal" :in-theory (enable all-true-listp))))

(defthm all-true-listp-of-nthcdr
  (implies (all-true-listp x)
           (equal (all-true-listp (nthcdr n x))
                  t))
  :hints (("Goal" :in-theory (enable nthcdr))))
