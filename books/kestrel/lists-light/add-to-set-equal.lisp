; A lightweight book about the built-in function add-to-set-equal.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable add-to-set-equal))

(defthm consp-of-add-to-set-equal-type
  (consp (add-to-set-equal a x))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable add-to-set-equal))))

;; consp-of-add-to-set-equal is better
(in-theory (disable (:t add-to-set-equal)))

(defthm true-listp-of-add-to-set-equal-type
  (implies (true-listp x)
           (true-listp (add-to-set-equal a x)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable add-to-set-equal))))

(defthm true-listp-of-add-to-set-equal
  (equal (true-listp (add-to-set-equal a x))
         (true-listp x))
  :hints (("Goal" :in-theory (enable add-to-set-equal))))

(defthm member-equal-of-add-to-set-equal-iff
  (iff (member-equal x1 (add-to-set-equal x2 l))
       (if (equal x1 x2)
           t
         (member-equal x1 l)))
  :hints (("Goal" :in-theory (enable add-to-set-equal))))
