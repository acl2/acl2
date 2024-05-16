; A lightweight book about the built-in function remove-assoc-equal
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book previously introduced an equivalent function called clear-key.

(in-theory (disable remove-assoc-equal))

;; Changed param names to match std
(defthm alistp-of-remove-assoc-equal
  (implies (alistp x)
           (alistp (remove-assoc-equal a x)))
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

(defthm len-of-remove-assoc-equal-linear
  (<= (len (remove-assoc-equal key alist))
      (len alist))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

(defthm true-listp-of-remove-assoc-equal-type
  (implies (true-listp alist)
           (true-listp (remove-assoc-equal key alist)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

(defthm remove-assoc-equal-when-not-member-equal-of-strip-cars
  (implies (not (member-equal key (strip-cars alist)))
           (equal (remove-assoc-equal key alist)
                  (true-list-fix alist)))
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))
