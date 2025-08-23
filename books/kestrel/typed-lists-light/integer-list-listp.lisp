; Recognizing a list of lists of integers
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

;; Note that integer-listp, called here, is built in to ACL2

(defund integer-list-listp (x)
  (declare (xargs :guard t))
  (if (not (consp x))
      (null x)
    (and (integer-listp (first x))
         (integer-list-listp (rest x)))))

(defthm integer-list-listp-of-cons
  (equal (integer-list-listp (cons a x))
         (and (integer-listp a)
              (integer-list-listp x)))
  :hints (("Goal" :in-theory (enable integer-list-listp))))

(defthmd integer-listp-of-car-when-integer-list-listp
  (implies (integer-list-listp x)
           (integer-listp (car x)))
  :hints (("Goal" :in-theory (enable integer-list-listp))))

(local (in-theory (enable integer-listp-of-car-when-integer-list-listp)))

(defthm integer-list-listp-forward-to-true-listp
  (implies (integer-list-listp x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable integer-list-listp))))

(defthm integer-list-listp-of-append
  (equal (integer-list-listp (append x y))
         (and (integer-list-listp (true-list-fix x))
              (integer-list-listp y)))
  :hints (("Goal" :in-theory (enable integer-list-listp append))))

(defthmd true-listp-when-integer-list-listp
  (implies (integer-list-listp x)
           (true-listp x))
  :hints (("Goal" :in-theory (enable integer-list-listp))))
