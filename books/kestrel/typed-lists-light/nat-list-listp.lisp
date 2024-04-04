; Recognizing a list of lists of naturals
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund nat-list-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (nat-listp (first x))
         (nat-list-listp (rest x)))))

(defthm nat-list-listp-of-cons
  (equal (nat-list-listp (cons a x))
         (and (nat-listp a)
              (nat-list-listp x)))
  :hints (("Goal" :in-theory (enable nat-list-listp))))

(defthmd nat-listp-of-car-when-nat-list-listp
  (implies (nat-list-listp x)
           (nat-listp (car x)))
  :hints (("Goal" :in-theory (enable nat-list-listp))))

(local (in-theory (enable nat-listp-of-car-when-nat-list-listp)))

(defthm nat-list-listp-forward-to-true-listp
  (implies (nat-list-listp x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable nat-list-listp))))

(defthm nat-list-listp-of-append
  (equal (nat-list-listp (append x y))
         (and (nat-list-listp (true-list-fix x))
              (nat-list-listp y)))
  :hints (("Goal" :in-theory (enable nat-list-listp append))))

(defthmd true-listp-when-nat-list-listp
  (implies (nat-list-listp x)
           (true-listp x))
  :hints (("Goal" :in-theory (enable nat-list-listp))))
