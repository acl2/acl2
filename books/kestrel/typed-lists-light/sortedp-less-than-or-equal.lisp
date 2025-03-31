; Recognizing a sorted (ascending) list of rationals
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also increasingp

(defund sortedp-<= (x)
  (declare (xargs :guard (rational-listp x)))
  (if (endp x)
      t
    (if (endp (rest x))
        t
      (and (<= (first x) (second x)) ;allows dups
           (sortedp-<= (rest x))))))

(defthm sortedp-<=-of-cdr
  (implies (sortedp-<= x)
           (sortedp-<= (cdr x)))
  :hints (("Goal" :in-theory (enable sortedp-<=))))

(defthmd <=-of-car-and-cadr-when-sortedp-<=
  (implies (and (sortedp-<= x)
                (consp (cdr x)))
           (<= (car x) (cadr x)))
  :hints (("Goal" :in-theory (enable sortedp-<=))))

(defthmd <=-of-car-and-cadr-when-sortedp-<=-linear
  (implies (and (sortedp-<= x)
                (consp (cdr x)))
           (<= (car x) (cadr x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable sortedp-<=))))

(defthm sortedp-<=-of-singleton
  (sortedp-<= (list x))
  :hints (("Goal" :in-theory (enable sortedp-<=))))

(defthm sortedp-<=-when-not-consp-of-cdr
  (implies (not (consp (cdr x)))
           (sortedp-<= x))
  :hints (("Goal" :in-theory (enable sortedp-<=))))
