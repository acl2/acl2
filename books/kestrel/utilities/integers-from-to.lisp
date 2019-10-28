; Lists of Contiguous Integers
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integers-from-to ((min integerp) (max integerp))
  :returns (ints integer-listp)
  :parents (kestrel-utilities)
  :short "Ordered list of all the integers in a range."
  :long
  (xdoc::topstring-p
   "The range goes from @('min') to @('max'), inclusive.
    If @('min') exceeds @('max'), the result is @('nil').")
  (mbe :logic (b* ((min (ifix min))
                   (max (ifix max)))
                (cond ((> min max) nil)
                      (t (cons min (integers-from-to (1+ min) max)))))
       :exec (integers-from-to-aux min max nil))
  :measure (nfix (- (1+ (ifix max)) (ifix min)))
  :verify-guards nil ; done below

  :prepwork
  ((define integers-from-to-aux ((min integerp)
                                 (max integerp)
                                 (ints integer-listp))
     (b* ((min (mbe :logic (ifix min) :exec min))
          (max (mbe :logic (ifix max) :exec max)))
       (cond ((> min max) ints)
             (t (integers-from-to-aux min (1- max) (cons max ints)))))
     :measure (nfix (- (1+ (ifix max)) (ifix min)))))

  ///

  (more-returns
   (ints true-listp
         :name true-listp-of-integers-from-to
         :rule-classes :type-prescription))

  (defrule nat-listp-of-integers-from-to
    (equal (nat-listp (integers-from-to min max))
           (or (> (ifix min) (ifix max))
               (natp (ifix min)))))

  (defcong int-equiv equal (integers-from-to min max) 1)

  (defcong int-equiv equal (integers-from-to min max) 2)

  (defrule integers-from-to-nil-when-min>max
    (implies (> (ifix min) (ifix max))
             (equal (integers-from-to min max)
                    nil)))

  (defrule integers-from-to-iff-min<=max
    (iff (integers-from-to min max)
         (<= (ifix min) (ifix max))))

  (defrule member-of-integers-from-to
    (iff (member x (integers-from-to min max))
         (and (integerp x)
              (<= (ifix min) x)
              (<= x (ifix max)))))

  (local
   (defrule verify-guards-lemma-1
     (implies (and (integerp min)
                   (integerp max)
                   (integer-listp ints))
              (equal (integers-from-to-aux min max ints)
                     (append (integers-from-to min max) ints)))
     :enable integers-from-to-aux))

  (local
   (defrule verify-guards-lemma-2
     (implies (and (integerp min)
                   (integerp max))
              (equal (integers-from-to-aux min max nil)
                     (integers-from-to min max)))))

  (verify-guards integers-from-to))
