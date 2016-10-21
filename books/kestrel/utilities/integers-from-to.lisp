; Lists of Contiguous Integers
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides a function to generate lists of contiguous integers.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integers-from-to ((min integerp) (max integerp))
  :returns (ints integer-listp)
  :parents (kestrel-utilities)
  :short "Ordered list of all the integers in a range."
  :long
  "<p>
   The range goes from @('min') to @('max'), inclusive.
   If @('min') exceeds @('max'), the result is @('nil').
   </p>"
  (integers-from-to-aux min max nil)

  :prepwork
  ((define integers-from-to-aux ((min integerp)
                                 (max integerp)
                                 (ints integer-listp))
     :returns (final-ints integer-listp :hyp (integer-listp ints))
     (b* ((min (mbe :logic (ifix min) :exec min))
          (max (mbe :logic (ifix max) :exec max)))
       (cond ((> min max) ints)
             (t (integers-from-to-aux min (1- max) (cons max ints)))))
     :measure (nfix (- (1+ (ifix max)) (ifix min)))
     ///

     (defrule nat-listp-of-integers-from-to-aux
       (equal (nat-listp (integers-from-to-aux min max ints))
              (and (nat-listp ints)
                   (or (> (ifix min) (ifix max))
                       (natp (ifix min))))))

     (defrule integers-from-to-iff-min<=max-or-ints
       (iff (integers-from-to-aux min max ints)
            (or (<= (ifix min) (ifix max))
                ints)))

     (defrule int-equiv-implies-equal-integers-from-to-aux-1
       (implies (int-equiv min min-equiv)
                (equal (integers-from-to-aux min max ints)
                       (integers-from-to-aux min-equiv max ints)))
       :rule-classes nil
       :hints ('(:expand ((integers-from-to-aux 0 max ints)))))

     (defrule int-equiv-implies-equal-integers-from-to-aux-2
       (implies (int-equiv max max-equiv)
                (equal (integers-from-to-aux min max ints)
                       (integers-from-to-aux min max-equiv ints)))
       :rule-classes nil
       :hints ('(:expand ((integers-from-to-aux min 0 ints)))))

     (defrule member-of-integers-from-to-aux
       (iff (member x (integers-from-to-aux min max ints))
            (or (and (integerp x)
                     (<= (ifix min) x)
                     (<= x (ifix max)))
                (member x ints))))))

  ///

  (more-returns
   (ints true-listp
         :name true-listp-of-integers-from-to
         :rule-classes :type-prescription))

  (defrule nat-listp-of-integers-from-to
    (equal (nat-listp (integers-from-to min max))
           (or (> (ifix min) (ifix max))
               (natp (ifix min)))))

  (defrule integers-from-to-iff-min<=max
    (iff (integers-from-to min max)
         (<= (ifix min) (ifix max))))

  (defcong int-equiv equal (integers-from-to min max) 1
    :hints (("Goal"
             :use (int-equiv-implies-equal-integers-from-to-aux-1
                   (:instance int-equiv-implies-equal-integers-from-to-aux-1
                              (ints nil))))))

  (defcong int-equiv equal (integers-from-to min max) 2
    :hints (("Goal"
             :use (int-equiv-implies-equal-integers-from-to-aux-2
                   (:instance int-equiv-implies-equal-integers-from-to-aux-2
                              (ints nil))))))

  (defrule member-of-integers-from-to
    (iff (member x (integers-from-to min max))
         (and (integerp x)
              (<= (ifix min) x)
              (<= x (ifix max))))))
