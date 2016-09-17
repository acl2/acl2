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
  :short "Ordered list of
          all the integers between @('min') and @('max'), inclusive."
  :long
  "<p>
   If @('min') exceeds @('max'), the result is @('nil').
   </p>"
  (b* ((min (mbe :logic (ifix min) :exec min))
       (max (mbe :logic (ifix max) :exec max)))
    (if (<= min max)
        (cons min (integers-from-to (1+ min) max))
      nil))
  :measure (nfix (- (1+ (ifix max)) (ifix min)))
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

  (defcong int-equiv equal (integers-from-to min max) 1)

  (defcong int-equiv equal (integers-from-to min max) 2)

  (defrule member-of-integers-from-to
    (iff (member x (integers-from-to min max))
         (and (integerp x)
              (<= (ifix min) x)
              (<= x (ifix max))))))
