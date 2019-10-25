; Set of Contiguous Integers
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "integers-from-to")

(include-book "kestrel/utilities/osets" :dir :system)
(include-book "kestrel/utilities/oset-theorems" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection integers-from-to-as-set
  :parents (integers-from-to)
  :short (xdoc::topstring
          "Theorems about @(tsee integers-from-to) as a "
          (xdoc::seetopic "std/osets" "finite set")
          ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @(tsee integers-from-to) is defined, and verified,
     to return a list of integers in increasing order.
     Because of this order, this list is also a set
     represented according to the @(csee std/osets) library.")
   (xdoc::p
    "Thus, here we introduce some theorems
     about @(tsee integers-from-to) viewed as a set:")
   (xdoc::ul
    (xdoc::li
     "The result of @(tsee integers-from-to) is (also) a set.")
    (xdoc::li
     "Membership in @(tsee integers-from-to) is equivalent to
      being an integer in the range.")
    (xdoc::li
     "Membership of all the elements in an @(tsee integers-from-to) list
      in an @(tsee integers-from-to) set is equivalent to
      the first range being contained in the second one.")))

  (defrule setp-of-integers-from-to
    (set::setp (integers-from-to min max))
    :enable (integers-from-to set::setp << lexorder alphorder)
    :hints ('(:expand ((integers-from-to (+ 1 min) max)
                       (integers-from-to 1 max)))))

  (defrule in-of-integers-from-to
    (iff (set::in x (integers-from-to min max))
         (and (integerp x)
              (<= (ifix min) x)
              (<= x (ifix max))))
    :enable set::in-to-member-when-setp)

  (defrule integers-from-to-list-in-integers-from-to
    (implies (and (integerp min1)
                  (integerp max1)
                  (integerp min2)
                  (integerp max2)
                  (<= min1 max1))
             (equal (set::list-in (integers-from-to min1 max1)
                                  (integers-from-to min2 max2))
                    (and (<= min2 min1)
                         (<= max1 max2))))
    :enable integers-from-to))
