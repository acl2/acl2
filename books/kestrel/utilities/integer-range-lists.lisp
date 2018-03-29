; Lists of Integers in Ranges
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/deflist" :dir :system)
(include-book "integer-range-fixing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist integer-range-listp (lower upper x)
  (integer-range-p lower upper x)
  :guard (and (integerp lower) (integerp upper))
  :parents (kestrel-utilities lists integer-range-p)
  :short "Recognize true lists of integers in ranges."
  :long
  "<p>
   This lifts @(tsee integer-range-p) to lists.
   The range goes from @('lower') inclusive to @('upper') exclusive,
   as in @(tsee integer-range-p).
   </p>"
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-range-list-fix ((lower integerp)
                                (upper integerp)
                                (x (integer-range-listp (ifix lower)
                                                        (ifix upper)
                                                        x)))
  :returns (fixed-x (integer-range-listp lower upper fixed-x)
                    :hyp  (and (integerp lower)
                               (integerp upper)
                               (< lower upper)))
  :parents (integer-range-listp)
  :short "Fixing function for @(tsee integer-range-listp)."
  :long
  "<p>
   This lifts @(tsee integer-range-fix) to lists.
   See that function for more information,
   in particular about
   the fixing of @('lower') and @('upper') to integers
   and the treatment of empty ranges.
   </p>"
  (mbe :logic (cond ((atom x) nil)
                    (t (cons (integer-range-fix lower upper (car x))
                             (integer-range-list-fix lower upper (cdr x)))))
       :exec x)
  :hooks (:fix)
  ///

  (more-returns
   (fixed-x integer-listp
            :name integer-listp-of-integer-range-list-fix))

  (defrule integer-range-list-fix-when-integer-range-p
    (implies (and (integer-range-listp (ifix lower) (ifix upper) x)
                  (< (ifix lower) (ifix upper)))
             (equal (integer-range-list-fix lower upper x)
                    x)))

  (defrule integer-range-list-fix-of-nil
    (equal (integer-range-list-fix lower upper nil)
           nil))

  (defrule integer-range-list-fix-of-cons
    (equal (integer-range-list-fix lower upper (cons x y))
           (cons (integer-range-fix lower upper x)
                 (integer-range-list-fix lower upper y))))

  (defrule integer-range-list-fix-of-append
    (equal (integer-range-list-fix lower upper (append x y))
           (append (integer-range-list-fix lower upper x)
                   (integer-range-list-fix lower upper y))))

  (defrule len-of-integer-range-list-fix
    (equal (len (integer-range-list-fix lower upper x))
           (len x)))

  (defrule consp-of-integer-range-list-fix
    (equal (consp (integer-range-list-fix lower upper x))
           (consp x)))

  (defrule car-of-integer-range-list-fix
    (implies (consp x)
             (equal (car (integer-range-list-fix lower upper x))
                    (integer-range-fix lower upper (car x)))))

  (defrule cdr-of-integer-range-list-fix
    (implies (consp x)
             (equal (cdr (integer-range-list-fix lower upper x))
                    (integer-range-list-fix lower upper (cdr x)))))

  (defrule rev-of-integer-range-list-fix
    (equal (rev (integer-range-list-fix lower upper x))
           (integer-range-list-fix lower upper (rev x)))
    :enable rev))
