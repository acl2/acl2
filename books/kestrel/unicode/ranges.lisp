; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "code-points")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ranges
  :parents (tables)
  :short "Ranges of code points, and lists of ranges."
  :long
  (xdoc::topstring
   (xdoc::p
    "The binary properties of the Unicode Character Database,
     such as @('XID_Start'),
     are sets of code points.
     These sets are large but consist of relatively few ranges,
     which is also how the files of the database list them:
     a line of such a file has either one code point
     or the first and the last code point of a range.")
   (xdoc::p
    "We represent such a set as a list of ranges.
     A code point is in the set
     when it is in one of the ranges of the list.
     The definition of membership does not depend on
     the order of the ranges, or on whether they overlap."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod range
  :short "Fixtype of ranges of code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "A range consists of a minimum and a maximum code point.
     It stands for the code points
     from the minimum to the maximum, both included.
     A range whose maximum is below its minimum has no code points."))
  ((min code-point)
   (max code-point))
  :pred range-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist range-list
  :short "Fixtype of lists of ranges of code points."
  :elt-type range
  :true-listp t
  :elementp-of-nil nil
  :pred range-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-point-in-range-p ((cp code-point-p) (range range-p))
  :returns (yes/no booleanp)
  :short "Check if a code point is in a range."
  (b* ((cp (code-point-fix cp))
       ((range range) range))
    (and (<= range.min cp)
         (<= cp range.max)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define code-point-in-ranges-p ((cp code-point-p) (ranges range-listp))
  :returns (yes/no booleanp)
  :short "Check if a code point is in one of the ranges of a list."
  (cond ((endp ranges) nil)
        (t (or (code-point-in-range-p cp (car ranges))
               (code-point-in-ranges-p cp (cdr ranges)))))
  :hooks (:fix)

  ///

  (defrule code-point-in-ranges-p-of-cons
    (equal (code-point-in-ranges-p cp (cons range ranges))
           (or (code-point-in-range-p cp range)
               (code-point-in-ranges-p cp ranges))))

  (defrule code-point-in-ranges-p-of-nil
    (not (code-point-in-ranges-p cp nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define range-size ((range range-p))
  :returns (size natp
                 :rule-classes (:rewrite :type-prescription)
                 :hints (("Goal" :in-theory (enable natp))))
  :short "Number of code points in a range."
  (b* (((range range) range))
    (if (<= range.min range.max)
        (+ 1 (- range.max range.min))
      0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define range-list-size ((ranges range-listp))
  :returns (size natp
                 :rule-classes (:rewrite :type-prescription)
                 :hints (("Goal" :induct t)))
  :short "Sum of the numbers of code points in the ranges of a list."
  :long
  (xdoc::topstring
   (xdoc::p
    "When no two ranges of the list overlap,
     this is the number of code points in the set
     that the list represents.
     The generated tables assert this number,
     as a check against the files they are generated from."))
  (cond ((endp ranges) 0)
        (t (+ (range-size (car ranges))
              (range-list-size (cdr ranges)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define range-within-range-p ((sub range-p) (sup range-p))
  :returns (yes/no booleanp)
  :short "Check if a range is within another range."
  (b* (((range sub) sub)
       ((range sup) sup))
    (and (<= sup.min sub.min)
         (<= sub.max sup.max)))
  :hooks (:fix)

  ///

  (defruled code-point-in-range-p-when-range-within-range-p
    (implies (and (range-within-range-p sub sup)
                  (code-point-in-range-p cp sub))
             (code-point-in-range-p cp sup))
    :enable code-point-in-range-p))

;;;;;;;;;;;;;;;;;;;;

(define range-within-ranges-p ((sub range-p) (sups range-listp))
  :returns (yes/no booleanp)
  :short "Check if a range is within one of the ranges of a list."
  (cond ((endp sups) nil)
        (t (or (range-within-range-p sub (car sups))
               (range-within-ranges-p sub (cdr sups)))))
  :hooks (:fix)

  ///

  (defruled code-point-in-ranges-p-when-range-within-ranges-p
    (implies (and (range-within-ranges-p sub sups)
                  (code-point-in-range-p cp sub))
             (code-point-in-ranges-p cp sups))
    :induct t
    :enable (code-point-in-ranges-p
             code-point-in-range-p-when-range-within-range-p)))

;;;;;;;;;;;;;;;;;;;;

(define ranges-within-ranges-p ((subs range-listp) (sups range-listp))
  :returns (yes/no booleanp)
  :short "Check if every range of a list
          is within one of the ranges of another list."
  :long
  (xdoc::topstring
   (xdoc::p
    "If this is the case,
     every code point in the first list of ranges
     is in the second list of ranges: see the theorem.
     So relations between properties,
     e.g. that every @('XID_Start') code point
     is also an @('XID_Continue') code point,
     are proved by evaluating this function on the tables.")
   (xdoc::p
    "The converse does not hold in general:
     a range of the first list could be covered
     by several ranges of the second list together.
     It does not happen with the generated tables,
     whose ranges are maximal."))
  (cond ((endp subs) t)
        (t (and (range-within-ranges-p (car subs) sups)
                (ranges-within-ranges-p (cdr subs) sups))))
  :hooks (:fix)

  ///

  (defruled code-point-in-ranges-p-when-ranges-within-ranges-p
    (implies (and (ranges-within-ranges-p subs sups)
                  (code-point-in-ranges-p cp subs))
             (code-point-in-ranges-p cp sups))
    :induct t
    :enable (code-point-in-ranges-p
             code-point-in-ranges-p-when-range-within-ranges-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define range-disjoint-from-range-p ((x range-p) (y range-p))
  :returns (yes/no booleanp)
  :short "Check if two ranges have no code point in common."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when one of the two ranges ends
     before the other one starts,
     and also when one of the two has no code points."))
  (b* (((range x) x)
       ((range y) y))
    (or (< x.max x.min)
        (< y.max y.min)
        (< x.max y.min)
        (< y.max x.min)))
  :hooks (:fix)

  ///

  (defruled not-code-point-in-range-p-when-range-disjoint-from-range-p
    (implies (and (range-disjoint-from-range-p x y)
                  (code-point-in-range-p cp x))
             (not (code-point-in-range-p cp y)))
    :enable code-point-in-range-p))

;;;;;;;;;;;;;;;;;;;;

(define range-disjoint-from-ranges-p ((x range-p) (ys range-listp))
  :returns (yes/no booleanp)
  :short "Check if a range has no code point in common
          with any of the ranges of a list."
  (cond ((endp ys) t)
        (t (and (range-disjoint-from-range-p x (car ys))
                (range-disjoint-from-ranges-p x (cdr ys)))))
  :hooks (:fix)

  ///

  (defruled not-code-point-in-ranges-p-when-range-disjoint-from-ranges-p
    (implies (and (range-disjoint-from-ranges-p x ys)
                  (code-point-in-range-p cp x))
             (not (code-point-in-ranges-p cp ys)))
    :induct t
    :enable (code-point-in-ranges-p
             not-code-point-in-range-p-when-range-disjoint-from-range-p)))

;;;;;;;;;;;;;;;;;;;;

(define ranges-disjoint-from-ranges-p ((xs range-listp) (ys range-listp))
  :returns (yes/no booleanp)
  :short "Check if no range of a list has a code point in common
          with any of the ranges of another list."
  :long
  (xdoc::topstring
   (xdoc::p
    "If this is the case,
     no code point is in both lists of ranges: see the theorem.
     Together with @(tsee ranges-within-ranges-p),
     this lets us prove, by evaluation on the tables,
     which code points of some part of the codespace have a property:
     the ones in some ranges do,
     and the ones in the other ranges of that part do not."))
  (cond ((endp xs) t)
        (t (and (range-disjoint-from-ranges-p (car xs) ys)
                (ranges-disjoint-from-ranges-p (cdr xs) ys))))
  :hooks (:fix)

  ///

  (defruled not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p
    (implies (and (ranges-disjoint-from-ranges-p xs ys)
                  (code-point-in-ranges-p cp xs))
             (not (code-point-in-ranges-p cp ys)))
    :induct t
    :enable (code-point-in-ranges-p
             not-code-point-in-ranges-p-when-range-disjoint-from-ranges-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define scalar-value-ranges ()
  :returns (ranges range-listp)
  :short "The Unicode scalar values, as a list of ranges."
  (list (range #x0000 #xD7FF)
        (range #xE000 #x10FFFF))

  ///

  (in-theory (disable (:e scalar-value-ranges)))

  (defruled scalar-value-p-when-code-point-in-scalar-value-ranges
    (implies (and (code-point-in-ranges-p cp (scalar-value-ranges))
                  (code-point-p cp))
             (scalar-value-p cp))
    :enable (code-point-in-range-p
             scalar-value-p-alt-def)
    :disable scalar-value-p))
