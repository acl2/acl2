; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "ranges")

(local (include-book "std/lists/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ range-operations
  :parents (tables)
  :short "Operations on sets of code points
          that are represented as lists of ranges:
          complement, union, intersection, difference, and size."
  :long
  (xdoc::topstring
   (xdoc::p
    "A list of ranges stands for a set of code points (see @(see ranges)).
     Here are the operations that make new sets out of such sets.
     They are for models that define their own sets of characters
     from the properties of this library,
     for example the letters that are not in a certain other set,
     and that state how many code points such a set has.
     They also give the code points on which a property differs
     between two versions of Unicode:
     that is the difference of two sets.")
   (xdoc::p
    "Each operation comes with a theorem that says
     which code points are in its result:
     a code point is in the complement of a set
     exactly when it is not in the set;
     it is in the union of two sets
     exactly when it is in one of the two; and so on.
     These theorems hold for all lists of ranges,
     in any order, overlapping or not.")
   (xdoc::p
    "The result of each operation is in normal form
     (see @(tsee ranges-normalized-p)):
     its ranges are not empty,
     they are in increasing order,
     and there is at least one code point
     between two consecutive ranges.
     For a list in normal form,
     @(tsee range-list-size) is the number of code points of the set:
     see @(see code-points-of-ranges).
     And the set is empty exactly when the list is empty.")
   (xdoc::p
    "All the operations are defined from one of them, the complement,
     which is computed by removing the ranges of a list, one at a time,
     from the range of all the code points.
     The time that this takes is proportional to
     the number of ranges of the argument
     times the number of ranges of the result.
     That is enough for the tables of this library,
     which have at most a few thousand ranges."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The minimum and the maximum of a range are at most #x10FFFF,
;; as facts that linear arithmetic can use.

(defrulel range->min-upper-bound
  (<= (range->min x) #x10FFFF)
  :rule-classes :linear
  :enable code-point-p
  :disable code-point-p-of-range->min
  :use code-point-p-of-range->min)

(defrulel range->max-upper-bound
  (<= (range->max x) #x10FFFF)
  :rule-classes :linear
  :enable code-point-p
  :disable code-point-p-of-range->max
  :use code-point-p-of-range->max)

(defrulel code-point-fix-upper-bound
  (<= (code-point-fix x) #x10FFFF)
  :rule-classes :linear
  :enable (code-point-fix
           code-point-p))

(defrulel range-listp-of-append
  (implies (and (range-listp x)
                (range-listp y))
           (range-listp (append x y)))
  :induct (len x)
  :enable (append
           len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule code-point-in-ranges-p-of-append
  (equal (code-point-in-ranges-p cp (append ranges1 ranges2))
         (or (code-point-in-ranges-p cp ranges1)
             (code-point-in-ranges-p cp ranges2)))
  :parents (range-operations)
  :short "A code point is in one of the ranges of two lists put together
          exactly when it is in one of the ranges of one of the two."
  :induct (len ranges1)
  :enable (code-point-in-ranges-p
           len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ranges-above-p ((bound integerp) (ranges range-listp))
  :returns (yes/no booleanp)
  :short "Check if the ranges of a list are not empty, are in increasing order
          with at least one code point between two consecutive ranges,
          and are all above a bound."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first range has to start above the bound.
     Each of the other ranges has to start above
     the code point after the end of the range before it."))
  (or (endp ranges)
      (b* (((range range) (car ranges)))
        (and (< (ifix bound) range.min)
             (<= range.min range.max)
             (ranges-above-p (+ 1 range.max) (cdr ranges)))))
  :hooks nil ; done below

  ///

  (fty::deffixequiv ranges-above-p
    :hints (("Goal"
             :induct (ranges-above-p bound ranges)
             :expand ((ranges-above-p bound (range-list-fix ranges))
                      (ranges-above-p (ifix bound) ranges))
             :in-theory (enable ranges-above-p))))

  (defruled ranges-above-p-when-above-greater
    (implies (and (ranges-above-p bound1 ranges)
                  (<= (ifix bound2) (ifix bound1)))
             (ranges-above-p bound2 ranges))
    :expand ((ranges-above-p bound1 ranges)
             (ranges-above-p bound2 ranges))))

;;;;;;;;;;;;;;;;;;;;

(define ranges-normalized-p ((ranges range-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of ranges is in normal form."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if its ranges are not empty,
     they are in increasing order,
     and there is at least one code point
     between two consecutive ranges
     (otherwise the two could be one range).
     Every set of code points has a list of ranges of this form.")
   (xdoc::p
    "The results of the operations on lists of ranges are in this form."))
  (ranges-above-p -1 ranges)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define range-minus-range ((range range-p) (minus range-p))
  :returns (ranges range-listp)
  :short "The code points of a range that are not in another range,
          as a list of at most two ranges."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the second range is empty or does not meet the first one,
     the result is the first range, unless that one is empty.
     Otherwise the result has
     the part of the first range that is below the second one,
     if there is one,
     and the part that is above it, if there is one."))
  (b* (((range r) range)
       ((range m) minus)
       ((when (< r.max r.min)) nil)
       ((when (or (< m.max m.min)
                  (< m.max r.min)
                  (< r.max m.min)))
        (list (range-fix range))))
    (append (and (< r.min m.min)
                 (list (range r.min (- m.min 1))))
            (and (< m.max r.max)
                 (list (range (+ 1 m.max) r.max)))))
  :guard-hints (("Goal" :in-theory (enable code-point-p natp)))
  :hooks (:fix)

  ///

  (defrule code-point-in-ranges-p-of-range-minus-range
    (equal (code-point-in-ranges-p cp (range-minus-range range minus))
           (and (code-point-in-range-p cp range)
                (not (code-point-in-range-p cp minus))))
    :enable (code-point-in-range-p
             code-point-p
             natp)))

;;;;;;;;;;;;;;;;;;;;

(define ranges-minus-range ((ranges range-listp) (minus range-p))
  :returns (new-ranges range-listp)
  :short "The code points of the ranges of a list that are not in a range,
          as a list of ranges."
  (cond ((endp ranges) nil)
        (t (append (range-minus-range (car ranges) minus)
                   (ranges-minus-range (cdr ranges) minus))))
  :hooks (:fix)

  ///

  (defrule code-point-in-ranges-p-of-ranges-minus-range
    (equal (code-point-in-ranges-p cp (ranges-minus-range ranges minus))
           (and (code-point-in-ranges-p cp ranges)
                (not (code-point-in-range-p cp minus))))
    :induct (ranges-minus-range ranges minus)
    :enable code-point-in-ranges-p)

  (defrule ranges-above-p-of-ranges-minus-range
    (implies (ranges-above-p bound ranges)
             (ranges-above-p bound (ranges-minus-range ranges minus)))
    :induct (ranges-above-p bound ranges)
    :enable (ranges-above-p
             range-minus-range
             ranges-above-p-when-above-greater
             code-point-p
             natp
             fix
             ifix)))

;;;;;;;;;;;;;;;;;;;;

(define ranges-minus-ranges ((ranges range-listp) (minus range-listp))
  :returns (new-ranges range-listp)
  :short "The code points of the ranges of a list
          that are not in the ranges of another list,
          as a list of ranges."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ranges of the second list are removed one at a time.
     If the first list is in normal form, so is the result.
     See @(tsee ranges-difference) for a function
     whose result is always in normal form."))
  (cond ((endp minus) (range-list-fix ranges))
        (t (ranges-minus-ranges (ranges-minus-range ranges (car minus))
                                (cdr minus))))
  :hooks (:fix)

  ///

  (defrule code-point-in-ranges-p-of-ranges-minus-ranges
    (equal (code-point-in-ranges-p cp (ranges-minus-ranges ranges minus))
           (and (code-point-in-ranges-p cp ranges)
                (not (code-point-in-ranges-p cp minus))))
    :induct (ranges-minus-ranges ranges minus)
    :enable code-point-in-ranges-p)

  (defrule ranges-above-p-of-ranges-minus-ranges
    (implies (ranges-above-p bound ranges)
             (ranges-above-p bound (ranges-minus-ranges ranges minus)))
    :induct (ranges-minus-ranges ranges minus))

  (defrule ranges-normalized-p-of-ranges-minus-ranges
    (implies (ranges-normalized-p ranges)
             (ranges-normalized-p (ranges-minus-ranges ranges minus)))
    :enable ranges-normalized-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ranges-complement ((ranges range-listp))
  :returns (new-ranges range-listp)
  :short "The code points that are not in the ranges of a list,
          as a list of ranges in normal form."
  :long
  (xdoc::topstring
   (xdoc::p
    "We remove the ranges of the list
     from the range of all the code points."))
  (ranges-minus-ranges (list (range 0 #x10FFFF)) ranges)
  :hooks (:fix)

  ///

  (defrule code-point-in-ranges-p-of-ranges-complement
    (equal (code-point-in-ranges-p cp (ranges-complement ranges))
           (not (code-point-in-ranges-p cp ranges)))
    :enable code-point-in-range-p)

  (defrule ranges-normalized-p-of-ranges-complement
    (ranges-normalized-p (ranges-complement ranges))))

;;;;;;;;;;;;;;;;;;;;

(define ranges-normalize ((ranges range-listp))
  :returns (new-ranges range-listp)
  :short "Put a list of ranges in normal form:
          the result has the same code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the complement of the complement."))
  (ranges-complement (ranges-complement ranges))
  :hooks (:fix)

  ///

  (defrule code-point-in-ranges-p-of-ranges-normalize
    (equal (code-point-in-ranges-p cp (ranges-normalize ranges))
           (code-point-in-ranges-p cp ranges))
    :enable not)

  (defrule ranges-normalized-p-of-ranges-normalize
    (ranges-normalized-p (ranges-normalize ranges))))

;;;;;;;;;;;;;;;;;;;;

(define ranges-union ((ranges1 range-listp) (ranges2 range-listp))
  :returns (new-ranges range-listp)
  :short "The code points that are in the ranges of one of two lists,
          as a list of ranges in normal form."
  (ranges-normalize (append ranges1 ranges2))
  :hooks (:fix)

  ///

  (defrule code-point-in-ranges-p-of-ranges-union
    (equal (code-point-in-ranges-p cp (ranges-union ranges1 ranges2))
           (or (code-point-in-ranges-p cp ranges1)
               (code-point-in-ranges-p cp ranges2))))

  (defrule ranges-normalized-p-of-ranges-union
    (ranges-normalized-p (ranges-union ranges1 ranges2))))

;;;;;;;;;;;;;;;;;;;;

(define ranges-difference ((ranges1 range-listp) (ranges2 range-listp))
  :returns (new-ranges range-listp)
  :short "The code points that are in the ranges of a list
          and not in the ranges of another list,
          as a list of ranges in normal form."
  (ranges-minus-ranges (ranges-normalize ranges1) ranges2)
  :hooks (:fix)

  ///

  (defrule code-point-in-ranges-p-of-ranges-difference
    (equal (code-point-in-ranges-p cp (ranges-difference ranges1 ranges2))
           (and (code-point-in-ranges-p cp ranges1)
                (not (code-point-in-ranges-p cp ranges2)))))

  (defrule ranges-normalized-p-of-ranges-difference
    (ranges-normalized-p (ranges-difference ranges1 ranges2))))

;;;;;;;;;;;;;;;;;;;;

(define ranges-intersection ((ranges1 range-listp) (ranges2 range-listp))
  :returns (new-ranges range-listp)
  :short "The code points that are in the ranges of both of two lists,
          as a list of ranges in normal form."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the code points of the first list
     that are not in the complement of the second one."))
  (ranges-difference ranges1 (ranges-complement ranges2))
  :hooks (:fix)

  ///

  (defrule code-point-in-ranges-p-of-ranges-intersection
    (equal (code-point-in-ranges-p cp (ranges-intersection ranges1 ranges2))
           (and (code-point-in-ranges-p cp ranges1)
                (code-point-in-ranges-p cp ranges2)))
    :enable not)

  (defrule ranges-normalized-p-of-ranges-intersection
    (ranges-normalized-p (ranges-intersection ranges1 ranges2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection empty-range-lists
  :parents (range-operations)
  :short "A list of ranges in normal form has no code points
          exactly when it is the empty list."
  :long
  (xdoc::topstring
   (xdoc::p
    "So the results of the operations can be tested by evaluation:
     two sets have no code point in common
     exactly when their intersection is the empty list,
     and every code point of a set is in another set
     exactly when their difference is the empty list.
     The last theorem is for that use:
     if the difference of two lists is the empty list,
     a code point that is in the first one is in the second one."))

  (defrule code-point-in-ranges-p-of-min-of-car-when-ranges-normalized-p
    (implies (and (ranges-normalized-p ranges)
                  (consp ranges))
             (code-point-in-ranges-p (range->min (car ranges)) ranges))
    :enable (ranges-normalized-p
             ranges-above-p
             code-point-in-ranges-p
             code-point-in-range-p))

  (defrule not-code-point-in-ranges-p-when-not-consp
    (implies (not (consp ranges))
             (not (code-point-in-ranges-p cp ranges)))
    :enable code-point-in-ranges-p)

  (defruled code-point-in-ranges-p-when-ranges-difference-is-empty
    (implies (and (not (consp (ranges-difference ranges1 ranges2)))
                  (code-point-in-ranges-p cp ranges1))
             (code-point-in-ranges-p cp ranges2))
    :disable (code-point-in-ranges-p-of-ranges-difference
              not-code-point-in-ranges-p-when-not-consp)
    :use (code-point-in-ranges-p-of-ranges-difference
          (:instance not-code-point-in-ranges-p-when-not-consp
                     (ranges (ranges-difference ranges1 ranges2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ code-points-of-ranges
  :parents (range-operations)
  :short "The code points of a list of ranges, as a list,
          and why the size of a list of ranges in normal form
          is the number of its code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @(tsee range-list-size)
     adds the sizes of the ranges of a list.
     That is the number of code points of the set
     only if no code point is in two of the ranges.
     Here we say this precisely.
     We define the list of the code points of the ranges of a list,
     in the order of the ranges.
     Its length is the size of the list of ranges;
     a code point is in it exactly when it is in one of the ranges;
     and if the list of ranges is in normal form
     (see @(tsee ranges-normalized-p)),
     no code point is in it twice.")
   (xdoc::p
    "So, to count the code points of a set that is given as a list of ranges,
     put the list in normal form, with @(tsee ranges-normalize)
     or with one of the other operations, and take its size."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;

(define range-code-points ((range range-p))
  :returns (cps code-point-listp)
  :short "The code points of a range, in increasing order."
  (integers-from-to (range->min range) (range->max range))
  :hooks (:fix)

  :prepwork
  ((defrulel code-point-listp-of-integers-from-to
     (implies (and (natp min)
                   (integerp max)
                   (<= max #x10FFFF))
              (code-point-listp (integers-from-to min max)))
     :induct t
     :enable (integers-from-to
              code-point-p
              natp
              ifix)))

  ///

  (defrule len-of-range-code-points
    (equal (len (range-code-points range))
           (range-size range))
    :enable (range-size
             acl2::len-of-integers-from-to
             nfix
             ifix
             fix))

  (defrule member-equal-of-range-code-points
    (iff (member-equal cp (range-code-points range))
         (and (code-point-p cp)
              (code-point-in-range-p cp range)))
    :enable (code-point-in-range-p
             code-point-p
             natp
             ifix)))

;;;;;;;;;;;;;;;;;;;;

(define range-list-code-points ((ranges range-listp))
  :returns (cps code-point-listp :hints (("Goal" :induct t)))
  :short "The code points of the ranges of a list:
          those of the first range, then those of the second one,
          and so on."
  (cond ((endp ranges) nil)
        (t (append (range-code-points (car ranges))
                   (range-list-code-points (cdr ranges)))))
  :hooks (:fix)

  ///

  (defrule len-of-range-list-code-points
    (equal (len (range-list-code-points ranges))
           (range-list-size ranges))
    :induct t
    :enable range-list-size)

  (defrule member-equal-of-range-list-code-points
    (iff (member-equal cp (range-list-code-points ranges))
         (and (code-point-p cp)
              (code-point-in-ranges-p cp ranges)))
    :induct t
    :enable code-point-in-ranges-p))

;;;;;;;;;;;;;;;;;;;;

(defsection range-list-code-points-without-duplicates
  :short "The list of the code points of a list of ranges in normal form
          has no duplicates."

  ;; A code point that is not above the bound is in none of the ranges.

  (defruled not-code-point-in-ranges-p-when-ranges-above-p
    (implies (and (ranges-above-p bound ranges)
                  (<= (code-point-fix cp) (ifix bound)))
             (not (code-point-in-ranges-p cp ranges)))
    :induct (ranges-above-p bound ranges)
    :enable (ranges-above-p
             code-point-in-ranges-p
             code-point-in-range-p
             ifix))

  (defrulel no-duplicatesp-equal-of-integers-from-to
    (no-duplicatesp-equal (integers-from-to min max))
    :induct (integers-from-to min max)
    :enable (integers-from-to
             acl2::integers-from-to-of-noninteger-max
             no-duplicatesp-equal
             ifix))

  (defrulel not-intersectp-equal-of-integers-from-to-when-ranges-above-p
    (implies (and (ranges-above-p bound ranges)
                  (<= (ifix max) (ifix bound)))
             (not (intersectp-equal (integers-from-to min max)
                                    (range-list-code-points ranges))))
    :induct (integers-from-to min max)
    :enable (integers-from-to
             acl2::integers-from-to-of-noninteger-max
             intersectp-equal
             not-code-point-in-ranges-p-when-ranges-above-p
             code-point-fix
             ifix))

  (defrulel no-duplicatesp-equal-of-append-when-not-intersectp-equal
    (implies (and (no-duplicatesp-equal x)
                  (no-duplicatesp-equal y)
                  (not (intersectp-equal x y)))
             (no-duplicatesp-equal (append x y)))
    :induct (len x)
    :enable (append
             no-duplicatesp-equal
             intersectp-equal
             len))

  (defrulel no-duplicatesp-equal-of-range-list-code-points-when-above
    (implies (ranges-above-p bound ranges)
             (no-duplicatesp-equal (range-list-code-points ranges)))
    :induct (ranges-above-p bound ranges)
    :enable (ranges-above-p
             range-list-code-points
             range-code-points
             ifix)
    ;; This rule exchanges the two lists.
    :disable acl2::no-duplicatesp-equal-of-append-of-append)

  (defrule no-duplicatesp-equal-of-range-list-code-points
    (implies (ranges-normalized-p ranges)
             (no-duplicatesp-equal (range-list-code-points ranges)))
    :enable ranges-normalized-p))
