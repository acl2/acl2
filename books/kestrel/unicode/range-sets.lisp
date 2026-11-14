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

(defxdoc+ range-sets
  :parents (tables)
  :short "Sets of code points, as sorted lists of disjoint ranges."
  :long
  (xdoc::topstring
   (xdoc::p
    "The binary properties of the Unicode Character Database,
     such as @('XID_Start'),
     are sets of code points.
     These sets are large but consist of relatively few ranges,
     which is also how the database lists them.
     We represent such a set as a list of ranges,
     each a pair @('(lo . hi)') of code points with @('lo <= hi'),
     standing for the code points from @('lo') to @('hi'), both included.")
   (xdoc::p
    "The list is sorted, and its ranges are disjoint and not adjacent:
     each range ends at least two code points
     before the next range starts.
     So the list consists of the maximal ranges of the set, in order,
     and two lists are equal exactly when they represent the same set.
     This invariant is part of the recognizer @(tsee range-set-p),
     so it is checked, by evaluation,
     for each table generated from the database.")
   (xdoc::p
    "Membership is defined, logically, as a plain search of the list.
     Its executable version stops as soon as it reaches a range
     that starts after the code point being looked up,
     which is correct because of the invariant;
     so looking up a small code point, e.g. an ASCII one, is fast.
     Larger code points take time proportional to the number of ranges."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define range-p (x)
  :returns (yes/no booleanp)
  :short "Recognize ranges of code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "A range is a pair @('(lo . hi)') of code points with @('lo <= hi')."))
  (and (consp x)
       (code-point-p (car x))
       (code-point-p (cdr x))
       (<= (car x) (cdr x)))

  ///

  (defrule range-p-forward
    (implies (range-p x)
             (and (consp x)
                  (natp (car x))
                  (natp (cdr x))
                  (<= (car x) (cdr x))
                  (<= (cdr x) #x10FFFF)))
    :rule-classes :forward-chaining
    :enable code-point-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define range-set-p (x)
  :returns (yes/no booleanp)
  :short "Recognize sets of code points
          represented as sorted lists of disjoint, non-adjacent ranges."
  (cond ((atom x) (null x))
        (t (and (range-p (car x))
                (range-set-p (cdr x))
                (or (atom (cdr x))
                    (< (+ 1 (cdr (car x)))
                       (car (cadr x)))))))
  :guard-hints (("Goal" :expand (range-set-p (cdr x))))

  ///

  (defrule true-listp-when-range-set-p
    (implies (range-set-p x)
             (true-listp x))
    :rule-classes :compound-recognizer
    :induct t)

  (defrule range-set-p-of-cdr
    (implies (range-set-p x)
             (range-set-p (cdr x))))

  (defrule range-p-of-car-when-range-set-p
    (implies (and (range-set-p x)
                  (consp x))
             (range-p (car x)))
    :rule-classes (:rewrite :forward-chaining))

  (defruled range-set-p-order
    (implies (and (range-set-p x)
                  (consp x)
                  (consp (cdr x)))
             (< (+ 1 (cdr (car x)))
                (car (cadr x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in-range-set-p ((cp natp) (set range-set-p))
  :returns (yes/no booleanp)
  :short "Check if a natural number is in a set of code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "A natural number that is not a code point is in no such set.")
   (xdoc::p
    "The logical definition searches the whole list.
     The executable definition stops at the first range
     that starts after the number,
     because then all the following ranges do too."))
  (mbe :logic (and (consp set)
                   (or (and (<= (car (car set)) (nfix cp))
                            (<= (nfix cp) (cdr (car set))))
                       (in-range-set-p cp (cdr set))))
       :exec (cond ((endp set) nil)
                   ((< cp (car (car set))) nil)
                   ((<= cp (cdr (car set))) t)
                   (t (in-range-set-p cp (cdr set)))))
  :hooks nil
  :verify-guards nil ; done below

  ///

  (fty::deffixequiv in-range-set-p
    :args ((cp natp)))

  (defruled not-in-range-set-p-when-below-first
    (implies (and (range-set-p set)
                  (consp set)
                  (< (nfix cp) (car (car set))))
             (not (in-range-set-p cp set)))
    :induct t
    :enable (range-set-p range-p))

  (defruled not-in-range-set-p-of-cdr-when-below-first
    (implies (and (range-set-p set)
                  (consp set)
                  (< (nfix cp) (car (car set))))
             (not (in-range-set-p cp (cdr set))))
    :use (:instance not-in-range-set-p-when-below-first (set (cdr set)))
    :enable (range-set-p range-p))

  (verify-guards in-range-set-p
    :hints (("Goal"
             :in-theory (enable not-in-range-set-p-of-cdr-when-below-first
                                nfix))))

  (defrule code-point-p-when-in-range-set-p
    (implies (and (in-range-set-p cp set)
                  (range-set-p set)
                  (natp cp))
             (code-point-p cp))
    :rule-classes :forward-chaining
    :induct t
    :enable (code-point-p nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define range-set-count ((set range-set-p))
  :returns (count natp
                  :hyp (range-set-p set)
                  :hints (("Goal"
                           :induct t
                           :in-theory (enable range-set-p range-p
                                              code-point-p natp fix))))
  :short "Number of code points in a set of code points."
  (cond ((endp set) 0)
        (t (+ (+ 1 (- (cdr (car set)) (car (car set))))
              (range-set-count (cdr set)))))
  :hooks nil
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define range-within-range-set-p ((range range-p) (set range-set-p))
  :returns (yes/no booleanp)
  :short "Check if a range is within one of the ranges of a set."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the ranges of a set are not adjacent,
     this is the case exactly when
     all the code points of the range are in the set;
     but we only need, and only prove, the `if' direction."))
  (and (consp set)
       (or (and (<= (car (car set)) (car range))
                (<= (cdr range) (cdr (car set))))
           (range-within-range-set-p range (cdr set))))
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable range-p)))

  ///

  (defruled in-range-set-p-when-range-within-range-set-p
    (implies (and (range-within-range-set-p range set)
                  (<= (car range) (nfix cp))
                  (<= (nfix cp) (cdr range)))
             (in-range-set-p cp set))
    :induct t
    :enable (in-range-set-p nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define range-set-subset-p ((sub range-set-p) (sup range-set-p))
  :returns (yes/no booleanp)
  :short "Check if every range of a set
          is within one of the ranges of another set."
  :long
  (xdoc::topstring
   (xdoc::p
    "If this is the case, the first set is a subset of the second:
     see the theorem.
     So relations between properties,
     e.g. that every @('XID_Start') code point
     is also an @('XID_Continue') code point,
     are proved by evaluating this function on the tables."))
  (or (endp sub)
      (and (range-within-range-set-p (car sub) sup)
           (range-set-subset-p (cdr sub) sup)))
  :hooks nil

  ///

  (defruled in-range-set-p-when-range-set-subset-p
    (implies (and (range-set-subset-p sub sup)
                  (in-range-set-p cp sub))
             (in-range-set-p cp sup))
    :induct t
    :enable (in-range-set-p
             in-range-set-p-when-range-within-range-set-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection scalar-value-range-set
  :short "The set of the Unicode scalar values, as a range set."

  (defconst *scalar-value-range-set*
    '((#x0000 . #xD7FF)
      (#xE000 . #x10FFFF)))

  (assert-event (range-set-p *scalar-value-range-set*))

  (defruled scalar-value-p-when-in-scalar-value-range-set
    (implies (and (in-range-set-p cp *scalar-value-range-set*)
                  (natp cp))
             (scalar-value-p cp))
    :enable (in-range-set-p scalar-value-p-alt-def nfix)
    :disable scalar-value-p))
