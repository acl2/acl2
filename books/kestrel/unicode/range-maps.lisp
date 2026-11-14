; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "range-sets")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ range-maps
  :parents (tables)
  :short "Maps from code points to values,
          as sorted lists of disjoint ranges with values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The enumerated and numeric properties
     of the Unicode Character Database,
     such as @('Canonical_Combining_Class'),
     are maps from code points to values,
     with a default value for most code points.
     We represent the part of such a map that differs from the default
     as a list of pairs @('((lo . hi) . value)'),
     where @('(lo . hi)') is a range of code points (see @(see range-sets))
     and @('value') is a non-@('nil') value
     that all the code points of the range have.")
   (xdoc::p
    "The list is sorted and its ranges are disjoint:
     each range ends before the next one starts.
     (Unlike in @(see range-sets), the ranges may be adjacent,
     as they are when adjacent ranges have different values.)
     This invariant is part of the recognizer @(tsee range-map-p),
     so it is checked, by evaluation,
     for each table generated from the database.")
   (xdoc::p
    "The lookup function returns @('nil')
     for the code points that are in no range,
     i.e. for those with the default value;
     the property functions built on it supply that value.")
   (xdoc::p
    "This book also has the recognizers of the range maps
     with particular types of values
     that the generated tables are instances of."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define range-map-p (x)
  :returns (yes/no booleanp)
  :short "Recognize maps from code points to values
          represented as sorted lists of disjoint ranges with values."
  (cond ((atom x) (null x))
        (t (and (consp (car x))
                (range-p (car (car x)))
                (not (null (cdr (car x))))
                (range-map-p (cdr x))
                (or (atom (cdr x))
                    (< (cdr (car (car x)))
                       (car (car (cadr x))))))))
  :guard-hints (("Goal" :expand (range-map-p (cdr x))))

  ///

  (defrule true-listp-when-range-map-p
    (implies (range-map-p x)
             (true-listp x))
    :rule-classes :compound-recognizer
    :induct t)

  (defrule range-map-p-of-cdr
    (implies (range-map-p x)
             (range-map-p (cdr x))))

  (defrule range-p-of-caar-when-range-map-p
    (implies (and (range-map-p x)
                  (consp x))
             (and (consp (car x))
                  (range-p (car (car x)))))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define range-map-lookup ((cp natp) (map range-map-p))
  :returns value
  :short "Look up a natural number in a range map."
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the value of the range that the number is in,
     or @('nil') if there is no such range.
     Since values are not @('nil'), there is no ambiguity.")
   (xdoc::p
    "The logical definition searches the whole list.
     The executable definition stops at the first range
     that starts after the number,
     because then all the following ranges do too."))
  (mbe :logic (and (consp map)
                   (if (and (<= (car (car (car map))) (nfix cp))
                            (<= (nfix cp) (cdr (car (car map)))))
                       (cdr (car map))
                     (range-map-lookup cp (cdr map))))
       :exec (cond ((endp map) nil)
                   ((< cp (car (car (car map)))) nil)
                   ((<= cp (cdr (car (car map)))) (cdr (car map)))
                   (t (range-map-lookup cp (cdr map)))))
  :hooks nil
  :verify-guards nil ; done below

  ///

  (fty::deffixequiv range-map-lookup
    :args ((cp natp)))

  (defruled range-map-lookup-when-below-first
    (implies (and (range-map-p map)
                  (consp map)
                  (< (nfix cp) (car (car (car map)))))
             (equal (range-map-lookup cp map)
                    nil))
    :induct t
    :enable (range-map-p range-p))

  (defruled range-map-lookup-of-cdr-when-below-first
    (implies (and (range-map-p map)
                  (consp map)
                  (< (nfix cp) (car (car (car map)))))
             (equal (range-map-lookup cp (cdr map))
                    nil))
    :use (:instance range-map-lookup-when-below-first (map (cdr map)))
    :enable (range-map-p range-p))

  (verify-guards range-map-lookup
    :hints (("Goal"
             :in-theory (enable range-map-lookup-of-cdr-when-below-first
                                nfix))))

  (defruled range-map-lookup-when-not-code-point-p
    (implies (and (range-map-p map)
                  (not (code-point-p (nfix cp))))
             (equal (range-map-lookup cp map)
                    nil))
    :induct t
    :enable (code-point-p nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ccc-value-p (x)
  :returns (yes/no booleanp)
  :short "Recognize the non-zero canonical combining classes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('Canonical_Combining_Class') property
     has values from 0 to 254 [UAX #44, Table 15].
     The value 0 is the default one,
     which is not in the range maps."))
  (and (integerp x)
       (<= 1 x)
       (<= x 254)))

;;;;;;;;;;;;;;;;;;;;

(define ccc-range-map-p (x)
  :returns (yes/no booleanp)
  :short "Recognize range maps whose values are
          non-zero canonical combining classes."
  (and (range-map-p x)
       (ccc-range-map-values-p x))

  :prepwork
  ((define ccc-range-map-values-p ((map range-map-p))
     :returns (yes/no booleanp)
     :parents nil
     (or (endp map)
         (and (ccc-value-p (cdr (car map)))
              (ccc-range-map-values-p (cdr map))))
     :hooks nil

     ///

     (defruled ccc-value-p-of-range-map-lookup
       (implies (and (ccc-range-map-values-p map)
                     (range-map-lookup cp map))
                (ccc-value-p (range-map-lookup cp map)))
       :induct t
       :enable range-map-lookup)))

  ///

  (defrule range-map-p-when-ccc-range-map-p
    (implies (ccc-range-map-p x)
             (range-map-p x)))

  (defrule ccc-value-p-of-range-map-lookup-when-ccc-range-map-p
    (implies (and (ccc-range-map-p map)
                  (range-map-lookup cp map))
             (ccc-value-p (range-map-lookup cp map)))
    :enable ccc-value-p-of-range-map-lookup))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-formatting-classes
  :short "The bidirectional classes
          of the explicit directional formatting characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the values of the @('Bidi_Class') property
     for the characters of [UAX #9, Sections 2.1 to 2.5]:
     the embeddings LRE and RLE,
     the overrides LRO and RLO,
     their terminator PDF,
     the isolates LRI, RLI and FSI,
     and their terminator PDI.
     We represent them as keywords."))

  (defconst *bidi-formatting-classes*
    '(:lre :rle :lro :rlo :pdf :lri :rli :fsi :pdi)))

;;;;;;;;;;;;;;;;;;;;

(define bidi-formatting-class-p (x)
  :returns (yes/no booleanp)
  :short "Recognize the bidirectional classes
          of the explicit directional formatting characters."
  (and (member-eq x *bidi-formatting-classes*) t))

;;;;;;;;;;;;;;;;;;;;

(define bidi-formatting-range-map-p (x)
  :returns (yes/no booleanp)
  :short "Recognize range maps whose values are bidirectional classes
          of explicit directional formatting characters."
  (and (range-map-p x)
       (bidi-formatting-range-map-values-p x))

  :prepwork
  ((define bidi-formatting-range-map-values-p ((map range-map-p))
     :returns (yes/no booleanp)
     :parents nil
     (or (endp map)
         (and (bidi-formatting-class-p (cdr (car map)))
              (bidi-formatting-range-map-values-p (cdr map))))
     :hooks nil

     ///

     (defruled bidi-formatting-class-p-of-range-map-lookup
       (implies (and (bidi-formatting-range-map-values-p map)
                     (range-map-lookup cp map))
                (bidi-formatting-class-p (range-map-lookup cp map)))
       :induct t
       :enable range-map-lookup)))

  ///

  (defrule range-map-p-when-bidi-formatting-range-map-p
    (implies (bidi-formatting-range-map-p x)
             (range-map-p x)))

  (defrule bidi-formatting-class-p-of-range-map-lookup-when-range-map-p
    (implies (and (bidi-formatting-range-map-p map)
                  (range-map-lookup cp map))
             (bidi-formatting-class-p (range-map-lookup cp map)))
    :enable bidi-formatting-class-p-of-range-map-lookup))
