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

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ nat-maps
  :parents (tables)
  :short "Maps from natural numbers to values, as sorted alists."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some properties of the Unicode Character Database,
     such as @('Decomposition_Mapping'),
     have a value of their own for each code point that has one,
     so that ranges do not help.
     We represent such a map as an alist
     from natural numbers to non-@('nil') values,
     whose keys are strictly increasing.
     The keys are code points for the tables generated from the database;
     the composition tables, which are computed from those,
     have keys that encode pairs of code points.")
   (xdoc::p
    "The invariant is part of the recognizer @(tsee nat-map-p),
     so it is checked, by evaluation,
     for each table generated from the database.")
   (xdoc::p
    "The lookup function returns @('nil') for the keys that are not present.
     Its logical definition searches the whole list.
     Its executable definition stops at the first key
     that is greater than the one being looked up,
     so looking up a small key is fast,
     while a large one takes time proportional to the size of the map.")
   (xdoc::p
    "This book also has the recognizer of the nat maps
     with the particular type of values
     that the generated decomposition tables are instances of."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nat-map-p (x)
  :returns (yes/no booleanp)
  :short "Recognize maps from natural numbers to non-@('nil') values
          represented as alists with strictly increasing keys."
  (cond ((atom x) (null x))
        (t (and (consp (car x))
                (natp (car (car x)))
                (not (null (cdr (car x))))
                (nat-map-p (cdr x))
                (or (atom (cdr x))
                    (< (car (car x))
                       (car (cadr x)))))))
  :guard-hints (("Goal" :expand (nat-map-p (cdr x))))

  ///

  (defrule true-listp-when-nat-map-p
    (implies (nat-map-p x)
             (true-listp x))
    :rule-classes :compound-recognizer
    :induct t)

  (defrule nat-map-p-of-cdr
    (implies (nat-map-p x)
             (nat-map-p (cdr x))))

  (defrule natp-of-caar-when-nat-map-p
    (implies (and (nat-map-p x)
                  (consp x))
             (and (consp (car x))
                  (natp (car (car x)))))
    :rule-classes :forward-chaining)

  (defruled cdar-when-nat-map-p
    (implies (and (nat-map-p x)
                  (consp x))
             (cdr (car x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nat-map-lookup ((key natp) (map nat-map-p))
  :returns value
  :short "Look up a natural number in a nat map."
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the value associated with the key,
     or @('nil') if the key is not in the map.
     Since values are not @('nil'), there is no ambiguity."))
  (mbe :logic (and (consp map)
                   (if (equal (car (car map)) (nfix key))
                       (cdr (car map))
                     (nat-map-lookup key (cdr map))))
       :exec (cond ((endp map) nil)
                   ((< key (car (car map))) nil)
                   ((= key (car (car map))) (cdr (car map)))
                   (t (nat-map-lookup key (cdr map)))))
  :hooks nil
  :verify-guards nil ; done below

  ///

  (fty::deffixequiv nat-map-lookup
    :args ((key natp)))

  (defruled nat-map-lookup-when-below-first
    (implies (and (nat-map-p map)
                  (consp map)
                  (< (nfix key) (car (car map))))
             (equal (nat-map-lookup key map)
                    nil))
    :induct t
    :enable nat-map-p)

  (defruled nat-map-lookup-of-cdr-when-below-first
    (implies (and (nat-map-p map)
                  (consp map)
                  (< (nfix key) (car (car map))))
             (equal (nat-map-lookup key (cdr map))
                    nil))
    :use (:instance nat-map-lookup-when-below-first (map (cdr map)))
    :enable nat-map-p)

  (verify-guards nat-map-lookup
    :hints (("Goal"
             :in-theory (enable nat-map-lookup-of-cdr-when-below-first
                                nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nat-map-put ((key natp) val (map nat-map-p))
  :returns new-map
  :short "Associate a value with a key in a nat map."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the key is already in the map, its value is replaced."))
  (b* ((key (lnfix key)))
    (cond ((endp map) (list (cons key val)))
          ((< key (car (car map))) (cons (cons key val) map))
          ((= key (car (car map))) (cons (cons key val) (cdr map)))
          (t (cons (car map) (nat-map-put key val (cdr map))))))
  :measure (len map)
  :hooks nil
  :verify-guards nil ; done below

  ///

  (fty::deffixequiv nat-map-put
    :args ((key natp)))

  (defruled car-of-car-of-nat-map-put
    (implies (nat-map-p map)
             (equal (car (car (nat-map-put key val map)))
                    (if (or (atom map)
                            (<= (nfix key) (car (car map))))
                        (nfix key)
                      (car (car map)))))
    :expand (nat-map-put key val map)
    :enable nat-map-p)

  (defrule nat-map-p-of-nat-map-put
    (implies (and (nat-map-p map)
                  val)
             (nat-map-p (nat-map-put key val map)))
    :induct t
    :enable (nat-map-p nfix car-of-car-of-nat-map-put))

  (verify-guards nat-map-put)

  (defrule nat-map-lookup-of-nat-map-put
    (implies (nat-map-p map)
             (equal (nat-map-lookup key1 (nat-map-put key2 val map))
                    (if (equal (nfix key1) (nfix key2))
                        val
                      (nat-map-lookup key1 map))))
    :induct t
    :enable (nat-map-lookup
             nat-map-lookup-when-below-first
             nat-map-lookup-of-cdr-when-below-first
             nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decomposition-map-p (x)
  :returns (yes/no booleanp)
  :short "Recognize nat maps from scalar values
          to non-empty lists of scalar values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the tables of decomposition mappings:
     no surrogate has a decomposition mapping,
     and no decomposition mapping contains a surrogate.
     So decomposing scalar values gives scalar values."))
  (and (nat-map-p x)
       (decomposition-map-entries-p x))

  :prepwork
  ((define decomposition-map-entries-p ((map nat-map-p))
     :returns (yes/no booleanp)
     :parents nil
     (or (endp map)
         (and (scalar-value-p (car (car map)))
              (consp (cdr (car map)))
              (scalar-value-listp (cdr (car map)))
              (decomposition-map-entries-p (cdr map))))
     :hooks nil

     ///

     (defruled scalar-value-listp-of-nat-map-lookup
       (implies (decomposition-map-entries-p map)
                (scalar-value-listp (nat-map-lookup key map)))
       :induct t
       :enable nat-map-lookup)

     (defruled consp-of-nat-map-lookup
       (implies (decomposition-map-entries-p map)
                (iff (consp (nat-map-lookup key map))
                     (nat-map-lookup key map)))
       :induct t
       :enable nat-map-lookup)

     (defruled scalar-value-p-when-nat-map-lookup
       (implies (and (decomposition-map-entries-p map)
                     (nat-map-lookup key map))
                (scalar-value-p (nfix key)))
       :induct t
       :enable nat-map-lookup)))

  ///

  (defrule nat-map-p-when-decomposition-map-p
    (implies (decomposition-map-p x)
             (nat-map-p x)))

  (defrule decomposition-map-p-of-nil
    (decomposition-map-p nil)
    :enable (nat-map-p decomposition-map-entries-p))

  (defrule scalar-value-listp-of-nat-map-lookup-when-decomposition-map-p
    (implies (decomposition-map-p map)
             (scalar-value-listp (nat-map-lookup key map)))
    :enable scalar-value-listp-of-nat-map-lookup)

  (defrule consp-of-nat-map-lookup-when-decomposition-map-p
    (implies (decomposition-map-p map)
             (iff (consp (nat-map-lookup key map))
                  (nat-map-lookup key map)))
    :enable consp-of-nat-map-lookup)

  (defruled scalar-value-p-when-nat-map-lookup-when-decomposition-map-p
    (implies (and (decomposition-map-p map)
                  (nat-map-lookup key map))
             (scalar-value-p (nfix key)))
    :enable scalar-value-p-when-nat-map-lookup))
