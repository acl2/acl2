; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "versions")
(include-book "range-maps")

(include-book "data/v16.0.0/derived-combining-class")
(include-book "data/v17.0.0/derived-combining-class")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ combining-classes
  :parents (normalization)
  :short "The @('Canonical_Combining_Class') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "This property assigns to each code point a number from 0 to 254.
     A code point whose class is 0 is called a starter [Unicode, D107];
     the others are combining marks of various kinds,
     and their classes say which of them may be reordered
     without changing the meaning of a text:
     see @(see canonical-ordering).")
   (xdoc::p
    "We take the property from the file
     @('extracted/DerivedCombiningClass.txt')
     of the Unicode Character Database, for each supported version.
     The tables have the code points whose class is not 0;
     all the other code points have class 0,
     which is the default that the file specifies
     and which is, in particular, the class of every unassigned code point
     and of every surrogate."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-combining-class-map ((ver versionp))
  :returns (map ccc-range-map-p)
  :short "The map from the code points
          whose @('Canonical_Combining_Class') is not 0
          to their classes,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *canonical-combining-class-v16.0.0*
                :v17.0.0 *canonical-combining-class-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-combining-class ((cp natp) (ver versionp))
  :returns (ccc natp :rule-classes :type-prescription)
  :short "The @('Canonical_Combining_Class') of a code point,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The class of a natural number that is not a code point is 0."))
  (b* ((ccc (range-map-lookup cp (canonical-combining-class-map ver))))
    (if ccc
        (mbe :logic (nfix ccc) :exec ccc)
      0))
  :guard-hints (("Goal"
                 :use (:instance
                       ccc-value-p-of-range-map-lookup-when-ccc-range-map-p
                       (map (canonical-combining-class-map ver)))
                 :in-theory
                 (e/d (ccc-value-p nfix)
                      (ccc-value-p-of-range-map-lookup-when-ccc-range-map-p))))

  ///

  (defrule canonical-combining-class-upper-bound
    (<= (canonical-combining-class cp ver) 254)
    :rule-classes :linear
    :use (:instance ccc-value-p-of-range-map-lookup-when-ccc-range-map-p
                    (map (canonical-combining-class-map ver)))
    :enable (ccc-value-p nfix)
    :disable ccc-value-p-of-range-map-lookup-when-ccc-range-map-p)

  (defruled canonical-combining-class-when-below-300
    (implies (< (nfix cp) #x300)
             (equal (canonical-combining-class cp ver)
                    0))
    :enable (canonical-combining-class-map
             range-map-lookup-when-below-first)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define starter-p ((cp natp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is a starter, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if its @('Canonical_Combining_Class') is 0 [Unicode, D107]."))
  (equal (canonical-combining-class cp ver) 0)

  ///

  (defruled starter-p-when-below-300
    (implies (< (nfix cp) #x300)
             (starter-p cp ver))
    :enable canonical-combining-class-when-below-300))
