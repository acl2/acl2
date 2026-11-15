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
(include-book "maps")

(include-book "data/v16.0.0/derived-combining-class")
(include-book "data/v17.0.0/derived-combining-class")
(include-book "data/v18.0.0/derived-combining-class")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

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
  :returns (map combining-class-mapp)
  :short "The map from the code points
          whose @('Canonical_Combining_Class') is not 0
          to their classes,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *canonical-combining-class-v16.0.0*
                :v17.0.0 *canonical-combining-class-v17.0.0*
                :v18.0.0 *canonical-combining-class-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-combining-class ((cp code-point-p) (ver versionp))
  :returns (ccc ubyte8p)
  :short "The @('Canonical_Combining_Class') of a code point,
          in a version of Unicode."
  (combining-class-map-lookup cp (canonical-combining-class-map ver))
  :hooks (:fix)

  ///

  (defrule natp-of-canonical-combining-class
    (natp (canonical-combining-class cp ver))
    :rule-classes :type-prescription)

  ;; We prove the next two theorems
  ;; by checking them on every code point, for each version.

  (local
   (define class-ok ((cp code-point-p) (map combining-class-mapp))
     :returns (yes/no booleanp)
     (b* ((ccc (combining-class-map-lookup cp map)))
       (and (<= ccc 254)
            (or (>= (code-point-fix cp) #x300)
                (equal ccc 0))))))

  (local
   (std::deflist class-ok-listp (x map)
     :guard (and (code-point-listp x)
                 (combining-class-mapp map))
     (class-ok x map)))

  (defrulel class-ok-listp-of-all-code-points
    (class-ok-listp (all-code-points) (canonical-combining-class-map ver))
    :enable (canonical-combining-class-map
             (:e all-code-points))
    :disable class-ok-listp-of-cons)

  (defrule canonical-combining-class-upper-bound
    (<= (canonical-combining-class cp ver) 254)
    :rule-classes :linear
    :enable class-ok
    :use (:instance class-ok-when-member-equal-of-class-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (map (canonical-combining-class-map ver))))

  (defruled canonical-combining-class-when-below-300
    (implies (< (code-point-fix cp) #x300)
             (equal (canonical-combining-class cp ver)
                    0))
    :enable class-ok
    :use (:instance class-ok-when-member-equal-of-class-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (map (canonical-combining-class-map ver)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define starter-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is a starter, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if its @('Canonical_Combining_Class') is 0 [Unicode, D107]."))
  (equal (canonical-combining-class cp ver) 0)
  :hooks (:fix)

  ///

  (defruled starter-p-when-below-300
    (implies (< (code-point-fix cp) #x300)
             (starter-p cp ver))
    :enable canonical-combining-class-when-below-300))
