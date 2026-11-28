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
(include-book "ranges")

(include-book "data/v16.0.0/prop-list")
(include-book "data/v17.0.0/prop-list")
(include-book "data/v18.0.0/prop-list")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ noncharacters
  :parents (unicode)
  :short "The @('Noncharacter_Code_Point') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "A noncharacter is a code point that is
     permanently reserved for internal use
     and will never be assigned to a character [Unicode, D14].
     There are 66 of them:
     the 32 code points from @('#xFDD0') to @('#xFDEF'),
     and the last two code points of each of the 17 planes,
     that is, the code points whose last four hexadecimal digits
     are @('FFFE') or @('FFFF').
     We take the property from the file @('PropList.txt')
     of the Unicode Character Database, for each supported version.")
   (xdoc::p
    "The theorem @('noncharacter-p-alt-def') says that
     the tables agree with that description, in every supported version.
     It is proved by checking every code point."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define noncharacter-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Noncharacter_Code_Point') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *noncharacter-code-point-v16.0.0*
                :v17.0.0 *noncharacter-code-point-v17.0.0*
                :v18.0.0 *noncharacter-code-point-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define noncharacter-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the
          @('Noncharacter_Code_Point') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (noncharacter-ranges ver))
  :hooks (:fix)

  ///

  (local
   (define noncharacter-ok ((cp code-point-p) (ranges range-listp))
     :returns (yes/no booleanp)
     (b* ((cp (code-point-fix cp)))
       (equal (code-point-in-ranges-p cp ranges)
              (or (and (<= #xFDD0 cp)
                       (<= cp #xFDEF))
                  (equal (logand cp #xFFFE) #xFFFE))))
     :hooks nil))

  (local
   (std::deflist noncharacter-ok-listp (x ranges)
     :guard (and (code-point-listp x)
                 (range-listp ranges))
     (noncharacter-ok x ranges)))

  (defrulel noncharacter-ok-listp-of-all-code-points
    (noncharacter-ok-listp (all-code-points) (noncharacter-ranges ver))
    :enable (noncharacter-ranges
             (:e all-code-points))
    :disable noncharacter-ok-listp-of-cons)

  (defruled noncharacter-p-alt-def
    (equal (noncharacter-p cp ver)
           (b* ((cp (code-point-fix cp)))
             (or (and (<= #xFDD0 cp)
                      (<= cp #xFDEF))
                 (equal (logand cp #xFFFE) #xFFFE))))
    :enable noncharacter-ok
    :use (:instance noncharacter-ok-when-member-equal-of-noncharacter-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ranges (noncharacter-ranges ver))))

  (defrule noncharacter-p-same-in-all-versions
    (equal (noncharacter-p cp ver1)
           (noncharacter-p cp ver2))
    :rule-classes nil
    :enable noncharacter-p-alt-def))
