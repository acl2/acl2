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

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pattern-syntax
  :parents (unicode)
  :short "The @('Pattern_Syntax') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the property that [UAX #31] provides
     for the characters that a programming language
     or another formal notation may use as its syntax:
     punctuation and symbols,
     as opposed to the characters of identifiers and to white space.
     We take it from the file @('PropList.txt')
     of the Unicode Character Database, for each supported version.")
   (xdoc::p
    "The Unicode stability policies say that
     this property does not change,
     and indeed it is the same in all the supported versions:
     see the theorem @('pattern-syntax-p-same-in-all-versions').
     Its version argument is there for uniformity,
     and so that the claim is checked rather than assumed
     when a version is added.")
   (xdoc::p
    "No code point has both this property
     and @('Pattern_White_Space') or @('XID_Continue'):
     see @(see property-relations)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pattern-syntax-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Pattern_Syntax') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *pattern-syntax-v16.0.0*
                :v17.0.0 *pattern-syntax-v17.0.0*
                :v18.0.0 *pattern-syntax-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pattern-syntax-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Pattern_Syntax') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (pattern-syntax-ranges ver))
  :hooks (:fix)

  ///

  (defrule pattern-syntax-p-same-in-all-versions
    (equal (pattern-syntax-p cp ver1)
           (pattern-syntax-p cp ver2))
    :rule-classes nil
    :enable pattern-syntax-ranges))
