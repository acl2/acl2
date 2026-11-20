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

(defxdoc+ deprecated
  :parents (unicode)
  :short "The @('Deprecated') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "A deprecated character is one
     whose use the Unicode Standard strongly discourages
     [Unicode, D13];
     it stays in the standard, and stays deprecated,
     but other characters or other mechanisms are to be used instead.
     An example is U+0149 LATIN SMALL LETTER N PRECEDED BY APOSTROPHE.
     We take the property from the file @('PropList.txt')
     of the Unicode Character Database, for each supported version."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deprecated-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Deprecated') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *deprecated-v16.0.0*
                :v17.0.0 *deprecated-v17.0.0*
                :v18.0.0 *deprecated-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deprecated-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Deprecated') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (deprecated-ranges ver))
  :hooks (:fix))
