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

(defxdoc+ prepended-concatenation-marks
  :parents (unicode)
  :short "The @('Prepended_Concatenation_Mark') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "A prepended concatenation mark is a format character
     that is written before a sequence of digits or letters
     and is displayed together with that sequence, around or under it:
     for example U+0600 ARABIC NUMBER SIGN.
     Unlike most format characters, these are visible.
     We take the property from the file @('PropList.txt')
     of the Unicode Character Database, for each supported version.")
   (xdoc::p
    "The property is the same in all the supported versions:
     see the theorem @('prepended-concatenation-mark-p-same-in-all-versions').
     The standard does not promise that;
     the theorem is checked again when a version is added,
     and if it fails then, the property has changed."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prepended-concatenation-mark-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Prepended_Concatenation_Mark') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *prepended-concatenation-mark-v16.0.0*
                :v17.0.0 *prepended-concatenation-mark-v17.0.0*
                :v18.0.0 *prepended-concatenation-mark-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prepended-concatenation-mark-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the
          @('Prepended_Concatenation_Mark') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (prepended-concatenation-mark-ranges ver))
  :hooks (:fix)

  ///

  (defrule prepended-concatenation-mark-p-same-in-all-versions
    (equal (prepended-concatenation-mark-p cp ver1)
           (prepended-concatenation-mark-p cp ver2))
    :rule-classes nil
    :enable prepended-concatenation-mark-ranges))
