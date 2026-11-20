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

(defxdoc+ variation-selectors
  :parents (unicode)
  :short "The @('Variation_Selector') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variation selector follows another character
     and asks for a particular form of it:
     for example, U+FE0F after certain symbols
     asks for their emoji form.
     A variation selector has no appearance of its own.
     We take the property from the file @('PropList.txt')
     of the Unicode Character Database, for each supported version.")
   (xdoc::p
    "There are 260 variation selectors, in four ranges,
     and they are the same in all the supported versions:
     see the theorem @('variation-selector-p-alt-def')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define variation-selector-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Variation_Selector') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *variation-selector-v16.0.0*
                :v17.0.0 *variation-selector-v17.0.0*
                :v18.0.0 *variation-selector-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define variation-selector-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the
          @('Variation_Selector') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (variation-selector-ranges ver))
  :hooks (:fix)

  ///

  (defruled variation-selector-p-alt-def
    (equal (variation-selector-p cp ver)
           (b* ((cp (code-point-fix cp)))
             (or (and (<= #x180B cp) ; MONGOLIAN FREE VARIATION SELECTOR
                      (<= cp #x180D)) ; ONE, TWO and THREE
                 (equal cp #x180F) ; MONGOLIAN FREE VARIATION SELECTOR FOUR
                 (and (<= #xFE00 cp) ; VARIATION SELECTOR-1
                      (<= cp #xFE0F)) ; to VARIATION SELECTOR-16
                 (and (<= #xE0100 cp) ; VARIATION SELECTOR-17
                      (<= cp #xE01EF))))) ; to VARIATION SELECTOR-256
    :enable (variation-selector-ranges
             code-point-in-range-p)))
