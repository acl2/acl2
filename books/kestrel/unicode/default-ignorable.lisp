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

(include-book "data/v16.0.0/derived-core-properties")
(include-book "data/v17.0.0/derived-core-properties")
(include-book "data/v18.0.0/derived-core-properties")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ default-ignorable
  :parents (unicode)
  :short "The @('Default_Ignorable_Code_Point') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "A code point with this property is one that
     should not be displayed at all,
     by a renderer that does not support it,
     unless the renderer is asked to show hidden characters
     [Unicode, Section 5.21].
     The format controls are here, such as the joiners
     and the bidirectional controls,
     and so are the variation selectors:
     see @(see property-relations).
     Such characters are normally invisible,
     so a lexer may have to reject or report them.")
   (xdoc::p
    "The property is derived from other properties.
     We take it from the file @('DerivedCoreProperties.txt')
     of the Unicode Character Database, for each supported version;
     we do not recompute it.")
   (xdoc::p
    "Most of the code points that have the property are unassigned:
     they are set aside for characters of this kind
     that may be added in the future.
     The stability policies do not say that the property never changes."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define default-ignorable-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Default_Ignorable_Code_Point') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *default-ignorable-code-point-v16.0.0*
                :v17.0.0 *default-ignorable-code-point-v17.0.0*
                :v18.0.0 *default-ignorable-code-point-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define default-ignorable-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the
          @('Default_Ignorable_Code_Point') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (default-ignorable-ranges ver))
  :hooks (:fix))
