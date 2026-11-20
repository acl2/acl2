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

(defxdoc+ join-controls
  :parents (unicode)
  :short "The @('Join_Control') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "The join controls are the two format characters
     that ask for, or prevent, a joined form of the characters around them:
     U+200C ZERO WIDTH NON-JOINER and U+200D ZERO WIDTH JOINER.
     Some scripts need them in the spelling of ordinary words,
     and the joiner also builds sequences of emoji.
     They have no appearance of their own.
     We take the property from the file @('PropList.txt')
     of the Unicode Character Database, for each supported version.")
   (xdoc::p
    "The property is the same in all the supported versions:
     see the theorem @('join-control-p-alt-def')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define join-control-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Join_Control') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *join-control-v16.0.0*
                :v17.0.0 *join-control-v17.0.0*
                :v18.0.0 *join-control-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define join-control-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Join_Control') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (join-control-ranges ver))
  :hooks (:fix)

  ///

  (defruled join-control-p-alt-def
    (equal (join-control-p cp ver)
           (b* ((cp (code-point-fix cp)))
             (or (equal cp #x200C) ; ZERO WIDTH NON-JOINER
                 (equal cp #x200D)))) ; ZERO WIDTH JOINER
    :enable (join-control-ranges
             code-point-in-range-p)))
