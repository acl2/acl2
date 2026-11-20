; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "property-relations")
(include-book "quick-check-theorems")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ identifier-status-and-normalization
  :parents (identifier-status)
  :short "Normalization Form KC (NFKC) changes no code point
          whose @('Identifier_Status') is @('Allowed'),
          and changes every code point
          whose @('Identifier_Type') has @('Not_NFKC')."
  :long
  (xdoc::topstring
   (xdoc::p
    "NFKC is compatibility decomposition
     followed by canonical composition (see @(see normalization)).
     The profile of [UTS #39, Section 3.1] leaves out
     the characters that NFKC changes,
     so that an identifier of allowed characters
     has no character that would be replaced by a look-alike.
     The type @('Not_NFKC') [UTS #39, Table 1]
     is the type of those characters.")
   (xdoc::p
    "Here these are theorems about the normalization function,
     for a code point taken alone (see @(tsee nfkc-changes-p)).
     They follow from the theorems of @(see identifier-type-relations),
     which are about the @('NFKC_Quick_Check') property,
     and from the theorem that NFKC changes a code point
     exactly when the value of that property is `no'.")
   (xdoc::p
    "The converse of the second theorem fails for seven code points
     that NFKC changes and whose type is not @('Not_NFKC'):
     U+0149, U+0F77, U+0F79, U+2329 and U+232A,
     whose type is @('Deprecated'),
     and U+3164 and U+FFA0, whose type is @('Default_Ignorable').
     None of the seven is @('Allowed')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule not-nfkc-changes-p-when-identifier-allowed-p
  (implies (identifier-allowed-p cp ver)
           (not (nfkc-changes-p cp ver)))
  :enable (nfkc-changes-p-in-terms-of-quick-check
           not-nfkc-quick-check-no-when-identifier-allowed-p))

(defrule nfkc-of-list-when-identifier-allowed-p
  (implies (identifier-allowed-p cp ver)
           (equal (nfkc (list cp) ver)
                  (list (code-point-fix cp))))
  :enable nfkc-changes-p
  :disable not-nfkc-changes-p-when-identifier-allowed-p
  :use not-nfkc-changes-p-when-identifier-allowed-p)

(defrule nfkc-changes-p-when-identifier-type-not-nfkc
  (implies (member-equal (identifier-type-not-nfkc)
                         (code-point-identifier-types cp ver))
           (nfkc-changes-p cp ver))
  :enable (nfkc-changes-p-in-terms-of-quick-check
           nfkc-quick-check-no-when-identifier-type-not-nfkc)
  :disable ((:e identifier-type-not-nfkc)))
