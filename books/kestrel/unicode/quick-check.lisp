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
(include-book "range-sets")

(include-book "data/v16.0.0/derived-normalization-props")
(include-book "data/v17.0.0/derived-normalization-props")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ quick-check
  :parents (normalization)
  :short "The quick check properties of the normalization forms."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each normalization form there is a property,
     e.g. @('NFC_Quick_Check'),
     that says whether a code point may occur in a text in that form:
     yes, no, or maybe
     [UAX #15, Section 9].
     The answer is `no' for a code point that the form always replaces;
     it is `maybe', for the forms NFC and NFKC,
     for a code point that composes with some code point before it,
     or whose decomposition starts with such a code point,
     so that whether it stays depends on what precedes it.
     These properties make it possible to tell that most texts
     are already normalized without normalizing them.")
   (xdoc::p
    "We take these derived properties
     from the file @('DerivedNormalizationProps.txt')
     of the Unicode Character Database, for each supported version;
     we do not recompute them.
     The tables have the code points whose value is `no' or `maybe';
     all the others have the value `yes',
     which is the default that the file specifies.")
   (xdoc::p
    "The normalization functions of this library do not use these properties.
     The books in the @('tests') directory check, for every code point,
     that the properties agree with those functions,
     which validates the functions against data
     that the Unicode Consortium derived independently."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define quick-check-value-p (x)
  :returns (yes/no booleanp)
  :short "Recognize the values of the quick check properties."
  (and (member-eq x '(:yes :no :maybe)) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nfd-quick-check-no-set ((ver versionp))
  :returns (set range-set-p)
  :short "The set of the code points
          whose @('NFD_Quick_Check') is `no',
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *nfd-quick-check-no-v16.0.0*
                :v17.0.0 *nfd-quick-check-no-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;

(define nfc-quick-check-no-set ((ver versionp))
  :returns (set range-set-p)
  :short "The set of the code points
          whose @('NFC_Quick_Check') is `no',
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *nfc-quick-check-no-v16.0.0*
                :v17.0.0 *nfc-quick-check-no-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;

(define nfc-quick-check-maybe-set ((ver versionp))
  :returns (set range-set-p)
  :short "The set of the code points
          whose @('NFC_Quick_Check') is `maybe',
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *nfc-quick-check-maybe-v16.0.0*
                :v17.0.0 *nfc-quick-check-maybe-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;

(define nfkd-quick-check-no-set ((ver versionp))
  :returns (set range-set-p)
  :short "The set of the code points
          whose @('NFKD_Quick_Check') is `no',
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *nfkd-quick-check-no-v16.0.0*
                :v17.0.0 *nfkd-quick-check-no-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;

(define nfkc-quick-check-no-set ((ver versionp))
  :returns (set range-set-p)
  :short "The set of the code points
          whose @('NFKC_Quick_Check') is `no',
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *nfkc-quick-check-no-v16.0.0*
                :v17.0.0 *nfkc-quick-check-no-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;

(define nfkc-quick-check-maybe-set ((ver versionp))
  :returns (set range-set-p)
  :short "The set of the code points
          whose @('NFKC_Quick_Check') is `maybe',
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *nfkc-quick-check-maybe-v16.0.0*
                :v17.0.0 *nfkc-quick-check-maybe-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nfd-quick-check ((cp natp) (ver versionp))
  :returns (value quick-check-value-p)
  :short "The @('NFD_Quick_Check') of a code point,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "For this form the value is never `maybe'."))
  (cond ((in-range-set-p cp (nfd-quick-check-no-set ver)) :no)
        (t :yes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nfc-quick-check ((cp natp) (ver versionp))
  :returns (value quick-check-value-p)
  :short "The @('NFC_Quick_Check') of a code point,
          in a version of Unicode."
  (cond ((in-range-set-p cp (nfc-quick-check-no-set ver)) :no)
        ((in-range-set-p cp (nfc-quick-check-maybe-set ver)) :maybe)
        (t :yes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nfkd-quick-check ((cp natp) (ver versionp))
  :returns (value quick-check-value-p)
  :short "The @('NFKD_Quick_Check') of a code point,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "For this form the value is never `maybe'."))
  (cond ((in-range-set-p cp (nfkd-quick-check-no-set ver)) :no)
        (t :yes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nfkc-quick-check ((cp natp) (ver versionp))
  :returns (value quick-check-value-p)
  :short "The @('NFKC_Quick_Check') of a code point,
          in a version of Unicode."
  (cond ((in-range-set-p cp (nfkc-quick-check-no-set ver)) :no)
        ((in-range-set-p cp (nfkc-quick-check-maybe-set ver)) :maybe)
        (t :yes)))
