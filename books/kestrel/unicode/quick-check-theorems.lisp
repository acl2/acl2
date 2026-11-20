; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "quick-check")
(include-book "normalization")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ quick-check-theorems
  :parents (quick-check)
  :short "The quick check is exact for the two decomposed normalization forms,
          NFD and NFKD."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here NFD and NFKD are Normalization Forms D and KD,
     which are canonical decomposition and compatibility decomposition
     (see @(see normalization) for the names of the four forms).
     Their quick check properties are
     @('NFD_Quick_Check') and @('NFKD_Quick_Check')
     (see @(see quick-check)),
     which have no `maybe' values [UAX #15, Section 9].")
   (xdoc::p
    "The quick check of [UAX #15, Section 9] goes through a text once.
     Its answer is `no' if it finds a code point
     whose quick check value is `no',
     or a code point that is out of canonical order
     with the one before it
     (see @(see canonical-ordering));
     otherwise, if it finds a code point whose value is `maybe',
     its answer is `maybe';
     otherwise its answer is `yes'.
     So, for the two decomposed forms,
     its answer is `yes' exactly when
     every code point of the text has the value `yes'
     and the text is in canonical order.")
   (xdoc::p
    "We prove that this is right:
     in every supported version of Unicode,
     a list of code points is in NFD
     (see @(tsee nfd-memberp))
     exactly when all its code points
     have the value `yes' for @('NFD_Quick_Check')
     and the list is in canonical order;
     and the same holds for NFKD
     (see @(tsee nfkd-memberp))
     and @('NFKD_Quick_Check').
     So an implementation can use the quick check for these two forms
     instead of normalizing the text and comparing.")
   (xdoc::p
    "The normalization functions of this library
     do not use the quick check properties,
     which we take from a file of the Unicode Character Database.
     So these theorems also say that
     the values of the two properties in that file
     are the ones that follow from the decomposition mappings:
     the value of a code point is `yes'
     exactly when the code point is its own decomposition,
     canonical for NFD, compatibility for NFKD.
     We prove this by checking it on every code point, for each version;
     so adding a version checks it for that version.")
   (xdoc::p
    "The corresponding theorems for the two composed forms,
     NFC and NFKC, whose properties have `maybe' values,
     are not here yet.
     For those two forms we only prove
     which code points have the value `no': see @(see quick-check-no)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The check on a code point, for a table of the code points
;; whose value is `no' and for a map of decompositions:
;; the code point is in the table
;; exactly when it is not its own decomposition.
;; The decomposition is as in the function DECOMPOSITION.

(local
 (define value-ok ((cp code-point-p)
                   (no-ranges range-listp)
                   (full decomposition-mapp))
   :returns (yes/no booleanp)
   (b* ((cp (code-point-fix cp))
        (decomposition (if (hangul-syllable-p cp)
                           (hangul-syllable-decomposition cp)
                         (or (decomposition-map-lookup cp full)
                             (list cp)))))
     (equal (code-point-in-ranges-p cp no-ranges)
            (not (equal decomposition (list cp)))))
   :hooks nil))

(local
 (std::deflist value-ok-listp (x no-ranges full)
   :guard (and (code-point-listp x)
               (range-listp no-ranges)
               (decomposition-mapp full))
   (value-ok x no-ranges full)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nfd-quick-check-yes-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if the @('NFD_Quick_Check') of a code point is `yes',
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the quick check property of Normalization Form D (NFD),
     which is canonical decomposition
     (see @(tsee nfd-quick-check)).
     Its value is `yes' exactly when
     the code point is its own canonical decomposition
     (see @(tsee undecomposable-p)),
     and `no' otherwise."))
  (quick-check-value-case (nfd-quick-check cp ver) :yes)
  :hooks (:fix)

  ///

  (defrulel value-ok-listp-of-all-code-points-for-nfd
    (value-ok-listp (all-code-points)
                    (nfd-quick-check-no-ranges ver)
                    (canonical-decompositions ver))
    :enable (nfd-quick-check-no-ranges
             canonical-decompositions
             (:e all-code-points))
    :disable value-ok-listp-of-cons)

  (defruled nfd-quick-check-yes-p-alt-def
    (equal (nfd-quick-check-yes-p cp ver)
           (undecomposable-p cp nil ver))
    :enable (nfd-quick-check
             undecomposable-p
             decomposition
             value-ok)
    :use (:instance value-ok-when-member-equal-of-value-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (no-ranges (nfd-quick-check-no-ranges ver))
                    (full (canonical-decompositions ver)))))

;;;;;;;;;;;;;;;;;;;;

(std::deflist nfd-quick-check-yes-listp (x ver)
  :guard (and (code-point-listp x)
              (versionp ver))
  :short "Check if the @('NFD_Quick_Check') of every code point of a list
          is `yes', in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the quick check property of Normalization Form D (NFD),
     which is canonical decomposition.
     The list is in NFD exactly when this holds
     and the list is in canonical order
     (see @(tsee canonically-ordered-p)),
     which is what the quick check of [UAX #15, Section 9] tests."))
  (nfd-quick-check-yes-p x ver)

  ///

  (fty::deffixequiv nfd-quick-check-yes-listp
    :args ((x code-point-listp) (ver versionp))
    :hints (("Goal"
             :induct (nfd-quick-check-yes-listp x ver)
             :in-theory (enable nfd-quick-check-yes-listp))))

  (defruled nfd-quick-check-yes-listp-alt-def
    (equal (nfd-quick-check-yes-listp cps ver)
           (undecomposable-listp cps nil ver))
    :induct t
    :enable (nfd-quick-check-yes-listp
             undecomposable-listp
             nfd-quick-check-yes-p-alt-def))

  (defruled nfd-memberp-in-terms-of-quick-check
    (equal (nfd-memberp cps ver)
           (and (nfd-quick-check-yes-listp cps ver)
                (canonically-ordered-p cps ver)))
    :enable (nfd-memberp-alt-def
             nfd-quick-check-yes-listp-alt-def)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nfkd-quick-check-yes-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if the @('NFKD_Quick_Check') of a code point is `yes',
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the quick check property of Normalization Form KD (NFKD),
     which is compatibility decomposition
     (see @(tsee nfkd-quick-check));
     the letter K stands for compatibility.
     Its value is `yes' exactly when
     the code point is its own compatibility decomposition
     (see @(tsee undecomposable-p)),
     and `no' otherwise."))
  (quick-check-value-case (nfkd-quick-check cp ver) :yes)
  :hooks (:fix)

  ///

  (defrulel value-ok-listp-of-all-code-points-for-nfkd
    (value-ok-listp (all-code-points)
                    (nfkd-quick-check-no-ranges ver)
                    (compatibility-decompositions ver))
    :enable (nfkd-quick-check-no-ranges
             compatibility-decompositions
             (:e all-code-points))
    :disable value-ok-listp-of-cons)

  (defruled nfkd-quick-check-yes-p-alt-def
    (equal (nfkd-quick-check-yes-p cp ver)
           (undecomposable-p cp t ver))
    :enable (nfkd-quick-check
             undecomposable-p
             decomposition
             value-ok)
    :use (:instance value-ok-when-member-equal-of-value-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (no-ranges (nfkd-quick-check-no-ranges ver))
                    (full (compatibility-decompositions ver)))))

;;;;;;;;;;;;;;;;;;;;

(std::deflist nfkd-quick-check-yes-listp (x ver)
  :guard (and (code-point-listp x)
              (versionp ver))
  :short "Check if the @('NFKD_Quick_Check') of every code point of a list
          is `yes', in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the quick check property of Normalization Form KD (NFKD),
     which is compatibility decomposition;
     the letter K stands for compatibility.
     The list is in NFKD exactly when this holds
     and the list is in canonical order
     (see @(tsee canonically-ordered-p)),
     which is what the quick check of [UAX #15, Section 9] tests."))
  (nfkd-quick-check-yes-p x ver)

  ///

  (fty::deffixequiv nfkd-quick-check-yes-listp
    :args ((x code-point-listp) (ver versionp))
    :hints (("Goal"
             :induct (nfkd-quick-check-yes-listp x ver)
             :in-theory (enable nfkd-quick-check-yes-listp))))

  (defruled nfkd-quick-check-yes-listp-alt-def
    (equal (nfkd-quick-check-yes-listp cps ver)
           (undecomposable-listp cps t ver))
    :induct t
    :enable (nfkd-quick-check-yes-listp
             undecomposable-listp
             nfkd-quick-check-yes-p-alt-def))

  (defruled nfkd-memberp-in-terms-of-quick-check
    (equal (nfkd-memberp cps ver)
           (and (nfkd-quick-check-yes-listp cps ver)
                (canonically-ordered-p cps ver)))
    :enable (nfkd-memberp-alt-def
             nfkd-quick-check-yes-listp-alt-def)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ quick-check-no
  :parents (quick-check-theorems)
  :short "The code points that the two composed normalization forms change
          are those whose quick check value is `no'."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two composed forms are Normalization Forms C and KC
     (NFC and NFKC: see @(see normalization)).
     Their quick check properties,
     @('NFC_Quick_Check') and @('NFKC_Quick_Check'),
     have three values [UAX #15, Section 9].
     The value `no' is for the code points
     that cannot occur in text of that form.
     The theorems here say that, in every supported version of Unicode,
     these are exactly the code points
     that the form changes when it is applied to them alone:
     the code points that are not their own NFC form,
     or their own NFKC form.")
   (xdoc::p
    "Specifications use both descriptions.
     For example, a profile of identifiers
     that leaves out compatibility characters
     can say that it leaves out the characters that NFKC changes,
     or the characters whose @('NFKC_Quick_Check') is `no'.
     These theorems say that the two are the same set.")
   (xdoc::p
    "A code point whose value is `maybe' is not changed
     when the form is applied to it alone;
     it may be changed when it follows other code points.")
   (xdoc::p
    "The theorems are proved by checking every code point, for each version;
     so adding a version checks them for that version."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;

(define nfc-changes-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if Normalization Form C (NFC) changes a code point,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if the NFC form of the list that consists of the code point
     is not that list."))
  (not (equal (nfc (list cp) ver)
              (list (code-point-fix cp))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(defsection nfc-changes-p-and-quick-check
  :short "Normalization Form C (NFC) changes a code point
          exactly when the @('NFC_Quick_Check') property
          of the code point is `no'."

  (local
   (define nfc-no-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (equal (nfc-changes-p cp ver)
            (quick-check-value-case (nfc-quick-check cp ver) :no))
     :hooks nil))

  (local
   (std::deflist nfc-no-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (nfc-no-ok x ver)))

  (defrulel nfc-no-ok-listp-of-all-code-points
    (nfc-no-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable nfc-no-ok-listp-of-cons)

  (defruled nfc-changes-p-in-terms-of-quick-check
    (equal (nfc-changes-p cp ver)
           (quick-check-value-case (nfc-quick-check cp ver) :no))
    :enable nfc-no-ok
    :use (:instance nfc-no-ok-when-member-equal-of-nfc-no-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver)))))

;;;;;;;;;;;;;;;;;;;;

(define nfkc-changes-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if Normalization Form KC (NFKC) changes a code point,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if the NFKC form of the list that consists of the code point
     is not that list."))
  (not (equal (nfkc (list cp) ver)
              (list (code-point-fix cp))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(defsection nfkc-changes-p-and-quick-check
  :short "Normalization Form KC (NFKC) changes a code point
          exactly when the @('NFKC_Quick_Check') property
          of the code point is `no'."

  (local
   (define nfkc-no-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (equal (nfkc-changes-p cp ver)
            (quick-check-value-case (nfkc-quick-check cp ver) :no))
     :hooks nil))

  (local
   (std::deflist nfkc-no-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (nfkc-no-ok x ver)))

  (defrulel nfkc-no-ok-listp-of-all-code-points
    (nfkc-no-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable nfkc-no-ok-listp-of-cons)

  (defruled nfkc-changes-p-in-terms-of-quick-check
    (equal (nfkc-changes-p cp ver)
           (quick-check-value-case (nfkc-quick-check cp ver) :no))
    :enable nfkc-no-ok
    :use (:instance nfkc-no-ok-when-member-equal-of-nfkc-no-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver)))))
