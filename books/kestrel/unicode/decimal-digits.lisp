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
(include-book "maps")

(include-book "data/v16.0.0/unicode-data")
(include-book "data/v17.0.0/unicode-data")
(include-book "data/v18.0.0/unicode-data")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ decimal-digits
  :parents (unicode)
  :short "The decimal digits and their values."
  :long
  (xdoc::topstring
   (xdoc::p
    "A decimal digit is a character
     whose @('Numeric_Type') property is @('Decimal'):
     a digit of a system that writes numbers
     in base ten with digits for zero to nine,
     such as the ASCII digits and the Arabic-Indic digits
     [UAX #44, Table 9].
     Its @('Numeric_Value') is a number from 0 to 9.
     Unicode has some seventy-seven such systems of digits.")
   (xdoc::p
    "The digits of a system are ten consecutive code points,
     in the order of their values;
     this is a rule of the standard [Unicode, Section 4.6],
     and here it is a theorem about the supported versions.
     So a digit determines the zero of its system,
     and two digits belong to the same system
     exactly when they have the same zero:
     see @(tsee decimal-digit-zero).")
   (xdoc::p
    "We take the values from field 6 of the file @('UnicodeData.txt')
     of the Unicode Character Database, for each supported version.
     The other numeric characters,
     such as superscript digits, fractions and Roman numerals,
     are not decimal digits in this sense and are not here."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decimal-digit-values ((ver versionp))
  :returns (map decimal-digit-mapp)
  :short "The map from the decimal digits to their values,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *decimal-digit-v16.0.0*
                :v17.0.0 *decimal-digit-v17.0.0*
                :v18.0.0 *decimal-digit-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decimal-digit-value ((cp code-point-p) (ver versionp))
  :returns (value? digit-value-option-p)
  :short "The value of a code point as a decimal digit,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is a number from 0 to 9 if the code point is a decimal digit,
     and @('nil') if it is not."))
  (decimal-digit-map-lookup cp (decimal-digit-values ver))
  :hooks (:fix)

  ///

  (defrule natp-or-null-of-decimal-digit-value
    (or (natp (decimal-digit-value cp ver))
        (equal (decimal-digit-value cp ver) nil))
    :rule-classes :type-prescription
    :disable (decimal-digit-value
              digit-value-option-p-of-decimal-digit-value)
    :enable digit-value-option-p
    :use digit-value-option-p-of-decimal-digit-value)

  (defrule decimal-digit-value-upper-bound
    (implies (decimal-digit-value cp ver)
             (<= (decimal-digit-value cp ver) 9))
    :rule-classes :linear
    :disable (decimal-digit-value
              digit-value-option-p-of-decimal-digit-value)
    :enable (digit-value-option-p
             digit-value-p)
    :use digit-value-option-p-of-decimal-digit-value))

;;;;;;;;;;;;;;;;;;;;

(define decimal-digit-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is a decimal digit,
          in a version of Unicode."
  (and (decimal-digit-value cp ver) t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define decimal-digit-zero ((cp code-point-p) (ver versionp))
  :returns (zero integerp :rule-classes (:rewrite :type-prescription))
  :short "The code point of the digit zero
          of the system of a decimal digit,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the code point of the digit, less its value.
     For example, for U+0667 ARABIC-INDIC DIGIT SEVEN
     it is U+0660 ARABIC-INDIC DIGIT ZERO.
     Two decimal digits are of the same system of digits
     exactly when this function gives the same result for both.")
   (xdoc::p
    "For a code point that is not a decimal digit,
     the result is the code point itself."))
  (- (code-point-fix cp)
     (or (decimal-digit-value cp ver) 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection decimal-digit-theorems
  :short "The decimal digits of a system are ten consecutive code points
          with the values 0 to 9."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is: for a decimal digit,
     its zero (see @(tsee decimal-digit-zero)) is a code point,
     and for each number from 0 to 9,
     the code point that many places after the zero
     is a decimal digit with that number as its value.
     We prove this by checking it on every code point, for each version;
     so adding a version checks it for that version.")
   (xdoc::p
    "It follows that two code points of the same system
     that are decimal digits have different values
     unless they are the same code point,
     and that the ASCII digits have the values 0 to 9."))

  (local (in-theory (enable fix)))

  (local
   (define digit-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (b* ((value (decimal-digit-value cp ver))
          ((unless value) t)
          (zero (- (code-point-fix cp) value)))
       (and (<= 0 zero)
            (<= (+ zero 9) #x10FFFF)
            (equal (decimal-digit-value zero ver) 0)
            (equal (decimal-digit-value (+ zero 1) ver) 1)
            (equal (decimal-digit-value (+ zero 2) ver) 2)
            (equal (decimal-digit-value (+ zero 3) ver) 3)
            (equal (decimal-digit-value (+ zero 4) ver) 4)
            (equal (decimal-digit-value (+ zero 5) ver) 5)
            (equal (decimal-digit-value (+ zero 6) ver) 6)
            (equal (decimal-digit-value (+ zero 7) ver) 7)
            (equal (decimal-digit-value (+ zero 8) ver) 8)
            (equal (decimal-digit-value (+ zero 9) ver) 9)))
     :guard-hints (("Goal" :in-theory (enable code-point-p)))
     :hooks nil))

  (local
   (std::deflist digit-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (digit-ok x ver)))

  (defrulel digit-ok-listp-of-all-code-points
    (digit-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable digit-ok-listp-of-cons)

  (defrulel digit-ok-holds
    (digit-ok cp ver)
    :rule-classes nil
    :use (:instance digit-ok-when-member-equal-of-digit-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver)))
    :enable digit-ok)

  (defrule code-point-p-of-decimal-digit-zero
    (code-point-p (decimal-digit-zero cp ver))
    :enable (decimal-digit-zero
             digit-ok
             code-point-p)
    :use digit-ok-holds)

  (defrule decimal-digit-value-of-decimal-digit-zero-plus
    (implies (and (decimal-digit-p cp ver)
                  (natp i)
                  (<= i 9))
             (equal (decimal-digit-value (+ i (decimal-digit-zero cp ver))
                                         ver)
                    i))
    :enable (decimal-digit-p
             decimal-digit-zero
             digit-ok)
    :cases ((equal i 0)
            (equal i 1)
            (equal i 2)
            (equal i 3)
            (equal i 4)
            (equal i 5)
            (equal i 6)
            (equal i 7)
            (equal i 8)
            (equal i 9))
    :use digit-ok-holds)

  (defrule decimal-digit-value-of-decimal-digit-zero
    (implies (decimal-digit-p cp ver)
             (equal (decimal-digit-value (decimal-digit-zero cp ver) ver)
                    0))
    :disable decimal-digit-value-of-decimal-digit-zero-plus
    :use (:instance decimal-digit-value-of-decimal-digit-zero-plus (i 0)))

  ;; The ASCII digits.

  (defrulel decimal-digit-value-of-ascii-zero
    (equal (decimal-digit-value #x30 ver) 0)
    :enable (decimal-digit-value decimal-digit-values))

  (defruled decimal-digit-value-when-ascii-digit
    (implies (and (code-point-p cp)
                  (<= #x30 cp)
                  (<= cp #x39))
             (equal (decimal-digit-value cp ver)
                    (- cp #x30)))
    :disable decimal-digit-value-of-decimal-digit-zero-plus
    :enable (decimal-digit-p
             decimal-digit-zero
             natp)
    :use (:instance decimal-digit-value-of-decimal-digit-zero-plus
                    (cp #x30)
                    (i (- cp #x30)))))
