; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "decimal-digits")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ mixed-number-detection
  :parents (unicode)
  :short "Whether a string has decimal digits
          of more than one system of digits."
  :long
  (xdoc::topstring
   (xdoc::p
    "Digits of different systems can look alike:
     U+09EA BENGALI DIGIT FOUR looks like U+0038 DIGIT EIGHT.
     Unicode Security Mechanisms [UTS #39, Section 5.3]
     gives a process to detect a string that mixes systems of digits:
     for each character of the string that has a decimal number value,
     take the character that is the zero of its system;
     if that gives more than one zero,
     the string has digits of several decimal number systems.")
   (xdoc::p
    "The zero of the system of a decimal digit
     is the code point of the digit, less its value:
     see @(tsee decimal-digit-zero).
     The process ignores every character that is not a decimal digit;
     the specification states it for strings
     that have no other numeric characters,
     such as Roman numerals."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decimal-digit-zeros ((cps code-point-listp) (ver versionp))
  :returns (zeros code-point-listp)
  :short "The zeros of the systems of the decimal digits
          of a list of code points,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is a list without duplicates, which stands for a set:
     one code point for each system of digits
     that has a digit in the list."))
  (b* (((when (endp cps)) nil)
       (zeros (decimal-digit-zeros (cdr cps) ver))
       ((unless (decimal-digit-p (car cps) ver)) zeros)
       (zero (decimal-digit-zero (car cps) ver)))
    (if (member-equal zero zeros)
        zeros
      (cons zero zeros)))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defrule no-duplicatesp-equal-of-decimal-digit-zeros
    (no-duplicatesp-equal (decimal-digit-zeros cps ver))
    :induct t))

;;;;;;;;;;;;;;;;;;;;

(define mixed-number-systems-p ((cps code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a list of code points has decimal digits
          of more than one system of digits,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the process of [UTS #39, Section 5.3]:
     see @(see mixed-number-detection)."))
  (consp (cdr (decimal-digit-zeros cps ver)))
  :hooks (:fix))
