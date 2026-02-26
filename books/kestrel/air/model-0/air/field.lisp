; AIR Library
; Model 0: Field Arithmetic
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR-M0")

(include-book "../portcullis")

(include-book "kestrel/arithmetic-light/mod" :dir :system)
(include-book "kestrel/crypto/primes/koala-bear" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "std/util/defmacro-plus" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ field
  :parents (model-0)
  :short "Koala Bear field arithmetic for Model 0 AIR."
  :long
  (xdoc::topstring
   (xdoc::p
    "Model 0 uses the Koala Bear prime field for AIR constraints,
     matching Ziren's Plonky3-based implementation.")
   (xdoc::p
    "The prime is @('p = 2^31 - 2^24 + 1 = 2,130,706,433').")
   (xdoc::p
    "Since @('256 < p'), all 8-bit byte values embed uniquely into the field
     as themselves (no reduction needed).")
   (xdoc::p
    "This file provides macro abbreviations for the @(see pfield::prime-fields)
     library, specialized to the Koala Bear prime.
     This follows the pattern established by the Semaphore and Aleo projects."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Field Prime (from certified Pratt certificate)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ prime ()
  :short "The Koala Bear prime: 2^31 - 2^24 + 1 = 2130706433."
  '(primes::koala-bear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Field Element Recognizer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ field-elem-p (x)
  :short "Recognize a valid Koala Bear field element."
  :long
  (xdoc::topstring
   (xdoc::p
    "Abbreviation for @('(pfield::fep x (primes::koala-bear))')."))
  `(pfield::fep ,x (primes::koala-bear)))

;; Note: pfield::fep already has fep-fw-to-natp as a forward-chaining rule,
;; which provides similar functionality to a compound-recognizer.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Field Arithmetic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ field-add (a b)
  :short "Field addition: @('(a + b) mod p')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Abbreviation for @('(pfield::add a b (primes::koala-bear))')."))
  `(pfield::add ,a ,b (primes::koala-bear)))

(defmacro+ field-sub (a b)
  :short "Field subtraction: @('(a - b) mod p')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Abbreviation for @('(pfield::sub a b (primes::koala-bear))')."))
  `(pfield::sub ,a ,b (primes::koala-bear)))

(defmacro+ field-mul (a b)
  :short "Field multiplication: @('(a * b) mod p')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Abbreviation for @('(pfield::mul a b (primes::koala-bear))')."))
  `(pfield::mul ,a ,b (primes::koala-bear)))

(defmacro+ field-neg (a)
  :short "Field negation: @('-a mod p')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Abbreviation for @('(pfield::neg a (primes::koala-bear))')."))
  `(pfield::neg ,a (primes::koala-bear)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Embedding bytes into the field
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ nat-to-field (n)
  :short "Embed a natural number into the field."
  :long
  (xdoc::topstring
   (xdoc::p
    "Computes @('n mod p')."))
  `(mod ,n (primes::koala-bear)))

;; Since 256 < p, bytes embed as themselves
(defthm byte-embeds-uniquely
  (implies (and (natp x) (< x 256))
           (equal (nat-to-field x) x)))

;; Bytes are field elements
(defthm byte-is-field-elem
  (implies (and (natp x) (< x 256))
           (field-elem-p x))
  :hints (("Goal" :in-theory (enable pfield::fep))))
