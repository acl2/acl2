; Primes Library: Koala Bear Prime
;
; Copyright (C) 2025 Eric McCarthy (bendyarm on GitHub)
;
; License: See the LICENSE file distributed with this library.
;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This prime number is defined by the formula 2^31 - 2^24 + 1 = 2130706433.
;; The Pratt certificate in this file is used to prove primality of this number.
;;
;; References for the KoalaBear field prime:
;; - Ziren (ZKM) zkVM arithmetization uses KoalaBear as the trace field for AIR
;;   constraints.
;;   https://docs.zkm.io/design/arithmetization.html
;; - Ziren's prover pipeline evaluates all arithmetic in the KoalaBear field
;;   before recursively compressing proofs.
;;   https://docs.zkm.io/design/prover-architecture/prover-architecture.html
;; - Kayson Wang, "Efficient Prime Fields for Zero-knowledge proof" (HackMD):
;;   documents Plonky3's implementation of KoalaBear alongside other STARK-
;;   friendly primes.
;;   https://hackmd.io/@Voidkai/BkNX3xUZA

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "kestrel/number-theory/defprime" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprime koala-bear

  #x7f000001

  ;; The following certificate was generated using SageMath
  ;; The koala-bear prime is 2^31 - 2^24 + 1 = 2130706433
  ;; This is a 31-bit prime number.
  ;;
  ;; Complete factorization tree:
  ;; p-1 = 2^24 * 127
  (3 (2 127)
     (24 1)
     (() ()))

  :parents (crypto::crypto)

  :short "The koala-bear prime."

  :long
  (xdoc::topstring
   (xdoc::p
    "The koala-bear prime is defined by the formula "
    (xdoc::code "2^31 - 2^24 + 1 = 2130706433")
    ", also known as the KoalaBear field prime.")
   (xdoc::p
    "Ziren's zkVM (ZVM/Ziren) expresses AIR traces over this field so that "
    "every register column becomes a polynomial on a KoalaBear evaluation "
    "domain.")
   (xdoc::p
    "Ziren's proof system runs its Machine Prover in KoalaBear before "
    "recursively translating the resulting STARK proofs into BN254 for "
    "Groth16 aggregation.")
   (xdoc::p
    "Outside of Ziren, the KoalaBear prime is implemented inside Plonky3 as "
    "one of the ~32-bit, FRI-friendly fields for zero-knowledge systems.")
   (xdoc::p
    "See also "
    (xdoc::ahref
     "https://docs.zkm.io/design/arithmetization.html"
     "Ziren arithmetization")
    ", "
    (xdoc::ahref
     "https://docs.zkm.io/design/prover-architecture/prover-architecture.html"
     "Ziren prover architecture")
    ", and "
    (xdoc::ahref
     "https://hackmd.io/@Voidkai/BkNX3xUZA"
     "\"Efficient Prime Fields for Zero-knowledge proof\".") )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This prime has length 31 bits.

(assert-event (equal (integer-length (koala-bear)) 31))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Decimal version of this prime.

(assert-event
 (equal (koala-bear)
        2130706433))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Verify this equals 2^31 - 2^24 + 1

(assert-event
 (equal (koala-bear)
        (+ (- (expt 2 31) (expt 2 24)) 1)))

