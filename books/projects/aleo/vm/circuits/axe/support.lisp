; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "support-blake2s") ; reduce?
(include-book "kestrel/utilities/make-var-names" :dir :system)
(include-book "kestrel/axe/r1cs/lift-r1cs" :dir :system)
(include-book "kestrel/axe/r1cs/axe-rules-r1cs" :dir :system)
(include-book "kestrel/axe/r1cs/axe-prover-r1cs" :dir :system)
(include-book "kestrel/crypto/r1cs/gadgets/boolean-alt-rules" :dir :system)
(include-book "kestrel/crypto/r1cs/gadgets/xor-rules" :dir :system)
;(include-book "kestrel/axe/dag-info" :dir :system)
(include-book "kestrel/axe/make-conjunction-dag" :dir :system)
(include-book "kestrel/bv-lists/bits-to-bytes-little" :dir :system)
(include-book "kestrel/bv-lists/bits-to-bytes2" :dir :system)
(include-book "kestrel/bv-lists/bits-to-bytes-little2" :dir :system)
(include-book "kestrel/bv/rules7" :dir :system)
(include-book "kestrel/bv/rules9" :dir :system)
(include-book "projects/bls12-377-curves/primes/bls12-377-prime" :dir :system)
(include-book "kestrel/lists-light/cons" :dir :system)
(include-book "kestrel/prime-fields/fe-listp-fast" :dir :system)
(include-book "kestrel/crypto/r1cs/tools/vars" :dir :system) ; for r1cs-constraint-vars
(include-book "kestrel/crypto/sha-3/sha-3" :dir :system) ; SHA-3 spec, so we can define the openers below

;; (1-w)*w=0
(defthm bitp-idiom
  (implies (and (fep x p)
                (primep p))
           (equal (equal 0 (mul (add (neg x p) 1 p) x p))
                  (bitp x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p)
           :cases ((equal x 0) (equal x 1)))))

;; 2xy = x+y-z
(defthm bitxor-idiom-1
  (implies (and (bitp a)
                (bitp b)
                (fep c p)
                (primep p)
                (not (equal 2 p)))
           (equal (equal (mul 2 (mul a b p) p) (add b (add a (neg c p) p) p))
                  (equal c (acl2::bitxor a b))))
  :hints (("Goal" :use (:instance pfield::bitxor-constraint-intro
                                  (pfield::a a)
                                  (pfield::b b)
                                  (pfield::c c)
                                  (pfield::p p)
                                  )
           :in-theory (disable pfield::bitxor-constraint-intro))))

(defthm bitxor-idiom-2
  (implies (and (bitp a)
                (bitp b)
                (pfield::fep c p)
                (primep p)
                (not (equal 2 p)))
           (equal (equal (mul 2 (mul a b p) p) (add a (add b (neg c p) p) p))
                  (equal c (acl2::bitxor a b))))
  :hints (("Goal" :use (:instance pfield::bitxor-constraint-intro
                                  (pfield::a a)
                                  (pfield::b b)
                                  (pfield::c c)
                                  (pfield::p p)
                                  )
           :in-theory (disable pfield::bitxor-constraint-intro))))

;; Warning: This can mess up other patterns, like bitxor patterns
(defthm bitand-idiom-1
  (implies (and (bitp a)
                (bitp b)
                (primep p))
           (equal (mul a b p)
                  (bitand a b)))
  :hints (("Goal" :in-theory (disable acl2::bitp-becomes-unsigned-byte-p))))

;; this one replaces (mul a b) with (bitand a b)
(defthm bitxor-idiom-1-alt
  (implies (and (bitp a)
                (bitp b)
                (fep c p)
                (primep p)
                (not (equal 2 p)))
           (equal (equal (mul 2 (bitand a b) p) (add b (add a (neg c p) p) p))
                  (equal c (acl2::bitxor a b))))
  :hints (("Goal" :use (:instance pfield::bitxor-constraint-intro
                                  (pfield::a a)
                                  (pfield::b b)
                                  (pfield::c c)
                                  (pfield::p p)
                                  )
           :in-theory (disable pfield::bitxor-constraint-intro))))

;; this one replaces (mul a b) with (bitand a b)
(defthm bitxor-idiom-2-alt
  (implies (and (bitp a)
                (bitp b)
                (fep c p)
                (primep p)
                (not (equal 2 p)))
           (equal (equal (mul 2 (bitand a b) p) (add a (add b (neg c p) p) p))
                  (equal c (acl2::bitxor a b))))
  :hints (("Goal" :use (:instance bitxor-idiom-1-alt)
           :in-theory (disable pfield::bitxor-constraint-intro
                               add-of-mul-of-2-becomes-bvcat
                               add-of-mul-of-power-of-2
                               bitxor-idiom-1-alt
                               acl2::bitp-becomes-unsigned-byte-p))))

(defthm bitnot-idiom-1
  (implies (and (bitp a)
                (primep p))
           (equal (add 1 (neg a p) p)
                  (bitnot a)))
  :hints (("Goal" :in-theory (disable acl2::bitp-becomes-unsigned-byte-p))))

(defthm bitnot-idiom-2
  (implies (and (bitp a)
                (primep p))
           (equal (add (neg a p) 1 p)
                  (bitnot a)))
  :hints (("Goal" :in-theory (disable acl2::bitp-becomes-unsigned-byte-p))))

;; needed to relieve hyps when doing only top-level rewriting of constraints
(defthm bitp-of-add-of-neg-and-1
  (implies (and (bitp a)
                (primep p))
           (bitp (add (neg a p) 1 p))))

;; needed to relieve hyps when doing only top-level rewriting of constraints
(defthm bitp-of-add-of-1-and-neg
  (implies (and (bitp a)
                (primep p))
           (bitp (add 1 (neg a p) p))))

(defthm bitp-of-mul
  (implies (and (bitp a)
                (bitp b))
           (bitp (mul a b p)))
  :hints (("Goal" :in-theory (e/d (bitp) (acl2::bitp-becomes-unsigned-byte-p)))))

(acl2::defopeners acl2::group)
(acl2::defopeners acl2::firstn)

(acl2::defopeners sha3::map-bit-string-to-plane)
(acl2::defopeners sha3::theta-d-lanes)
(acl2::defopeners sha3::theta-planes)
(acl2::defopeners sha3::theta-lanes)
(acl2::defopeners sha3::theta-lane)

(acl2::defopeners sha3::chi-planes)
(acl2::defopeners sha3::chi-lanes)
(acl2::defopeners sha3::chi-lane)

(acl2::defopeners sha3::theta-c-lanes)
(acl2::defopeners sha3::theta-c-lane)

(acl2::defopeners sha3::rho-aux-aux)
(acl2::defopeners sha3::rho-aux)

(acl2::defopeners sha3::pi-planes)
(acl2::defopeners sha3::pi-lanes)

(acl2::defopeners sha3::iota-aux2)

(acl2::defopeners update-nth)

(defconst *global-proof-rules*
  '(;;acl2::booleanp-of-booland
    ;; bitp rules:
    ;; acl2::bitp-of-bvchop-of-1 ; drop?
    ;;misc rules:
    primes::primep-of-bls12-377-scalar-field-prime-constant ;use more?
    pfield::add-associative-when-constant ; at least move constants forward, so they can be combined
    pfield::add-of-add-combine-constants
    pfield::equal-of-add-combine-constants
    pfield::add-commutative-when-constant
    pfield::add-commutative-2-when-constant
    pfield::mod-of-ifix-when-fep ; which rules introduce this?
    acl2::bvchop-of-bvcat-same
    acl2::bvcat-of-bvchop-low
    acl2::bvcat-of-bvchop-high
    ))
