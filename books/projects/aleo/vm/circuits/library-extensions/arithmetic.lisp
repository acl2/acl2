; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "std/util/defrule" :dir :system)

(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If p is a positive integer,
; then it is >= 2^(n-1), where n is the bit length of p.
; By definition of bit length (i.e. integer length),
; if the bit length is n, then p = 2^(n-1) + ...,
; and thus p >= 2^(n-1).

(defruled positive->=-expt2-of-integer-length-minus-1
  (implies (posp p)
           (>= p (expt 2 (1- (integer-length p)))))
  :rule-classes ((:linear :trigger-terms ((integer-length p))))
  :induct t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Exponentiation in base 2 is monotonic w.r.t. exponents.

(defruled expt2-mono
  (implies (and (natp a)
                (natp b)
                (<= a b))
           (<= (expt 2 a)
               (expt 2 b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If two addends are bounded by a power of 2,
; the addition is bounded by that power plus one in the exponent.

(defruled plus-expt2-upper-bound
  (implies (and (integerp n)
                (< a (expt 2 n))
                (< b (expt 2 n)))
           (< (+ a b) (expt 2 (1+ n))))
  :prep-books
  ((acl2::scatter-exponents)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Similar to the above, but for a subtraction offset by 2^n.

(defruled diff-offset-expt2-upper-bound
  (implies (and (integerp n)
                (>= b 0)
                (< a (expt 2 n))
                (< b (expt 2 n)))
           (< (+ (- a b)
                 (expt 2 n))
              (expt 2 (1+ n))))
  :prep-books
  ((acl2::scatter-exponents)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If two factors are bounded by powers of 2,
; the product is bounded by the power of 2 with the sum of the exponents.

(defruled times-expt2-upper-bound
  (implies (and (natp a)
                (natp b)
                (natp n)
                (natp m)
                (< a (expt 2 n))
                (< b (expt 2 m)))
           (< (* a b)
              (* (expt 2 (+ n m)))))
  :do-not-induct t
  :use (:instance lemma0 (k (expt 2 n)) (h (expt 2 m)))
  :prep-lemmas
  ((defruled lemma0
     (implies (and (natp a)
                   (natp b)
                   (natp k)
                   (natp h)
                   (< a k)
                   (< b h))
              (< (* a b) (* k h)))
     :prep-books ((set-default-hints '((acl2::nonlinearp-default-hint
                                        acl2::stable-under-simplificationp
                                        acl2::hist
                                        acl2::pspv)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The characterization of Euclidian division on natural numbers implies that
; the quotient is the result of both floor and truncate
; and the remainder is the result of both mod and rem.

(defruled floor-when-euclidian
  (implies (and (natp x)
                (natp y)
                (natp q)
                (natp r)
                (equal x (+ (* y q) r))
                (< r y))
           (equal (floor x y) q)))

(defruled truncate-when-euclidian
  (implies (and (natp x)
                (natp y)
                (natp q)
                (natp r)
                (equal x (+ (* y q) r))
                (< r y))
           (equal (truncate x y) q)))

(defruled mod-when-euclidian
  (implies (and (natp x)
                (natp y)
                (natp q)
                (natp r)
                (equal x (+ (* y q) r))
                (< r y))
           (equal (mod x y) r)))

(defruled rem-when-euclidian
  (implies (and (natp x)
                (natp y)
                (natp q)
                (natp r)
                (equal x (+ (* y q) r))
                (< r y))
           (equal (rem x y) r)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Monotonicity of integer-length.

(defruled integer-length-mono
  (implies (and (natp a)
                (natp b)
                (<= a b))
           (<= (integer-length a)
               (integer-length b)))
  :prep-books
  ((include-book "kestrel/arithmetic-light/integer-length" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Bit size of one less than a power of two.

(defruled integer-length-of-expt2-minus-1
  (implies (natp n)
           (equal (integer-length (1- (expt 2 n))) n))
  :prep-books
  ((include-book "kestrel/arithmetic-light/integer-length" :dir :system)))
