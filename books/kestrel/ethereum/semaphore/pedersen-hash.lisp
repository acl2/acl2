; Ethereum Semaphore Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "base-points-for-pedersen-hash")

(include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pedersen-hash
  :parents (semaphore-specification)
  :short "The Pedersen hash for the Ethereum Semaphore."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is specified in Section 5.3.2 of "
    (xdoc::ahref
     "https://github.com/appliedzkp/semaphore/blob/master/spec/Semaphore%20Spec.pdf"
     "https://github.com/appliedzkp/semaphore/blob/master/spec/Semaphore%20Spec.pdf")
    " and also, in more detail, in "
    (xdoc::ahref
     "https://iden3-docs.readthedocs.io/en/latest/_downloads/4b929e0f96aef77b75bb5cfc0f832151/Pedersen-Hash.pdf"
     "https://iden3-docs.readthedocs.io/en/latest/_downloads/4b929e0f96aef77b75bb5cfc0f832151/Pedersen-Hash.pdf")
    ". In the documentation of our formalization of Pedersen hash,
     we use `[ES]' (for `Ethereum Specification`) to refer to the first
     and `[IS]' (for `Iden3 Specification`) to refer to the second.
     There appear to be a few discrepancies between the two,
     although there should not be any;
     we will update our specification and documentation
     as these discrepancies are discussed and resolved.")
   (xdoc::p
    "Note that the Pedersen hash formalized here differs from "
    (xdoc::seetopic "zcash::pedersen-hash" "the one in Zcash")
    "; in particular, this one uses 4-bit windows,
     while the one in Zcash uses 3-bit windows.
     Yet, the two share obvious characteristics.
     In the future, we may formalize a generic form of Pedersen hash,
     obtaining the Ethereum Semaphore one and the Zcash one
     by suitably instantiating and specializing the generic one."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen-pad ((m bit-listp))
  :returns (m1 bit-listp :hyp (bit-listp m))
  :short "Pedersen hash padding."
  :long
  (xdoc::topstring
   (xdoc::p
    "[IS] says that if the input message is not a multiple of 4 bits,
     it is padded with 1, 2, or 3 bits to turn it into a multiple of 4 bits.
     [ES] does not say anything about it,
     but it talks about 4-bit windows,
     thus perhaps leaving the padding implicit.
     [IS] says that the zero bits are appended,
     which suggests that they are added at the end."))
  (case (mod (len m) 4)
    (0 m)
    (1 (append m (list 0 0 0)))
    (2 (append m (list 0 0)))
    (3 (append m (list 0)))
    (otherwise (acl2::impossible)))

  :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))

  ///

  (defruledl lemma1
    (implies (and (integerp i)
                  (equal (mod i 4) 0))
             (equal (* 4 (ceiling i 4))
                    i)))

  (defruledl lemma2
    (implies (and (integerp i)
                  (equal (mod i 4) 1))
             (equal (* 4 (ceiling i 4))
                    (+ i 3))))

  (defruledl lemma3
    (implies (and (integerp i)
                  (equal (mod i 4) 2))
             (equal (* 4 (ceiling i 4))
                    (+ i 2))))

  (defruledl lemma4
    (implies (and (integerp i)
                  (equal (mod i 4) 3))
             (equal (* 4 (ceiling i 4))
                    (+ i 1))))

  (defret len-of-pedersen-pad
    (equal (len m1)
           (* 4 (ceiling (len m) 4)))
    :hints (("Goal" :use ((:instance lemma1 (i (len m)))
                          (:instance lemma2 (i (len m)))
                          (:instance lemma3 (i (len m)))
                          (:instance lemma4 (i (len m)))))))

  (defret multiple-of-4-len-of-pedersen-hash
    (integerp (/ (len m1) 4))
    :hints (("Goal" :use len-of-pedersen-pad))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen-enc ((4bits bit-listp))
  :guard (= (len 4bits) 4)
  :returns (i integerp :hyp (bit-listp 4bits))
  :short "Encode a window of 4 bits."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the function @($\\mathit{enc}$) in [IS],
     while in [ES] it is part of the double summation.")
   (xdoc::p
    "There is a discrepancy between [ES] and [IS]
     in the treatment of the fourth bit:
     [ES] maps 0 to 1 and 1 to -1,
     while [IS] maps 0 to -1 and 1 to 1.
     The Circom code in the Semaphore repository
     is consistent with [ES],
     so we follow [ES] here.")
   (xdoc::p
    "There is also a discrepancy between [ES] and [IS]
     in the treatment of the other three bits:
     [IS] adds 1 to their weighted sum,
     while [ES] does not.
     The Circom code in the Semaphore repository
     is consistent with [IS],
     and we have confirmed with the authors of Semaphore
     that the sum must include the 1 addend
     and that [IS] should be fixed, which we have done in Overleaf."))
  (b* ((b0 (first 4bits))
       (b1 (second 4bits))
       (b2 (third 4bits))
       (b3 (fourth 4bits)))
    (* (if (= b3 0) 1 -1)
       (+ 1 b0 (* 2 b1) (* 4 b2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen-scalar ((segment bit-listp))
  :guard (integerp (/ (len segment) 4))
  :returns (i integerp :hyp (bit-listp segment))
  :short "The function that maps each message segment to a scalar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the function that maps @($M_i$) to @($\\langle M_i \\rangle$)
     in [IS],
     while in [IS] it is part of the double summation.
     Each @($M_i$) is a segment,
     and the result is used in the scalar multiplication
     of a BabyJubjub curve point:
     this motivates the name of this ACL2 function.")
   (xdoc::p
    "This is a weighted sum of the encodings of the 4-bit windows
     (see @(tsee pedersen-enc)).
     The sum in [IS] appears to be off by one:
     it should end at @($k_i$), not at @($k_i-1$),
     otherwise it would ignore the last 4-bit window.
     The sum in [ES] is correct, because @($W$) is 50,
     but it neglects to accommodate the fact that
     the last segment may consist of less than 200 bits
     (i.e. less than 50 4-bit windows).
     Nonetheless, both issues are easily resolved and fixable:
     it is clear what our specification should say here."))
  (pedersen-scalar-loop 0 segment)

  :prepwork
  ((define pedersen-scalar-loop ((w natp) (segment bit-listp))
     :guard (integerp (/ (len segment) 4))
     :returns (i integerp :hyp (and (natp w) (bit-listp segment)))
     :parents nil
     (if (consp segment)
         (+ (* (pedersen-enc (take 4 segment))
               (expt 2 (* 5 w)))
            (pedersen-scalar-loop (1+ w) (nthcdr 4 segment)))
       0)
     :measure (len segment)
     :prepwork ((local (include-book "std/lists/nthcdr" :dir :system))
                (local (include-book "arithmetic-3/top" :dir :system)))
     :verify-guards nil ; done below
     ///
     (defrulel verify-guards-lemma
       (implies (and (integerp (/ (len x) 4))
                     (consp x))
                (>= (len x) 4))
       :cases ((equal (len x) 1)
               (equal (len x) 2)
               (equal (len x) 3))
       :rule-classes :linear
       :prep-books ((include-book "std/lists/len" :dir :system)))
     (verify-guards pedersen-scalar-loop))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen-generator ((i natp))
  :returns (point baby-jubjub-pointp
                  :hints (("Goal"
                           :cases ((member i '(0 1 2 3 4 5 6 7 8 9)))
                           :in-theory (enable ecurve::twisted-edwards-zero))))
  :short "Generator points for Pedersen hash."
  :long
  (xdoc::topstring
   (xdoc::p
    "The scalars returned by @(tsee pedersen-scalar)
     are used to multiply a sequence of BabyJubjub points,
     and the resulting points are added up together.
     This is described by equation (1) in [IS],
     and by the double summation in [ES].
     The points are denoted @($P_0,\\ldots,P_l$) in [IS] and @($g_s$) in [ES].
     These points are fixed for Semaphore, so they can be precomputed.")
   (xdoc::p
    "We have precomputed the points in @(see pedersen-hash-base-points).
     The constant @('*pedersen-base-points-for-semaphore*') lists them.
     Even though Pedersen hash should allow any number of points in general,
     for Semaphore we only need ten points (the ones in the list constant).
     The outer summation in [ES] goes from 0 to @($S-1$), and @($S\leq10$).")
   (xdoc::p
    "We define this function to return one of the ten points
     when the index is below 10,
     or the zero point otherwise.
     The index will always be below 10, when used in the Semaphore."))
  (b* ((i (nfix i)))
    (if (< i 10)
        (nth i *pedersen-base-points-for-semaphore*)
      (ecurve::twisted-edwards-zero))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen-addend ((segment bit-listp) (i natp))
  :guard (integerp (/ (len segment) 4))
  :returns (point baby-jubjub-pointp)
  :short "Addend point in the sum that yields the Pedersen hash."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the result of the scalar multiplication between
     the integer returned by @(tsee pedersen-scalar)
     and the generator point returned by @(tsee pedersen-generator)."))
  (baby-jubjub-mul (pedersen-scalar segment)
                   (pedersen-generator i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen ((m bit-listp))
  :returns (hash baby-jubjub-pointp)
  :short "Point resulting from the Pedersen hash."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pad the message if needed,
     and then we go through each segment
     and add the addend points together."))
  (b* ((m1 (pedersen-pad m)))
    (pedersen-loop 0 m1))

  :prepwork
  ((define pedersen-loop ((i natp) (m bit-listp))
     :guard (integerp (/ (len m) 4))
     :returns (point baby-jubjub-pointp)
     :parents nil
     (b* (((when (<= (len m) 200)) (pedersen-addend m i))
          (point1 (pedersen-addend (take 200 m) i))
          (point2 (pedersen-loop (1+ i) (nthcdr 200 m))))
       (baby-jubjub-add point1 point2))
     :measure (len m)
     :prepwork ((local (include-book "std/lists/nthcdr" :dir :system)))
     :verify-guards :after-returns)
   (local (include-book "arithmetic/top" :dir :system))))
