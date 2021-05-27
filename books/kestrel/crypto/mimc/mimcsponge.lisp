; MiMC Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

(in-package "MIMC")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Included Books

(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)

(include-book "round-constants-for-semaphore")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Specification of the MiMC variant used by Semaphore.

;; Primary reference:
;; MiMC: Efficient Encryption and Cryptographic Hashing with
;;       Minimal Multiplicative Complexity
;; Martin Albrecht et al.
;; Published in:
;;   Advances in Cryptology – ASIACRYPT 2016: 22nd International
;;   Conference on the Theory and Application of Cryptology and
;;   Information Security, Hanoi, Vietnam, December 4-8, 2016,
;;   Proceedings, Part 1, Springer LNCS 10031, pp. 191–219.
;; Also available at:
;;   https://eprint.iacr.org/2016/492
;; Usually referred to as "MiMC spec" or [Alb+16].
;;
;; This file defines an instantiation of the MiMC spec as
;; described in the "semaphore spec", available here:
;;   https://docs.zkproof.org/pages/standards/accepted-workshop3/proposal-semaphore.pdf
;;
;; Here are the MiMC spec alternatives chosen and some clarifications,
;; interpretations, and assumptions made.
;;
;; * Field prime:
;;   Note that the field prime is a parameter to the functions in this file.
;;   However, Semaphore uses the BN-254 curve order.
;;   See Semaphore spec, section 4.2.
;;   Question: is the fact that 3 divides (p - 1) a problem?
;;   Discussion:
;;     In [Alb+16], section 5.3 states:
;;         it needs to be assured that the cubing in the round function
;;         creates a permutation. For this, it is sufficient to require
;;         gcd(3, p − 1) = 1.
;;     It so happens that 3 divides (p - 1), when p is the BN-254 curve order,
;;     so gcd(3, p - 1) = 3.
;;     However, we are using an exponent of 5 (see below).
;;     Since gcd(5, p - 1) = 1, and since this ensures that x^5 mod p
;;     is a permutation, this is not a problem.
;;   See also additional note on the round function exponent below.
;;
;; * Permutation:
;;   MiMC-2p/p (Feistel).
;;   The MiMC-2n/n (Feistel) permutation is described in [Alb+16] sections 2.1
;;   and 2.2, and the MiMC-2p/p variant in section 5.1.
;;   The difference is that MiMC-2n/n does arithmetic in a field of size 2^n
;;   and MiMC-2p/p does arithmetic in a field of size p, a large prime.
;;   Most analysis of MiMC-2n/n carries over to MiMC-2p/p.
;;
;; * Round Function:
;;   Exponent of 5, and k=0.
;;   The round function is described in [Alb+16] section 2.1 and the
;;   variant round function using an exponent of 5 is described in section 5.3.
;;
;;   A "round function" is a function that is repeatedly applied for some
;;   number of rounds.  We can think of the "round function" as being a
;;   sequence of functions for i from 0 to n-1:
;;     F_i(x) = (x + c_i)^5   (as in [Alb+16] 2.1, but with an exponent of 5)
;;   or we can think of the "round function" as a function of two arguments:
;;     F(x,i) = (x + c[i])^5
;;   Note that since we are using a permutation rather than the block cipher,
;;   k=0, and we omit k from the round function.
;;
;;   Question: does the exponent 5 lose any security?
;;     [Alb+16] section 5.3, p.19 states:
;;         ... from the security point of view and from the implementation one,
;;         there is no advantage to choose exponents of the form 2t + 1 greater
;;         than 3.
;;     The MiMC spec is not explicit whether this analysis applies to MiMC-2p/p.
;;     We recommend that this part of the Semaphore spec be clarified.
;;
;;   Additional note on whether an exponent of 5 results in the round function
;;     being a permutation.
;;     In [Alb+16] section 5.3 p.18, for the MiMC-2n/n case,
;;     they write:
;;         Remember that for MiMC-n/n, d has to satisfy the condition
;;         gcd(d, 2n − 1) = 1 in order to be a permutation, while in
;;         the case of MiMC-2n/n (that is, for Feistel Networks) this
;;         condition is not necessary.
;;     The MiMC spec is not explicit whether the relaxation for Feistel
;;     Networks carries over to MiMC-2p/p.  If it does,
;;     then this would be another reason not to worry about
;;     whether (x^5 mod p) is a permutation.

;; * Number of Rounds:
;;   220.
;;   This is calculated by 2 * ceiling(log_5(p)).
;;   Typo in the MiMC spec:
;;     In section 5.1, they state that p/p should have number of rounds
;;       r = ceiling( log p) / log_2 3 ).
;;     They left out the base-2 part of the log in the numerator, confusing the
;;     issue, and they did not use the same notation as the previous page, which
;;     would have given the simpler equivalent formula:
;;       r = ceiling(log_3(p))
;;   In the "mimc spec" section 5.3 Different Round Functions,
;;   they do not explicitly update the formula for computing the number of
;;   rounds needed, but it is clear that the 3 is derived from the exponent so
;;   the computation for an exponent of 5 is
;;     r = ceiling(log_5(p))
;;
;;  This computation is also mentioned at the top of
;;    https://github.com/kobigurk/circomlib/blob/master/circuits/mimcsponge.circom
;;  in a comment:
;;    // log_5(21888242871839275222246405745257275088548364400416034343698204186575808495617) ~= 110
;;    // => nRounds should be 220
;;
;; * Other "MiMC spec" issues.
;;   * [Alb+16] section 6.1, there is a subsection titled "MiMC in the SNARK
;;     setting."  However, there is an error, as described in
;;     https://github.com/zcash/zcash/issues/2233#issuecomment-291840857
;;     Daira Hopwood wrote:
;;         Note that there appears to be an error in the MiMC paper concerning
;;         the number of constraints needed; the paper claims in section 6.1
;;         (page 22) that only one R1CS constraint is needed to implement each
;;         round of the permutation (which is reflected in the prototype
;;         implementation). However this fails to constrain the intermediate
;;         value Y in equation (5) on page 22, which is necessary for security.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Unhygienic macro to make modular addition more readable.

;; This works as long as the local var containing the field order
;; has the name 'field-order.
(defmacro f+ (a b)
  `(pfield::add ,a ,b field-order))

;; Utility to describe return type.

(defun fe-pairp (elems prime)
  (declare (xargs :guard (rtl::primep prime)))
  (and (= (len elems) 2)
       (pfield::fe-listp elems prime)))

;; and rules to pick it apart

(defthm fep-of-car-of-fe-pairp
  (implies (fe-pairp x field-order)
           (pfield::fep (car x) field-order)))

(defthm fep-of-cadr-of-fe-pairp
  (implies (fe-pairp x field-order)
           (pfield::fep (cadr x) field-order)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2.1 The block cipher

;; We are currently interested mainly in
;; MiMC-2p/p
;; Feistel mode over prime field,
;; using an exponent of 5,
;; and using field addition in place of XORs.
;; The "mimc spec" does not describe this combination together,
;; it defines each variation in a separate section, and
;; we have to combine them as best we can.

;; For the relevant sections for describing the block cipher:
;; 2.1 The block cipher
;;   -- defines MiMC-n/n and MiMC-2n/n, where the field is 2^n
;; 5.1 MiMC over prime fields
;;   -- briefly defines MiMC-p/p and MiMC-2p/p
;; 5.3 Different Round Functions
;;   -- very briefly mentions MiMC-p/p but does not mention MiMC-2p/p.
;;      Also, it is not precise about which parts of the analysis
;;      of GF(2^n) apply to GF(p).
;; 6.1 Verifiable Computation and SNARK
;;   -- here, they redefine the CIRCLED PLUS character to be field addition:
;;      "The addition in the field, which is the same as bitwise XOR,
;;      is a comparatively less expensive operation."
;;      and later they show the round function (MiMC-p/p with exponent=3) in R1CS:
;;        X + k_i + C_i + U = 0
;;        U * U = Y
;;        Y * U = Z
;;      which also implies the XORs have turned into field additions.
;;      In "semaphore spec", they state:  "[circle plus] operations
;;      have been replaced with field additions.".


;; Field order is prime.
;; (Note, other than the field order check,
;; this definition is the same as mimc-n/n.)
;; x (plaintext input), key, and elements of round-constants are
;; all field elements.

(defun mimc-p/p-block-cipher
  (x key field-order exponent nrounds round-constants)
  (declare (xargs :guard (and (posp field-order) (< 2 field-order)
                              (rtl::primep field-order)
                              (pfield::fep x field-order)
                              (pfield::fep key field-order)
                              (natp exponent) (< 2 exponent)
                              (natp nrounds)
                              (pfield::fe-listp round-constants field-order)
                              (= (len round-constants) nrounds)
                              )))
  (if (atom round-constants) ; it will be nil
      (f+ x key)
    (mimc-p/p-block-cipher
     (let ((x+k+c_i (f+ (f+ x key)
                        (car round-constants))))
       (pfield::pow x+k+c_i exponent field-order))
     key field-order exponent
     (- nrounds 1)
     (cdr round-constants))))

(defthm return-type-of--mimc-p/p-block-cipher
  (implies ;; same as guard of mimc-p/p-block-cipher
           (and (posp field-order) (< 2 field-order)
                (pfield::fep x field-order)
                (pfield::fep key field-order)
                (natp exponent) (< 2 exponent)
                (natp nrounds)
                (pfield::fe-listp round-constants field-order)
                (= (len round-constants) nrounds)
                )
           (pfield::fep (mimc-p/p-block-cipher
                         x key field-order exponent nrounds round-constants)
                        field-order)))


;; Feistel-mode.
;; Field order is prime.
;; (Note, other than the field order check,
;; this definition is the same as mimc-2n/n.)

;; "mimc spec" is not as precise for this mode.
;; The issues:
;; * mimc-spec:
;;     "In the last round, the swap operation is not applied."
;;   There is no swap operation defined in the spec.
;;   A standard Feistel network does not swap the right and left
;;   blocks after the last round function.
;;   Some such diagrams show no swap
;;   (e.g. https://en.wikipedia.org/wiki/Feistel_cipher );
;;   others show two swaps that cancel each other (e.g.,
;;   https://www.tutorialspoint.com/cryptography/feistel_block_cipher.htm )
;;   The sentence in the spec could mean either (1) they
;;   are confirming the standard Feistel network operation, or
;;   (2) only 1 of the 2 swaps is done.
;;   For now I'm guessing it means (1, standard Feistel).
;; * Does not indicate whether k is added at the end.
;;   For comparison, in MiMC-n/n, they write:
;;     "The ciphertext is finally produced by adding the key k
;;     again to the output of the last round."
;;   For MiMC-2n/n and -2p/p, does this happen?  If so, how is it
;;   added?  Just to the right half?
;;   However, if k=0 as in the permutation, it doesn't matter.

;; NOTE after inspecting
;; https://github.com/kobigurk/circomlib/blob/master/circuits/mimcsponge.circom
;; * "the swap operation is not applied" is interpreted as we conjectured.
;; * they do not add k at the end.
;;   This difference will not matter for the permutation case since k=0,
;;   but it is something to be aware of.
;;   We take out adding k at the end, with a comment.
;;   (Besides, it was never precisely defined whether to add k to xL or xR.)

;;
(defun mimc-2p/p-block-cipher-body
    (xL xR k field-order exponent nrounds round-constants)
  (declare (xargs :guard (and (posp field-order) (< 2 field-order)
                              (rtl::primep field-order)
                              (pfield::fep xL field-order)
                              (pfield::fep xR field-order)
                              (pfield::fep k field-order)
                              (natp exponent) (< 2 exponent)
                              (natp nrounds)
                              (pfield::fe-listp round-constants field-order)
                              (= (len round-constants) nrounds)
                              )))
  (if (zp nrounds) ; nil
      (list xR xL) ; undo the last reverse.  This means the top-level call
          ; of this function must have nrounds >= 1.
    (mimc-2p/p-block-cipher-body
     (f+ xR (pfield::pow (f+ (f+ xL k)
                             (car round-constants))
                         exponent
                         field-order))
     xL
     k field-order exponent (- nrounds 1) (cdr round-constants))))

(defthm return-type-of--mimc-2p/p-block-cipher-body
  (implies (and ;; same as guard of mimc-p/p-block-cipher
                (posp field-order) (< 2 field-order)
                (rtl::primep field-order)
                (pfield::fep xL field-order)
                (pfield::fep xR field-order)
                (pfield::fep k field-order)
                (natp exponent) (< 2 exponent)
                (natp nrounds)
                (pfield::fe-listp round-constants field-order)
                (= (len round-constants) nrounds)
                )
           (fe-pairp (mimc-2p/p-block-cipher-body xL xR k field-order exponent nrounds round-constants)
                     field-order)
           ))

(defun mimc-2p/p-block-cipher
    (xL xR k field-order exponent nrounds round-constants)
  (declare (xargs :guard (and (posp field-order) (< 2 field-order)
                              (rtl::primep field-order)
                              (pfield::fep xL field-order)
                              (pfield::fep xR field-order)
                              (pfield::fep k field-order)
                              (natp exponent) (< 2 exponent)
                              (posp nrounds)
                              (pfield::fe-listp round-constants field-order)
                              (= (len round-constants) nrounds)
                              )))
    (if (zp nrounds)
        (list xL xR)
      (mimc-2p/p-block-cipher-body xL xR k field-order exponent nrounds round-constants)))

(defthm return-type-of--mimc-2p/p-block-cipher
  (implies (and ;; same as guard of mimc-p/p-block-cipher
            (posp field-order) (< 2 field-order)
            (rtl::primep field-order)
            (pfield::fep xL field-order)
            (pfield::fep xR field-order)
            (pfield::fep k field-order)
            (natp exponent) (< 2 exponent)
            (posp nrounds)
            (pfield::fe-listp round-constants field-order)
            ;; thing to explore: why is the double-rewrite decl needed?
            (= (len (double-rewrite round-constants)) nrounds)
            )
           (fe-pairp (mimc-2p/p-block-cipher xL xR k field-order exponent nrounds round-constants)
                     field-order)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2.2 The permutation

(defun mimc-p/p-permutation (x field-order exponent nrounds round-constants)
  (declare (xargs :guard (and (posp field-order) (< 2 field-order)
                              (rtl::primep field-order)
                              (pfield::fep x field-order)
                              (natp exponent) (< 2 exponent)
                              (natp nrounds)
                              (pfield::fe-listp round-constants field-order)
                              (= (len round-constants) nrounds)
                              )))
  (mimc-p/p-block-cipher x 0 field-order exponent nrounds round-constants))

(defthm return-type-of--mimc-p/p-permutation
  (implies (and (posp field-order) (< 2 field-order)
                              (rtl::primep field-order)
                              (pfield::fep x field-order)
                              (natp exponent) (< 2 exponent)
                              (natp nrounds)
                              (pfield::fe-listp round-constants field-order)
                              (= (len (double-rewrite round-constants)) nrounds)
                              )
           (pfield::fep (mimc-p/p-permutation x field-order exponent nrounds round-constants)
                        field-order)))

(defun mimc-2p/p-permutation (xL xR field-order exponent nrounds round-constants)
  (declare (xargs :guard (and (posp field-order) (< 2 field-order)
                              (rtl::primep field-order)
                              (pfield::fep xL field-order)
                              (pfield::fep xR field-order)
                              (natp exponent) (< 2 exponent)
                              (posp nrounds)
                              (pfield::fe-listp round-constants field-order)
                              (= (len round-constants) nrounds)
                              )))
  (mimc-2p/p-block-cipher xL xR 0 field-order exponent nrounds round-constants))

(defthm return-type-of--mimc-2p/p-permutation
  (implies (and (posp field-order) (< 2 field-order)
                              (rtl::primep field-order)
                              (pfield::fep xL field-order)
                              (pfield::fep xR field-order)
                              (natp exponent) (< 2 exponent)
                              (posp nrounds)
                              (pfield::fe-listp round-constants field-order)
                              (= (len (double-rewrite round-constants)) nrounds)
                              )
           (fe-pairp (mimc-2p/p-permutation xL xR field-order exponent nrounds round-constants)
                     field-order)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2.3 The hash function

;; The hash functions mentioned here are left for future work:
;;   MiMCHash
;;   MiMCHash-l
;;   MiMCHash-t
;;   MiMCHash-256
;;   MiMCHash-256b
;;   MiMCHash-tb


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; "semaphore spec" section:
;; 5.3.1 MiMC sponge
;;  "We then define MiMCSponge(m, n)
;;   as a sponge construction with capacity = 1, rate = 1
;;   m is the amount of input field elements and
;;   n is the amount of output field elements."
;;
;; Notes.  Leave in to document discovery process.
;; * there is no discussion of pads
;; * capacity = 1 and rate = 1 doesn't make sense in bits.
;;   Probably it means number of field elements.
;; * There is no discussion of the order in which
;;   the inputs enter the sponge, or the outputs are squeezed.
;;   We assume it is from left to right.
;; * There is no discussion of whether the output of
;;   MiMC-2p/p should be assigned to (c,r) or (r,c).
;;   We originally assumed it is (c,r), which turned out to be backwards, see below.

;; After noting those spec imprecisions, we must look at
;; the circuit.  Hopefully that will pin down the spec.
;; https://github.com/kobigurk/circomlib/blob/master/circuits/mimcsponge.circom
;; * no pad seen
;; * capacity and rate as assumed: 1 field element each
;; * (x_L, x_R) order:  circuit doc string states "S = R||C".
;;   That is not quite correct, what it really means is
;;   x_L||x_R = R||C.  So I got the mapping backwards initially.
;;   Now changed it to match circuit.

;;------------------------------
;; Fully parameterized MiMCsponge absorb, squeeze, and top level.

;;----------------
;; absorb

(defun MiMCsponge-absorb (r c inputs field-order constants exponent nrounds)
  ;; we would like to verify guards but we first need to prove the return type
  ;; of mimc-2p/p-permutation
  (declare (xargs :guard (and (posp field-order) (< 2 field-order)
                              (rtl::primep field-order)
                              (pfield::fep r field-order)
                              (pfield::fep c field-order)
                              (pfield::fe-listp inputs field-order)
                              (pfield::fe-listp constants field-order)
                              (natp exponent) (< 2 exponent)
                              (posp nrounds)
                              (= (len constants) nrounds))))
  (if (atom inputs) ; will be nil
      (list r c)
    (let ((new-r (f+ r (car inputs))))
      (let ((new-r-c (mimc-2p/p-permutation
                      new-r c
                      field-order exponent nrounds constants)))
        (MiMCsponge-absorb
         (first new-r-c) (second new-r-c)
         (cdr inputs)
         field-order
         constants exponent nrounds)))))

(defthm return-type-of--mimcsponge-absorb
  (implies (and (posp field-order) (< 2 field-order)
                (rtl::primep field-order)
                (pfield::fep r field-order)
                (pfield::fep c field-order)
                (pfield::fe-listp inputs field-order)
                (pfield::fe-listp constants field-order)
                (natp exponent) (< 2 exponent)
                (posp nrounds)
                (= (len (double-rewrite constants)) nrounds))
           (fe-pairp (MiMCsponge-absorb r c inputs field-order constants exponent nrounds) field-order)))

;;----------------
;; squeeze

(defun MiMCsponge-squeeze (r c n field-order constants exponent nrounds)
  (declare (xargs :guard (and (posp field-order) (< 2 field-order)
                              (rtl::primep field-order)
                              (pfield::fep r field-order)
                              (pfield::fep c field-order)
                              (posp n)
                              (pfield::fe-listp constants field-order)
                              (natp exponent) (< 2 exponent)
                              (posp nrounds)
                              (= (len constants) nrounds))))

  (if (zp n) ; should never be called with n=0; this is for the measure
      nil
    (if (= n 1) ; separate base case so we don't calculate the permutation
                ; simply to throw it away with a recursive call returning nil.
        (list r)
      (cons r
            (let ((new-r-c (mimc-2p/p-permutation
                            r c
                            field-order exponent nrounds constants)))
              (MiMCsponge-squeeze
               (first new-r-c) (second new-r-c)
               (- n 1)
               field-order constants exponent nrounds))))))

(defthm return-type-of--mimcsponge-squeeze
  (implies (and (posp field-order) (< 2 field-order)
                (rtl::primep field-order)
                (pfield::fep r field-order)
                (pfield::fep c field-order)
                (posp n)
                (pfield::fe-listp constants field-order)
                (natp exponent) (< 2 exponent)
                (posp nrounds)
                (= (len (double-rewrite constants)) nrounds))
           (pfield::fe-listp (MiMCsponge-squeeze r c n field-order constants exponent nrounds)
                             field-order)))

(defthm number-of-outputs-of--mimcsponge-squeeze
  (implies (and (posp field-order) (< 2 field-order)
                (rtl::primep field-order)
                (pfield::fep r field-order)
                (pfield::fep c field-order)
                (posp n)
                (pfield::fe-listp constants field-order)
                (natp exponent) (< 2 exponent)
                (posp nrounds)
                (= (len (double-rewrite constants)) nrounds))
           (equal (len (MiMCsponge-squeeze r c n field-order constants exponent nrounds))
                  n)))

;;----------------
;; MiMCsponge, with parameters

(defun MiMCsponge (m n inputs field-order constants exponent nrounds)
  (declare (xargs :guard (and (posp field-order) (< 2 field-order)
                              (rtl::primep field-order)
                              (natp m)
                              (posp n)
                              (pfield::fe-listp inputs field-order)
                              (= (len inputs) m)
                              (pfield::fe-listp constants field-order)
                              (natp exponent) (< 2 exponent)
                              (posp nrounds)
                              (= (len constants) nrounds))))
  (if (not (= m (len inputs)))
    nil
    (let ((r-c (MiMCsponge-absorb 0 0 inputs field-order constants exponent nrounds)))
      (MiMCsponge-squeeze (first r-c) (second r-c) n field-order constants exponent nrounds))))

(defthm return-type-of--mimcsponge
  (implies (and (posp field-order) (< 2 field-order)
                (rtl::primep field-order)
                (natp m)
                (posp n)
                (pfield::fe-listp inputs field-order)
                (= (len (double-rewrite inputs)) m)
                (pfield::fe-listp constants field-order)
                (natp exponent) (< 2 exponent)
                (posp nrounds)
                (= (len (double-rewrite constants)) nrounds))
           (pfield::fe-listp (MiMCsponge m n inputs field-order constants exponent nrounds)
                             field-order)))

(defthm number-of-outputs-of--mimcsponge
  (implies (and (posp field-order) (< 2 field-order)
                (rtl::primep field-order)
                (natp m)
                (posp n)
                (pfield::fe-listp inputs field-order)
                (= (len (double-rewrite inputs)) m)
                (pfield::fe-listp constants field-order)
                (natp exponent) (< 2 exponent)
                (posp nrounds)
                (= (len (double-rewrite constants)) nrounds))
           (equal (len (MiMCsponge m n inputs field-order constants exponent nrounds))
                  n)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Specialize MiMCsponge to
;;  * field-order (= (primes::bn-254-group-prime) = (zksemaphore::baby-jubjub-prime))
;;  * constants (= (mimc-feistel-220-constants))
;;  * exponent (= 5), and
;;  * number of rounds (220).

(defun MiMCsponge-semaphore (m n inputs)
  (declare (xargs :guard (and (natp m)
                              (posp n)
                              (pfield::fe-listp inputs (zksemaphore::baby-jubjub-prime))
                              (= (len inputs) m))))
  (declare (xargs :guard-hints (("Goal" :in-theory (enable (:e ZKSEMAPHORE::BABY-JUBJUB-PRIME))))))
  (MiMCsponge m n inputs
              (zksemaphore::baby-jubjub-prime)
              (mimc-feistel-220-constants)
              5 ; exponent
              220 ; nrounds
              ))

(defthm return-type-of--mimcsponge-semaphore
  (implies (and (natp m)
                (posp n)
                (pfield::fe-listp inputs (zksemaphore::baby-jubjub-prime))
                (= (len (double-rewrite inputs)) m))
           (pfield::fe-listp (MiMCsponge-semaphore m n inputs)
                             (zksemaphore::baby-jubjub-prime)))
  :hints (("Goal" :in-theory (enable (:e ZKSEMAPHORE::BABY-JUBJUB-PRIME)))))

(defthm number-of-outputs-of--mimcsponge-semaphore
  (implies (and (natp m)
                (posp n)
                (pfield::fe-listp inputs (zksemaphore::baby-jubjub-prime))
                (= (len (double-rewrite inputs)) m))
           (equal (len (MiMCsponge-semaphore m n inputs))
                  n))
  :hints (("Goal" :in-theory (enable (:e ZKSEMAPHORE::BABY-JUBJUB-PRIME)))))
