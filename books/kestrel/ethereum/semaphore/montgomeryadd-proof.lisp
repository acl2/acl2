; Ethereum Semaphore Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "kestrel/ethereum/semaphore/prime-field-abbreviations" :dir :system)
(include-book "kestrel/ethereum/semaphore/json-to-r1cs/load-circom-json" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

; (depends-on "json/montgomeryadd.json")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains a proof of the MontgomeryAdd() ciruit component
; (see the Circom code of Semaphore).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Load the circuit.

(acl2::load-circom-json "json/montgomeryadd.json" '(baby-jubjub-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The circuit adds two points in Montgomery coordinates:
;
;   a = ...  -- constant
;   d = ...  -- constant
;   A = (2 * (a + d)) / (a - d)  -- constant
;   B = 4 / (a - d)  -- constant
;
;   (x1, y1), (x2, y2)  -- inputs
;   (x3, y3)  -- outputs
;
;             y2 - y1
;    lamda = ---------
;             x2 - x1
;
;    x3 = B * lamda^2 - A - x1 - x2
;
;    y3 = lamda * (x1 - x3) - y1
;
; The point (x3, y3) is the sum of the points (x1, y1) and (x2, y2).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The circuit implicitly assumes that
; all the input and output variables are field elements,
; and that x1 and x2 (whose difference is used as denominator) are different.
; We capture all of these assumptions in the precondition predicate.

(define precond (x1 y1 x2 y2 x3 y3)
  :returns (yes/no booleanp)
  (and (pfep x1)
       (pfep y1)
       (pfep x2)
       (pfep y2)
       (pfep x3)
       (pfep y3)
       (not (equal x1 x2))))

; The specification is the one sketched above,
; where all the operations are in the prime field.
; We formalize the specification as follows,
; but we should eventually use
; the elliptic curve library and the definition of BabyJubjub here.

(defconst *a* 168700)
(defconst *d* 168696)
(defconst *biga* (pfdiv (pfmul 2 (pfadd *a* *d*)) (pfsub *a* *d*)))
(defconst *bigb* (pfdiv 4 (pfsub *a* *d*)))

(define montgomery-add ((x1 pfep) (y1 pfep) (x2 pfep) (y2 pfep))
  :guard (not (equal x1 x2))
  :returns (mv (x3 pfep) (y3 pfep))
  (b* ((lambda (pfdiv (pfsub y2 y1)
                      (pfsub x2 x1)))
       (x3 (pfaddall (pfmulall *bigb* lambda lambda)
                     (pfneg *biga*)
                     (pfneg x1)
                     (pfneg x2)))
       (y3 (pfsub (pfmul lambda (pfsub x1 x3))
                  y1)))
    (mv x3 y3))
  :guard-hints (("Goal" :in-theory (enable (:e baby-jubjub-prime)))))

(define spec (x1 y1 x2 y2 x3 y3)
  :guard (precond x1 y1 x2 y2 x3 y3)
  (b* (((mv x3$ y3$) (montgomery-add x1 y1 x2 y2)))
    (and (equal x3 x3$)
         (equal y3 y3$)))
  :guard-hints (("Goal" :in-theory (enable precond))))

; The circuit predicate is mechanically obtained as usual
; (e.g. see explanation in the MultiMux1 and MultiMux3 proofs).
; Note that 'lambda' is misspelled as 'lamda' in the Circom code;
; that is why the variable below is :|main.lamda| and not :|main.lambda|.

(define auxp (lambda)
  :returns (yes/no booleanp)
  (pfep lambda))

(define circuit-core (x1 y1 x2 y2 x3 y3 lambda)
  :guard (and (precond x1 y1 x2 y2 x3 y3)
              (auxp lambda))
  :returns (yes/no booleanp)
  (r1cs::r1cs-holdsp (acl2::montgomeryadd-make-r1cs)
                     (list (cons :|main.in1[0]| x1)
                           (cons :|main.in1[1]| y1)
                           (cons :|main.in2[0]| x2)
                           (cons :|main.in2[1]| y2)
                           (cons :|main.out[0]| x3)
                           (cons :|main.out[1]| y3)
                           (cons :|main.lamda| lambda)))
  :guard-debug t
  :guard-hints (("Goal" :in-theory (e/d (precond auxp r1cs::r1cs-valuationp)
                                        ((:e baby-jubjub-prime))))))

(define-sk circuit (x1 y1 x2 y2 x3 y3)
  :guard (precond x1 y1 x2 y2 x3 y3)
  :returns (yes/no booleanp)
  (exists (lambda)
          (and (auxp lambda)
               (circuit-core x1 y1 x2 y2 x3 y3 lambda))))

; If we try proving directly that the circuit implements the specification,
; i.e. that CIRCUIT-CORE implies SPEC,
; different choices of rules all seem to take us far from the proof goal.
; The proof is actually very simple, if we look at the Circom code:
; Given the constraint
;
;    lambda * (x2 - x1) = y2 -y1
;
; it suffices to divide both sides for (x2 - x1) to obtain
;
;             y2 - y1
;    lamda = ---------
;             x2 - x1
;
; which is one step (recall that the precondition ensures x1 /= x2).
; Instead, when attempting the proof that CIRCUIT-CORE implies SPEC,
; things get spread around, for different kinds of rules.
; The normalization rules seem to work against us here.
; Perhaps we could attempt to disable certain rules
; to prevent things from being spread around,
; or perhaps we could add rules to somehow regroup things
; (having care of avoiding loops),
; but this all seems fragile and time-consuming.
; So here we go for a more direct, and in a way more robust, proof.

; First, to avoid the complexities introduced by the Circom-to-R1CS compilation,
; which also seems to unduly move things around,
; we define a predicate that captures the Circom constraints more directly.
; This predicate should be correct for the proofs to go through,
; but it not part of the "trusted computing base":
; it does not appear in the final theorem.

(define circom (x1 y1 x2 y2 x3 y3 lambda)
  :guard (and (precond x1 y1 x2 y2 x3 y3)
              (auxp lambda))
  :returns (yes/no booleanp)
  (and (equal (pfmul lambda
                     (pfsub x2 x1))
              (pfsub y2 y1))
       (equal x3 (pfaddall (pfmulall *bigb* lambda lambda)
                           (pfneg *biga*)
                           (pfneg x1)
                           (pfneg x2)))
       (equal y3 (pfsub (pfmul lambda (pfsub x1 x3))
                        y1)))
  :guard-hints (("Goal" :in-theory (enable precond
                                           auxp
                                           (:e baby-jubjub-prime)))))

; The equivalence of the Circom predicate with the R1CS predicate
; is sufficiently simple that the normalization rules take care of it.
; After all, the compilation process is just making transformations
; that more or less line up with the normalization rules,
; so it is not surprising that this works.
; Note that we need the bind-free rules; the others do not work here.

(defruled circuit-core-is-circom
  (implies (and (precond x1 y1 x2 y2 x3 y3)
                (auxp lambda))
           (equal (circuit-core x1 y1 x2 y2 x3 y3 lambda)
                  (circom x1 y1 x2 y2 x3 y3 lambda)))
  :enable (precond
           auxp
           circuit-core
           r1cs::r1cs-holdsp
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           circom
           (:e baby-jubjub-prime))
  :disable pfield::move-negation-1
  :prep-books ((include-book "kestrel/prime-fields/bind-free-rules" :dir :system)))

; Now we turn to the core of the proof that the circuit implements the spec.
; We prove that CIRCOM implies SPEC, which, as noted above,
; amounts to dividing both sides of an equality.
; We do not really have an explicit way to tell ACL2 to do that:
; we take a prime field rule and instantiate accordingly.

(defruled circom-implies-spec
  (implies (and (precond x1 y1 x2 y2 x3 y3)
                (auxp lambda)
                (circom x1 y1 x2 y2 x3 y3 lambda))
           (spec x1 y1 x2 y2 x3 y3))
  :enable (precond
           auxp
           circom
           spec
           montgomery-add)
  :use (:instance pfield::equal-of-mul-cancel
        (y lambda)
        (z (pfsub x2 x1))
        (x (pfsub y2 y1))
        (p (baby-jubjub-prime))))

; Given the equivalence of CIRCOM and CIRCUIT-CORE,
; it is trivial to prove that CIRCUIT-CORE implies SPEC.

(defruled circuit-core-implies-spec
  (implies (and (precond x1 y1 x2 y2 x3 y3)
                (auxp lambda)
                (circuit-core x1 y1 x2 y2 x3 y3 lambda))
           (spec x1 y1 x2 y2 x3 y3))
  :enable (circuit-core-is-circom
           circom-implies-spec))

; Showing that CIRCUIT implies SPEC is then mechanical.

(defruled circuit-implies-spec
  (implies (and (precond x1 y1 x2 y2 x3 y3)
                (circuit x1 y1 x2 y2 x3 y3))
           (spec x1 y1 x2 y2 x3 y3))
  :enable circuit
  :use (:instance circuit-core-implies-spec
        (lambda (circuit-witness x1 y1 x2 y2 x3 y3))))

; To prove that the circuit has solutions given the spec,
; we need to find a witness for lambda.
; This is easy, looking at the Circom code.

(defun lambda-witness (x1 y1 x2 y2)
  (pfdiv (pfsub y2 y1)
         (pfsub x2 x1)))

; Again, we prove that SPEC implies CIRCOM,
; we avoid the issues discussed above,
; namely that the rules seem to take formulas into a bad direction.
; The proof here is as easy as the other one,
; namely multiplying (instead of dividing) both sides of the equality.
; We use exactly the same hints as the other theorem.

(defruled spec-implies-circom
  (implies (and (precond x1 y1 x2 y2 x3 y3)
                (spec x1 y1 x2 y2 x3 y3))
           (b* ((lambda (lambda-witness x1 y1 x2 y2)))
             (circom x1 y1 x2 y2 x3 y3 lambda)))
  :enable (precond
           auxp
           circom
           spec
           montgomery-add
           (:e baby-jubjub-prime))
  :disable pfield::move-negation-1
  :use (:instance PFIELD::EQUAL-OF-MUL-CANCEL
        (y (lambda-witness x1 y1 x2 y2))
        (z (pfsub x2 x1))
        (x (pfsub y2 y1))
        (p (baby-jubjub-prime))))

; The witness satisfies AUXP under the precondition.
; This is needed in subsequent proofs.

(defruled auxp-when-precond
  (implies (precond x1 y1 x2 y2 x3 y3)
           (b* ((lambda (lambda-witness x1 y1 x2 y2)))
             (auxp lambda)))
  :enable (precond auxp))

; Given the equivalence between CIRCOM and CIRCUIT-CORE,
; it is wasy to prove that SPEC implies CIRCUIT-CORE.

(defruled spec-implies-circuit-core
  (implies (and (precond x1 y1 x2 y2 x3 y3)
                (spec x1 y1 x2 y2 x3 y3))
           (b* ((lambda (lambda-witness x1 y1 x2 y2)))
             (circuit-core x1 y1 x2 y2 x3 y3 lambda)))
  :use ((:instance circuit-core-is-circom (lambda (lambda-witness x1 y1 x2 y2)))
        spec-implies-circom
        auxp-when-precond)
  :disable lambda-witness)

; Proving that SPEC implies CIRCUIT is then mechanical.

(defruled spec-implies-circuit
  (implies (and (precond x1 y1 x2 y2 x3 y3)
                (spec x1 y1 x2 y2 x3 y3))
           (circuit x1 y1 x2 y2 x3 y3))
  :enable (spec-implies-circuit-core
           auxp-when-precond)
  :disable (lambda-witness)
  :use (:instance circuit-suff (lambda (lambda-witness x1 y1 x2 y2))))

; Putting together the 'if' and 'only if' proofs,
; we get the equivalence proof.
; Note that it does not involve the CIRCOM predicate,
; which was just an intermediate device.

(defruled circuit-is-spec
  (implies (precond x1 y1 x2 y2 x3 y3)
           (equal (circuit x1 y1 x2 y2 x3 y3)
                  (spec x1 y1 x2 y2 x3 y3)))
  :use (circuit-implies-spec spec-implies-circuit))
