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
(local (include-book "kestrel/alists-light/lookup-equal" :dir :system))

; (depends-on "json/montgomerydouble.json")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains a proof of the MontgomeryDouble() ciruit component
; (see the Circom code of Semaphore).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Load the circuit.

(acl2::load-circom-json "json/montgomerydouble.json" '(baby-jubjub-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The circuit doubles a point in Montgomery coordinates:
;
;   a = ...  -- constant
;   d = ...  -- constant
;   A = (2 * (a + d)) / (a - d)  -- constant
;   B = 4 / (a - d)  -- constant
;
;   (x, y)  -- inputs
;   (xd, yd)  -- outputs
;
;            3 * x * x + 2 * A * x + 1
;   lamda = ------------------------
;                  2 * B * y
;
;   xd = B * lamda * lambda - A - 2 * x
;
;   yd = lamda * (x - xd) - y
;
; The point (xd, yd) is the double of the point (x, y).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The circuit implicitly assumes that
; all the input and output variables are field elements,
; and that y (used as denominator) is not 0.
; We capture all of these assumptions in the precondition predicate.

(define precond (x y xd yd)
  :returns (yes/no booleanp)
  (and (pfep x)
       (pfep y)
       (pfep xd)
       (pfep yd)
       (not (equal y 0))))

; The specification is the one sketched above,
; where all the operations are field operations.
; We formalize the specification as follows,
; but we should eventually use
; the elliptic curve library and the definition of BabyJubjub here.

(defconst *a* 168700)
(defconst *d* 168696)
(defconst *biga* (pfdiv (pfmul 2 (pfadd *a* *d*)) (pfsub *a* *d*)))
(defconst *bigb* (pfdiv 4 (pfsub *a* *d*)))

(define montgomery-double ((x pfep) (y pfep))
  :guard (not (equal y 0))
  :returns (mv (xd pfep) (yd pfep))
  (b* ((lambda (pfdiv (pfaddall (pfmulall 3 x x)
                                (pfmulall 2 *biga* x)
                                1)
                      (pfmulall 2 *bigb* y)))
       (xd (pfaddall (pfmulall *bigb* lambda lambda)
                     (pfneg *biga*)
                     (pfneg (pfmul 2 x))))
       (yd (pfsub (pfmul lambda (pfsub x xd))
                  y)))
    (mv xd yd))
  :guard-hints (("Goal" :in-theory (enable (:e baby-jubjub-prime)))))

(define spec (x y xd yd)
  :guard (precond x y xd yd)
  (b* (((mv xd$ yd$) (montgomery-double x y)))
    (and (equal xd xd$)
         (equal yd yd$)))
  :guard-hints (("Goal" :in-theory (enable precond))))

; The circuit predicate is mechanically obtained as usual
; (e.g. see explanation in the MultiMux1 and MultiMux3 proofs).
; Note that 'lambda' is misspelled as 'lamda' in the Circom code;
; that is why the variable below is :|main.lamda| and not :|main.lambda|.

(define auxp (x^2 lambda)
  :returns (yes/no booleanp)
  (and (pfep x^2)
       (pfep lambda)))

(define circuit-core (x y xd yd x^2 lambda)
  :guard (and (precond x y xd yd)
              (auxp x^2 lambda))
  :returns (yes/no booleanp)
  (r1cs::r1cs-holdsp (acl2::montgomerydouble-make-r1cs)
                     (list (cons :|main.in[0]| x)
                           (cons :|main.in[1]| y)
                           (cons :|main.out[0]| xd)
                           (cons :|main.out[1]| yd)
                           (cons :|main.x1_2| x^2)
                           (cons :|main.lamda| lambda)))
  :guard-hints (("Goal" :in-theory (e/d (precond auxp r1cs::r1cs-valuationp)
                                        ((:e baby-jubjub-prime))))))

(define-sk circuit (x y xd yd)
  :guard (precond x y xd yd)
  :returns (yes/no booleanp)
  (exists (x^2 lambda)
          (and (auxp x^2 lambda)
               (circuit-core x y xd yd x^2 lambda))))

; We prove that the circuit implements the specification.
; The first theorem needs the bind-free versions
; of the rules for addition and negation;
; using the non-bind-free rules does not work -- the proof fails.
; Critically, we also need to enable division
; and the rule to distribute inverse over multiplication:
; this distribution enables certain cancelations
; in the subgoals generated by the calculations during the proofs.
; The second theorem is essentially mechanical.

(defruled circuit-core-implies-spec
  (implies (and (precond x y xd yd)
                (auxp x^2 lambda)
                (circuit-core x y xd yd x^2 lambda))
           (spec x y xd yd))
  :enable (precond
           auxp
           circuit-core
           r1cs::r1cs-holdsp
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           spec
           montgomery-double
           pfield::div
           pfield::inv-of-mul
           (:e baby-jubjub-prime))
  :prep-books ((include-book "kestrel/prime-fields/bind-free-rules" :dir :system)))

(defruled circuit-implies-spec
  (implies (and (precond x y xd yd)
                (circuit x y xd yd))
           (spec x y xd yd))
  :enable circuit
  :use (:instance circuit-core-implies-spec
        (x^2 (mv-nth 0 (circuit-witness x y xd yd)))
        (lambda (mv-nth 1 (circuit-witness x y xd yd)))))

; We prove that the circuit has solutions for the specification.
; The first theorem uses the same hints and books as its converse above,
; except that it needs the non-bind-free rules;
; using the bind-free rules does not work -- the proof loops.
; (This loop should be investigated.)
; The witnesses for the auxiliary variables are easily found,
; looking at the Circom code and the specification.
; The second theorem just establishes that the witnesses are field elements.
; The third theorems are essentially mechanical.

(defun x^2-witness (x)
  (pfmul x x))

(defun lambda-witness (x y)
  (pfdiv (pfaddall (pfmulall 3 x x)
                   (pfmulall 2 *biga* x)
                   1)
         (pfmulall 2 *bigb* y)))

(defruled spec-implies-circuit-core
  (implies (and (precond x y xd yd)
                (spec x y xd yd))
           (b* ((x^2 (x^2-witness x))
                (lambda (lambda-witness x y)))
             (circuit-core x y xd yd x^2 lambda)))
  :enable (precond
           auxp
           circuit-core
           r1cs::r1cs-holdsp
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           spec
           montgomery-double
           pfield::div
           pfield::inv-of-mul
           (:e baby-jubjub-prime))
  :prep-books ((include-book "kestrel/prime-fields/equal-of-add-rules" :dir :system)))

(defruled auxp-when-precond
  (implies (precond x y xd yd)
           (b* ((x^2 (x^2-witness x))
                (lambda (lambda-witness x y)))
             (auxp x^2 lambda)))
  :enable (precond auxp))

(defruled spec-implies-circuit
  (implies (and (precond x y xd yd)
                (spec x y xd yd))
           (circuit x y xd yd))
  :enable (spec-implies-circuit-core
           auxp-when-precond)
  :disable (x^2-witness lambda-witness)
  :use (:instance circuit-suff
        (x^2 (x^2-witness x))
        (lambda (lambda-witness x y))))

; The final theorem is mechanical.

(defruled circuit-is-spec
  (implies (precond x y xd yd)
           (equal (circuit x y xd yd)
                  (spec x y xd yd)))
  :use (circuit-implies-spec spec-implies-circuit))

; This proof works, but it seems somewhat indirect and fragile.
; Somewhat indirect: looking at the Circom code and the specification,
; the proof is really a couple of simple algebraic steps,
; but we need to use lots of rewrite rules in the proofs,
; and examination of the produced subgoals while developing the proofs
; reveals many unnecessary algebraic calculations and expansions;
; this proof is fast, but this indirection may be an issue in larger proofs.
; Somewhat fragile: as noted above, we must use
; the bind-free rules for one direction
; and the non-bind-free rules for the other direction;
; the reasons for this, and for the looping, are unclear at first sight.
