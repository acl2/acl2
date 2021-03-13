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
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

; (depends-on "json/edwards2montgomery.json")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains a proof of the Edwards2Montgomery() ciruit component
; (see the Circom code of Semaphore).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Load the circuit.

(acl2::load-circom-json "json/edwards2montgomery.json" '(baby-jubjub-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This circuit converts
; Edwards curve coordinates to Montgomery curve coordinates:
;
;               1 + y       1 + y
;   [u, v] = [ -------  , ---------- ]
;               1 - y      (1 - y)x
;
; Here x and y are the inputs (Edwards curve coordinates)
; while u and v are the outputs (Montgomery curve coordinates).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The circuit implicitly assumes that
; all the input and output variables are field elements,
; and that the denominators are not 0.
; We capture all of these assumptions in the precondition predicate.

(define precond (x y u v)
  :returns (yes/no booleanp)
  (and (pfep x)
       (pfep y)
       (pfep u)
       (pfep v)
       (not (equal x 0))
       (not (equal y 1))))

; The specification is the one sketched above,
; where all the operations are field operations.
; We formalize the specification as follows,
; but we should eventually use
; the elliptic curve library and the definition of BabyJubjub here.

(define edwards2montgomery ((x pfep) (y pfep))
  :guard (and (not (equal x 0))
              (not (equal y 1)))
  :returns (mv (u pfep) (v pfep))
  (b* ((u (pfdiv (pfadd 1 y)
                 (pfsub 1 y)))
       (v (pfdiv (pfadd 1 y)
                 (pfmul (pfsub 1 y) x))))
    (mv u v)))

(define spec (x y u v)
  :guard (precond x y u v)
  :returns (yes/no booleanp)
  (b* (((mv u$ v$) (edwards2montgomery x y)))
    (and (equal u u$)
         (equal v v$)))
  :guard-hints (("Goal" :in-theory (enable precond))))

; The circuit predicate is mechanically obtained as usual
; (e.g. see explanation in the MultiMux1 and MultiMux3 proofs).

(define circuit (x y u v)
  :guard (precond x y u v)
  :returns (yes/no booleanp)
  (r1cs::r1cs-holdsp (acl2::edwards2montgomery-make-r1cs)
                     (list (cons :|main.in[0]| x)
                           (cons :|main.in[1]| y)
                           (cons :|main.out[0]| u)
                           (cons :|main.out[1]| v)))
  :guard-hints (("Goal" :in-theory (e/d (precond r1cs::r1cs-valuationp)
                                        ((:e baby-jubjub-prime))))))

; Looking at the Circom code, the proof is really easy:
; just divide to go from the circuit to the specification,
; and just multiply to go from the specification to the circuit;
; also take into account the equality of u with (1+y)/(1-y) for v.
; The proof in ACL2 is more roundabout,
; but with the right rewrite rules we can get this proved.
; We need to disable the rules of distributivity of * over +,
; because they work against us here:
; for instance, they turn (1 - y) * x into x - x * y (see formulas above),
; but instead we want to treat (1 - y) as "atomic".
; We also need the rule PFIELD::INV-OF-MUL
; to turn 1/(a*b) into (1/a)*(1/b),
; which is critical to reach a normal form in which
; certain terms and their inverses can be canceled together
; (via other rules in the prime field library).
; We also need to expand division into multiplication by inverse:
; analogously to how subtraction is enabled by default,
; perhaps division should be also enabled by default.

(defruled circuit-is-spec
  (implies (precond u v x y)
           (equal (circuit u v x y)
                  (spec u v x y)))
  :enable (precond
           circuit
           r1cs::r1cs-holdsp
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           spec
           edwards2montgomery
           pfield::div
           pfield::inv-of-mul
           (:e baby-jubjub-prime))
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2))
