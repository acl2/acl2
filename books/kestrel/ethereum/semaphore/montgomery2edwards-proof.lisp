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

; (depends-on "json/montgomery2edwards.json")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains a proof of the Montgomery2Edwards() ciruit component
; (see the Circom code of Semaphore).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Load the circuit.

(acl2::load-circom-json "json/montgomery2edwards.json" '(baby-jubjub-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This circuit converts
; Montgomery curve coordinates to Edwards curve coordinates:
;
;               u    u - 1
;   [x, y] = [ ---, ------- ]
;               v    u + 1
;
; Here u and v are the inputs (Montgomery curve coordinates)
; while x and y are the outputs (Edwards curve coordinates).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The circuit implicitly assumes that
; all the input and output variables are field elements,
; and that the denominators are not 0.
; We capture all of these assumptions in the precondition predicate.

(define precond (u v x y)
  :returns (yes/no booleanp)
  (and (pfep u)
       (pfep v)
       (pfep x)
       (pfep y)
       (not (equal u (pfminus1)))
       (not (equal v 0))))

; The specification is the one sketched above,
; where all the operations are field operations.
; We formalize the specification as follows,
; but we should eventually use
; the elliptic curve library and the definition of BabyJubjub here.

(define montgomery2edwards ((u pfep) (v pfep))
  :guard (and (not (equal u (pfminus1)))
              (not (equal v 0)))
  :returns (mv (x pfep) (y pfep))
  (b* ((x (pfdiv u v))
       (y (pfdiv (pfsub u 1)
                 (pfadd u 1))))
    (mv x y))
  :guard-hints (("Goal" :in-theory (enable (:e baby-jubjub-prime)))))

(define spec (u v x y)
  :guard (precond u v x y)
  :returns (yes/no booleanp)
  (b* (((mv x$ y$) (montgomery2edwards u v)))
    (and (equal x x$)
         (equal y y$)))
  :guard-hints (("Goal" :in-theory (enable precond))))

; The circuit predicate is mechanically obtained as usual
; (e.g. see explanation in the MultiMux1 and MultiMux3 proofs).

(define circuit (u v x y)
  :guard (precond u v x y)
  :returns (yes/no booleanp)
  (r1cs::r1cs-holdsp (acl2::montgomery2edwards-make-r1cs)
                     (list (cons :|main.in[0]| u)
                           (cons :|main.in[1]| v)
                           (cons :|main.out[0]| x)
                           (cons :|main.out[1]| y)))
  :guard-hints (("Goal" :in-theory (e/d (precond r1cs::r1cs-valuationp)
                                        ((:e baby-jubjub-prime))))))

; Looking at the Circom code, the proof is really easy:
; just divide to go from the circuit to the specification,
; and just multiply to go from the specification to the circuit.
; The proof in ACL2 is more roundabout,
; but with the right rewrite rules we can get this proved.
; We need to disable the rules of distributivity of * over +,
; because they work against us here:
; for instance, they turn y * (u + 1) into y * y + y (see formulas above),
; but instead we want to treat (u + 1) as "atomic".
; We use the rule PFIELD::INV-OF-MUL (enabled below)
; to turn 1/(a*b) into (1/a)*(1/b),
; which is critical to reach a normal form in which
; certain terms and their inverses can be canceled together
; (via other rules in the prime field library).
; We also need to expand division into multiplication by inverse:
; analogously to how subtraction is enabled by default,
; perhaps division should be also enabled by default.

(defruled circuit-is-spec
  (implies (precond x y u v)
           (equal (circuit x y u v)
                  (spec x y u v)))
  :enable (precond
           circuit
           r1cs::r1cs-holdsp
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           spec
           montgomery2edwards
           pfield::div
           pfield::inv-of-mul
           (:e baby-jubjub-prime))
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2))
