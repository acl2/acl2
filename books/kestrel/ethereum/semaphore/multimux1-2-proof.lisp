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

; (depends-on "json/multimux1-2.json")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains a proof of the MultiMux1(2) ciruit component
; (see the Circom code of Semaphore).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Load the circuit.

(acl2::load-circom-json "json/multimux1-2.json" '(baby-jubjub-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The circuit does not constraint s to be a bit (which it could).
; (If s is not a bit, the circuit does not work as intended.)
; There is also an implicit assumption that
; the inputs and outputs are field elements;
; without this assumption, we can only prove MOD-equivalence.
; So we collect all of these assumptions into a predicate:
; this is a precondition of the circuit.

(define precond (s c00 c01 c10 c11 out0 out1)
  :returns (yes/no booleanp)
  (and (bitp s)
       (pfep c00)
       (pfep c01)
       (pfep c10)
       (pfep c11)
       (pfep out0)
       (pfep out1)))

; This is the functional specification of the circuit.
; Picturing the cij inputs as a table,
; the s input selects a column as the outi outputs.
;
;  +-----+-----+    +------+
;  | c00 | c01 |    | out0 |
;  +-----+-----+    +------+
;  | c10 | c11 |    | out1 |
;  +-----+-----+    +------+

(define multimux1-2 ((s bitp)
                     (c00 pfep)
                     (c01 pfep)
                     (c10 pfep)
                     (c11 pfep))
  :returns (mv (out0 pfep :hyp :guard)
               (out1 pfep :hyp :guard))
  (mv (nth s (list c00 c01))
      (nth s (list c10 c11))))

; To state the correctness of the circuit w.r.t. the function above,
; we need to turn the function above into a predicate, in the obvious way.
; The relation says that outi = cis, for i in {0, 1}.

(define spec (s c00 c01 c10 c11 out0 out1)
  :guard (precond s c00 c01 c10 c11 out0 out1)
  :returns (yes/no booleanp)
  (b* (((mv out0$ out1$) (multimux1-2 s c00 c01 c10 c11)))
    (and (equal out0 out0$)
         (equal out1 out1$)))
  :guard-hints (("Goal" :in-theory (enable precond))))

; To state the correctness of the circuit w.r.t. the specification above,
; we need to turn the circuit into a predicate,
; which we do via the R1CS semantics applied to the circuit obtained by
; compiling the Circom file and then converting the resulting JSON file.
; This kind of predicate definition could be automatically generated
; from just the circuit via a macro.
; Note that there are no auxiliary variables here,
; only input and output variables (the same as in the specification above),
; so there is no witness finding needed.

(define circuit (s c00 c01 c10 c11 out0 out1)
  :guard (precond s c00 c01 c10 c11 out0 out1)
  :returns (yes/no booleanp)
  (r1cs::r1cs-holdsp (acl2::multimux1-2-make-r1cs)
                     (list (cons :|main.s| s)
                           (cons :|main.c[0][0]| c00)
                           (cons :|main.c[0][1]| c01)
                           (cons :|main.c[1][0]| c10)
                           (cons :|main.c[1][1]| c11)
                           (cons :|main.out[0]| out0)
                           (cons :|main.out[1]| out1)))
  :guard-hints (("Goal" :in-theory (e/d (precond r1cs::r1cs-valuationp)
                                        ((:e baby-jubjub-prime))))))

; This is the proof of correctness of the circuit w.r.t. the specification,
; under the precondition.
; The proof is absolutely trivial when sketched on paper.
; Convincing ACL2 of that takes, as expected, slightly more effort.
; We need to enable the functions that describe
; the precondition, the specification, the circuit, and the R1CS semantics:
; these rules turn the R1CS constraints into shallowly embedded counterparts,
; which are then related, and proved equivalent via algebraic manipulations,
; to the constraints in the specification.
; It is very important that the executable counterpart
; of the generated nullary function MULTIMUX1-2-MAKE-R1CS is disabled,
; otherwise submitting the theorem hangs without any feedback,
; which may be confusing.
; But the function MULTIMUX1-2-MAKE-R1CS itself must be enabled,
; so that the R1CS constraints can be uncovered
; and turned into shallowly embedded counterparts.
; The JSON-to-R1CS conversion tool generates a MULTIMUX1-2-MAKE-R1CS function
; that is indeed enabled but with a disabled executable counterpart,
; so we do not need to add any hints to that effect here.

(defruled circuit-is-spec
  (implies (precond s c00 c01 c10 c11 out0 out1)
           (equal (circuit s c00 c01 c10 c11 out0 out1)
                  (spec s c00 c01 c10 c11 out0 out1)))
  :enable (precond
           circuit
           r1cs::r1cs-holdsp
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           spec
           multimux1-2
           (:e baby-jubjub-prime))
  :prep-books
  ((include-book "kestrel/prime-fields/equal-of-add-rules" :dir :system)))
