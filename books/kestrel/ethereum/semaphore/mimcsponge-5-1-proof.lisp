; A proof of the mimcsponge-5-1-0k r1cs
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "json-to-r1cs/load-circom-json")
(include-book "proof-tools")
(include-book "kestrel/crypto/r1cs/tools/axe-prover-r1cs" :dir :system)
(include-book "kestrel/crypto/mimc/mimcsponge-spec-rules" :dir :system)

;;;
;;; The spec
;;;

(defun mimcsponge-5-1-spec (in0 in1 in2 in3 in4 out)
  (declare (xargs :guard (and (fep in0 (baby-jubjub-prime))
                              (fep in1 (baby-jubjub-prime))
                              (fep in2 (baby-jubjub-prime))
                              (fep in3 (baby-jubjub-prime))
                              (fep in4 (baby-jubjub-prime))
                              (fep out (baby-jubjub-prime)))
                  :guard-hints (("Goal" :in-theory (enable (:e baby-jubjub-prime))))))
  (equal out (car (mimc::mimcsponge-semaphore 5 1 (list in0 in1 in2 in3 in4)))))

;;;
;;; Load the R1CS:
;;;

;; 3305 vars
;; 3300 constraints
;; (depends-on "json/mimcsponge-5-1-0k.json")
(local (acl2::load-circom-json "json/mimcsponge-5-1-0k.json" *baby-jubjub-prime*))

;;;
;;; Unroll the R1CS
;;;

(local
 (lift-semaphore-r1cs *mimcsponge-5-1-0k-r1cs-lifted*
                      (acl2::mimcsponge-5-1-0k-vars)
                      (acl2::mimcsponge-5-1-0k-constraints)))

;;;
;;; Prove that the spec holds, assuming the R1CS holds
;;;

(acl2::prove-implication-with-r1cs-prover
 *mimcsponge-5-1-0k-r1cs-lifted*
 '(mimcsponge-5-1-spec |main.ins[0]|
                       |main.ins[1]|
                       |main.ins[2]|
                       |main.ins[3]|
                       |main.ins[4]|
                       |main.outs[0]|)
 :rule-lists '( ;; empty rule set to force substitution, keeping the spec
               ;; closed to keep the dag small:
               ()
               ;; now open the spec:
               (mimcsponge-5-1-spec
                (mimc-spec-rules)
                (acl2::base-rules)
                (acl2::amazing-rules-bv)
                (acl2::list-rules)
                (pfield::add-and-mul-normalization-rules)
                acl2::equal-same)))
