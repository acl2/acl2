; Semaphore-specific versions of R1CS proof tools
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "kestrel/crypto/r1cs/tools/lift-r1cs" :dir :system)
(include-book "kestrel/crypto/r1cs/tools/verify-r1cs" :dir :system)

;; A thin wrapper around lift-r1cs-new that sets the prime for semaphore.
;; If the VARS are keywords (which is common), they get converted to the ZKSEMAPHORE package."
(defmacro lift-semaphore-r1cs (name-of-defconst vars constraints &rest args)
  `(r1cs::lift-r1cs-new ,name-of-defconst
                        ,vars
                        ,constraints
                        ;; This is baby-jubjub-prime:
                        21888242871839275222246405745257275088548364400416034343698204186575808495617
                        :package "ZKSEMAPHORE"
                        ,@args))

;; A wrapper of verify-r1cs that specializes it for the semaphore prime
(defmacro verify-semaphore-r1cs (lifted-r1cs ; a DAG
                                 spec-term ; a term over the input and output vars, not evaluated
                                 &key
                                 (bit-inputs 'nil) ; bitp assumptions will be generated for these
                                 ;; same as for acl2::prove-implication-with-r1cs-prover:
                                 (tactic ''(:rep :rewrite :subst))
                                 (rule-lists 'nil) ;todo: improve by building some in and allowing :extra-rules and :remove-rules?
                                 (global-rules 'nil) ;; rules to be added to every rule-list
                                 (interpreted-function-alist 'nil)
                                 (no-splitp 't) ; whether to prevent splitting into cases (note that we change the default here)
                                 (monitor 'nil)
                                 (print ':brief))
  `(r1cs::verify-r1cs ,lifted-r1cs
                      ,spec-term
                      21888242871839275222246405745257275088548364400416034343698204186575808495617
                      :bit-inputs ,bit-inputs
                      :tactic ,tactic
                      :rule-lists ,rule-lists
                      :global-rules ,global-rules
                      :interpreted-function-alist ,interpreted-function-alist
                      :no-splitp ,no-splitp
                      :monitor ,monitor
                      :print ,print))
