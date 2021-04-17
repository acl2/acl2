; A tool to verify an R1CS
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "kestrel/axe/conjoin-term-with-dag" :dir :system)
(include-book "kestrel/crypto/r1cs/fe-listp-fast" :dir :system)
(include-book "kestrel/crypto/r1cs/proof-support" :dir :system) ;for make-bitp-claims

;; Note that this only does the "forward" direction of the proof
(defmacro verify-r1cs (lifted-r1cs ; a DAG
                       spec-term ; a term over the input and output vars, not evaluated
                       prime     ; the prime for the R1CS
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
  `(encapsulate ()
     ;; Print the prime more clearly:
     (table acl2::evisc-table ,prime "<p>") ;a bit scary since it makes p look like a var

     ;; TODO: Suppress printing of error output at the end of failed proofs:
     (acl2::prove-implication-with-r1cs-prover
      (acl2::conjoin-term-with-dag! (acl2::make-conjunction-from-list
                                     (cons
                                      ;; Assume all vars are field elements:
                                      (pfield::gen-fe-listp-assumption (acl2::dag-vars ,lifted-r1cs)
                                                                       ;; bake in baby-jubjub-prime:
                                                                       '',prime)
                                      ;; Assume that the inputs are bits:
                                      (acl2::make-bitp-claims ,bit-inputs)))
                                    ,lifted-r1cs)
      ',spec-term
      :tactic ,tactic
      :rule-lists ,rule-lists     ;todo: use a default rule-list
      :global-rules ,global-rules ;todo: add some default global-rules
      :interpreted-function-alist ,interpreted-function-alist ;todo
      :no-splitp ,no-splitp
      :monitor ,monitor
      :print ,print)))
