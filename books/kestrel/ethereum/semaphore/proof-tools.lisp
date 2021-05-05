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
(acl2::defmacrodoc verify-semaphore-r1cs (lifted-r1cs ; a DAG
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
                      :print ,print)
    :parents (semaphore r1cs::r1cs-verification-with-axe)
    :short "A tool to verify a semaphore R1CS"
    :long "This tool is a wrapper for @(tsee r1cs::verify-r1cs) that sets the prime to @(tsee baby-jubjub-prime). See also @(tsee r1cs::r1cs-verification-with-axe)."
    :inputs (lifted-r1cs "A DAG representing the lifted R1CS"
            spec-term "A term over the input and output vars (this input is not evaluated)"
            :bit-inputs "Variables for which to generate BITP assumptions"
            :tactic "The Axe tactic to use"
            :rule-lists "A sequence of Axe rule sets, each of which is a list of rule names and/or calls of 0-ary functions that return lists of rule names.  These are applied one after the other."
            :global-rules "Rules to add to every rule-list in the sequence"
            :interpreted-function-alist "An interpreted-function-alist to evaluate ground terms" ;todo: document
            :no-splitp "Whether to split into cases" ;todo: switch it to :splitp? or :allow-splitting?  why is splitting not a tactic?!
            :monitor "Rules to monitor during rewriting"
            :print "Axe print argument" ;todo: document
            ))
