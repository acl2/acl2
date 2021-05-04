; A tool to verify an R1CS
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "kestrel/utilities/doc" :dir :system)
(include-book "kestrel/axe/conjoin-term-with-dag" :dir :system)
(include-book "kestrel/crypto/r1cs/fe-listp-fast" :dir :system)
(include-book "kestrel/crypto/r1cs/proof-support" :dir :system) ;for make-bitp-claims
(include-book "kestrel/axe/known-booleans" :dir :system)

;todo: not sure where these should go:
(acl2::add-known-boolean rtl::primep)
(acl2::add-known-boolean pfield::fep)
(acl2::add-known-boolean pfield::fe-listp)

;; Note that this only does the "forward" direction of the proof
(acl2::defmacrodoc verify-r1cs (lifted-r1cs
                                spec-term
                                prime
                                &key
                                (bit-inputs 'nil)
                                ;; same as for acl2::prove-implication-with-r1cs-prover:
                                (tactic ''(:rep :rewrite :subst))
                                (rule-lists 'nil) ;todo: improve by building some in and allowing :extra-rules and :remove-rules? ;todo: what if we give these but no :rewrite tactic
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
      :print ,print))
  :parents (r1cs-verification-with-axe)
  :short "A tool to verify an R1CS"
  :long "See @(tsee r1cs-verification-with-axe)."
  :inputs (lifted-r1cs "A DAG representing the lifted R1CS"
                       spec-term "A term over the input and output vars (this input is not evaluated)"
                       prime "The prime for the R1CS"
                       :bit-inputs "Variables for which to generate BITP assumptions"
                       :tactic "The Axe tactic to use"
                       :rule-lists "A sequence of Axe rule sets, each of which is a list of rule names and/or calls of 0-ary functions that return lists of rule names.  These are applied one after the other."
                       :global-rules "Rules to add to every rule-list in the sequence"
                       :interpreted-function-alist "An interpreted-function-alist to evaluate ground terms" ;todo: document
                       :no-splitp "Whether to split into cases" ;todo: switch it to :splitp? or :allow-splitting?  why is splitting not a tactic?!
                       :monitor "Rules to monitor during rewriting"
                       :print "Axe print argument" ;todo: document
                       ))
