; Zcash-specific version of verify-r1cs
;
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "kestrel/axe/r1cs/verify-r1cs" :dir :system)

;; A wrapper of verify-r1cs that specializes it for the zcash prime
(acl2::defmacrodoc verify-zcash-r1cs (lifted-r1cs ; a DAG
                                      spec-term ; a term over the input and output vars, not evaluated
                                      &key
                                      (bit-inputs 'nil) ; bitp assumptions will be generated for these
                                      ;; same as for acl2::prove-implication-with-r1cs-prover:
                                      (tactic ''(:rep :rewrite :subst))
                                      (rule-lists 'nil) ;todo: improve by building some in and allowing :extra-rules and :remove-rules?
                                      (global-rules 'nil) ;; rules to be added to every rule-list
                                      (use 'nil)
                                      (var-ordering 'nil)
                                      (interpreted-function-alist 'nil)
                                      (no-splitp 't) ; whether to prevent splitting into cases (note that we change the default here)
                                      (print-as-clausesp 'nil)
                                      (monitor 'nil)
                                      (print ':brief))
  `(r1cs::verify-r1cs ,lifted-r1cs
                      ,spec-term
                      ;; the prime (zcash::jubjub-q):
                      52435875175126190479447740508185965837690552500527637822603658699938581184513
                      :bit-inputs ,bit-inputs
                      :tactic ,tactic
                      :rule-lists ,rule-lists
                      :global-rules ,global-rules
                      :use ,use
                      :var-ordering ,var-ordering
                      :interpreted-function-alist ,interpreted-function-alist
                      :no-splitp ,no-splitp
                      :print-as-clausesp ,print-as-clausesp
                      :monitor ,monitor
                      :print ,print)
  :parents (zcash r1cs::verify-r1cs acl2::axe-r1cs)
  :short "A tool to verify a zcash R1CS"
  :description "This tool is a wrapper for @(tsee r1cs::verify-r1cs) that sets the prime to @(tsee jubjub-q). See also @(tsee acl2::axe-r1cs)."
  :args ((lifted-r1cs "A <see topic=\"@(url acl2::dags)\">DAG</see> representing the lifted R1CS")
         (spec-term "A term over the input and output vars (this input is not evaluated)")
         (bit-inputs "Variables for which to generate BITP assumptions")
         (tactic "The Axe tactic to use")
         (rule-lists "A sequence of Axe rule sets, each of which is a list of rule names and/or calls of 0-ary functions that return lists of rule names.  These are applied one after the other.")
         (global-rules "Rules to add to every rule-list in the sequence")
         (use "Axe :use hints for the proof (satisfies axe-use-hintp)")
         (var-ordering "Ordering on the vars, to restrict substitutions that express earlier vars in terms of later vars.  Not all vars need to be mentioned.")
         (interpreted-function-alist "An interpreted-function-alist to evaluate ground terms" ;todo: document
                                     )
         (no-splitp "Whether to split into cases") ;todo: switch it to :splitp? or :allow-splitting?  why is splitting not a tactic?!
         (print-as-clausesp "Whether to print proof goals as clauses (disjunctions to be proved), rather than conjunctions of negated literals (to be proved contradictory)")
         (monitor "Rules to monitor during rewriting")
         (print "Axe print argument") ;todo: document
         ))
