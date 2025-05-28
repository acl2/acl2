; A tool to verify an R1CS
;
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "axe-prover-r1cs") ; since this calls prove-implication-with-r1cs-prover
(include-book "kestrel/utilities/defmacrodoc" :dir :system)
(include-book "kestrel/axe/conjoin-term-with-dag" :dir :system)
(include-book "kestrel/prime-fields/fe-listp-fast" :dir :system)
(include-book "kestrel/crypto/r1cs/proof-support" :dir :system) ;for make-bitp-claims
(include-book "kestrel/axe/known-booleans" :dir :system)

;todo: not sure where these should go:
(acl2::add-known-boolean primep)
(acl2::add-known-boolean pfield::fep)
(acl2::add-known-boolean pfield::fe-listp)

;; Returns an event
(defun verify-r1cs-fn (lifted-r1cs
                       spec-term
                       prime
                       bit-inputs
                       tactic
                       rule-lists ;todo: improve by building some in and allowing :extra-rules and :remove-rules? ;todo: what if we give these but no :rewrite tactic
                       global-rules ;; rules to be added to every rule-list
                       use
                       var-ordering
                       interpreted-function-alist
                       no-splitp ; whether to prevent splitting into cases (note that we change the default here)
                       print-as-clausesp
                       no-print-fns
                       monitor
                       print)
  (declare (xargs :guard t))
  `(encapsulate ()
     ;; Print the prime more clearly:
     (table acl2::evisc-table ,prime "<p>") ;a bit scary since it makes p look like a var

     ;; TODO: Suppress printing of error output at the end of failed proofs:
     (acl2::prove-implication-with-r1cs-prover
      (acl2::conjoin-term-with-dag! (acl2::make-conjunction-from-list
                                     (cons
                                      ;; Assume all vars are field elements:
                                      (pfield::gen-fe-listp-assumption (acl2::dag-vars-unsorted ,lifted-r1cs)
                                                                       ;; bake in baby-jubjub-prime:
                                                                       '',prime)
                                      ;; Assume that the inputs are bits:
                                      (acl2::make-bitp-claims ,bit-inputs)))
                                    ,lifted-r1cs)
      ',spec-term
      :tactic ,tactic
      :rule-lists ,rule-lists     ;todo: use a default rule-list
      :global-rules ,global-rules ;todo: add some default global-rules
      :use ,use
      :var-ordering ,var-ordering
      :interpreted-function-alist ,interpreted-function-alist ;todo
      :no-splitp ,no-splitp
      :print-as-clausesp ,print-as-clausesp
      :no-print-fns ,no-print-fns
      :monitor ,monitor
      :print ,print)))

;; Note that this only does the "forward" direction of the proof.  But see a-3-3-1-proof.lisp for an example
;; that includes the "backward" direction as well.
(acl2::defmacrodoc verify-r1cs (lifted-r1cs
                                spec-term
                                prime
                                &key
                                (bit-inputs 'nil)
                                ;; same as for acl2::prove-implication-with-r1cs-prover:
                                (tactic ''(:rep :rewrite :subst))
                                (rule-lists 'nil) ;todo: improve by building some in and allowing :extra-rules and :remove-rules? ;todo: what if we give these but no :rewrite tactic
                                (global-rules 'nil) ;; rules to be added to every rule-list
                                (use 'nil) ; :use hints
                                (var-ordering 'nil)
                                (interpreted-function-alist 'nil)
                                (no-splitp 't) ; whether to prevent splitting into cases (note that we change the default here)
                                (print-as-clausesp 'nil)
                                (no-print-fns ''(fe-listp)) ; fe-listp terms can be huge
                                (monitor 'nil)
                                (print ':brief))
  (verify-r1cs-fn lifted-r1cs spec-term prime
                  bit-inputs tactic rule-lists global-rules use var-ordering interpreted-function-alist
                  no-splitp print-as-clausesp no-print-fns monitor print)
  :parents (acl2::axe-r1cs)
  :short "A tool to verify an R1CS"
  :description "See @(tsee acl2::axe-r1cs)."
  :args ((lifted-r1cs "A DAG representing the lifted R1CS")
         (spec-term "A term over the input and output vars (this input is not evaluated)")
         (prime "The prime for the R1CS")
         (bit-inputs "Variables for which to generate BITP assumptions")
         (tactic "The Axe tactic to use")
         (rule-lists "A sequence of Axe rule sets, each of which is a list of rule names and/or calls of 0-ary functions that return lists of rule names.  These are applied one after the other.")
         (global-rules "Rules to add to every rule-list in the sequence")
         (use "Axe :use hints for the proof (satisfies axe-use-hintp)")
         (var-ordering "Ordering on the vars, to restrict substitutions that express earlier vars in terms of later vars.  Not all vars need to be mentioned.")
         (interpreted-function-alist "An interpreted-function-alist to evaluate ground terms") ;todo: document
         (no-splitp "Whether to split into cases") ;todo: switch it to :splitp? or :allow-splitting?  why is splitting not a tactic?!
         (print-as-clausesp "Whether to print proof goals as clauses (disjunctions to be proved), rather than conjunctions of negated literals (to be proved contradictory)")
         (no-print-fns "Functions to skip over when printing the current case.")
         (monitor "Rules to monitor during rewriting")
         (print "Axe print argument") ;todo: document
         ))
