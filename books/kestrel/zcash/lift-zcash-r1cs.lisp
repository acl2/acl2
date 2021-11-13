; A Zcash-specific version of lift-r1cs
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "kestrel/axe/r1cs/lift-r1cs" :dir :system)

;; A thin wrapper around lift-r1cs that sets the prime and the package for Zcash.
;; If the VARS are keywords (which is common), they get converted to the ZCASH package.
(acl2::defmacrodoc lift-zcash-r1cs (name-of-defconst
                                    vars
                                    constraints
                                    &key
                                    (rules ':auto)
                                    (extra-rules 'nil)
                                    (remove-rules 'nil)
                                    (monitor 'nil)
                                    (memoizep 'nil)
                                    (count-hitsp 'nil)
                                    (print 'nil))
  `(r1cs::lift-r1cs ,name-of-defconst
                    ,vars
                    ,constraints
                    ;; This is (zcash::jubjub-q):
                    52435875175126190479447740508185965837690552500527637822603658699938581184513
                    :package "ZCASH"
                    :rules ,rules
                    :extra-rules ,extra-rules
                    :remove-rules ,remove-rules
                    :monitor ,monitor
                    :memoizep ,memoizep
                    :count-hitsp ,count-hitsp
                    :print ,print)
  :parents (zcash r1cs::lift-r1cs r1cs::r1cs-verification-with-axe)
  :short "A tool to lift a zcash R1CS"
  :description "This tool is a wrapper for @(tsee r1cs::lift-r1cs) that sets the prime to @(tsee jubjub-q) and sets the package to @('ZCASH').  See also @(tsee r1cs::r1cs-verification-with-axe)."
  :args ((name-of-defconst "The name of the defconst (a symbol) that will be created to hold the DAG.  This name should start and end with @('*').")
         (vars "A form that evaluates to the variables of the R1CS.")
         (constraints "A form that evaluates to the constraints of the R1CS.")
         (rules "Either :auto, or a form that evaluates to a list of symbols.  If the latter, the given rules replace the default rules used for lifting.")
         (extra-rules "Rules to be added to the default rule set used for lifting.  A form that evaluates to a list of symbols.  May be non-@('nil') only when @('rules') is @(':auto').")
         (remove-rules "Rules to be removed from the default rule set used for lifting.  A form that evaluates to a list of symbols.  May be non-@('nil') only when @('rules') is @(':auto').")
         (monitor "Rules to monitor during rewriting.  A form that evaluates to a list of symbols")
         (memoizep "Whether to perform memoization during rewriting.  A boolean.  This may actually slow down the lifting process.")
         (count-hitsp "Whether to count rule hits during rewriting (may cause rewriting to be somewhat slower).  A boolean.")
         (print "Axe print argument") ;todo: document
         ))
