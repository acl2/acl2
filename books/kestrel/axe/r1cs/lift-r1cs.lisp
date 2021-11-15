; Lifter for R1CSes (in sparse form)
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; A new version of the lifter for R1CSes in sparse form.  This version creates
;; a defconst containing the resulting DAG, but it does not embed the DAG in a
;; defun (thus, this version does not depend on any skip-proofs).

(include-book "lift-r1cs-rules")
(include-book "lift-r1cs-rule-lists")
(include-book "kestrel/utilities/doc" :dir :system)
(include-book "kestrel/crypto/r1cs/sparse/rule-lists" :dir :system)
(include-book "kestrel/crypto/r1cs/sparse/rules-axe" :dir :system)
(include-book "kestrel/crypto/r1cs/sparse/rules" :dir :system)
(include-book "lift-r1cs-common")
(include-book "kestrel/axe/def-simplified" :dir :system)
(include-book "kestrel/axe/interpreted-function-alists" :dir :system) ; for make-interpreted-function-alist
(include-book "kestrel/prime-fields/prime-fields-rules-axe" :dir :system)
(include-book "kestrel/prime-fields/bitp-idioms" :dir :system)
(include-book "kestrel/prime-fields/rules2" :dir :system)
(include-book "kestrel/utilities/ensure-rules-known" :dir :system)
;; The following include-books bring in rules mentioned in lift-r1cs-rules:
(include-book "kestrel/arithmetic-light/mod" :dir :system) ; for ACL2::MOD-OF-1-ARG1

;; Check that all the rules we'll use for lifting have been brought in above:
(acl2::ensure-rules-known (lift-r1cs-rules))

(defun fep-assumptions-for-vars-aux (vars prime acc)
  (declare (xargs :guard (and (symbol-listp vars)
                              (true-listp acc))))
  (if (endp vars)
      (acl2::reverse-list acc)
    (fep-assumptions-for-vars-aux (rest vars)
                                  prime
                                  (cons `(fep ,(first vars) ,prime)
                                        acc))))

;; Make a list of assertions stating that each of the VARS satisfies fep.
(defun fep-assumptions-for-vars (vars prime)
  (declare (xargs :guard (symbol-listp vars)))
  (fep-assumptions-for-vars-aux vars prime nil))

;; Makes an alist that binds vars to versions of themselves in the indicated
;; PACKAGE.  Except if PACKAGE is :auto, non-keywords get bound to themselves
;; and keywords bound to their counterparts int the ACL2 package (since
;; keywords are not legal var names).
(defun r1cs-var-to-lifted-var-alist (vars package acc)
  (declare (xargs :guard (and (symbol-listp vars)
                              (or (eq :auto package)
                                  (and (stringp package)
                                       (not (equal "" package))))
                              (alistp acc))))
  (if (endp vars)
      (acl2::reverse-list acc)
    (let* ((var (first vars))
           (new-var (if (eq :auto package)
                        (if (equal "KEYWORD" (symbol-package-name var))
                            (intern (symbol-name var) "ACL2")
                          ;; package is already ok
                          var)
                      ;; Switch the package of the var to PACKAGE:
                      (intern$ (symbol-name var) package))))
      (r1cs-var-to-lifted-var-alist (rest vars) package (acons var new-var acc)))))

;; Returns (mv erp event state).
(defun lift-r1cs-fn (name-of-defconst
                     vars ; may be keywords, in which case we switch to PACKAGE (if not :auto) or to the acl2 package
                     constraints
                     prime
                     package
                     extra-rules remove-rules rules
                     monitor memoizep
                     count-hitsp
                     print
                     whole-form state)
  (declare (xargs :guard (and (symbolp name-of-defconst)
                              (symbol-listp vars)
                              (r1cs-constraint-listp constraints)
                              ;;(r1csp r1cs)
                              (natp prime) ;;(rtl::primep prime) ;todo, slow!
                              (or (eq :auto package)
                                  (and (stringp package)
                                       (not (equal "" package))))
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (or (eq :auto rules) (symbol-listp rules))
                              (symbol-listp monitor)
                              (booleanp memoizep)
                              (booleanp count-hitsp))
                  :mode :program
                  :stobjs state))
  (b* ( ;; (vars (r1cs->vars r1cs))
       ;; (constraints (r1cs->constraints r1cs))
       ;; Maps the vars in the R1CS (which are just symbols in that piece of
       ;; data) to ACL2 variables for the proof:
       (r1cs-var-to-lifted-var-alist (r1cs-var-to-lifted-var-alist vars package nil))
       (lifted-vars (strip-cdrs r1cs-var-to-lifted-var-alist))
       ((acl2::when (not (no-duplicatesp lifted-vars))) ;todo: optimize by sorting
        (er hard? 'lift-r1cs-fn "Duplicate var(s) detected in ~X01." lifted-vars nil)
        (mv :duplicate-vars nil state))
       (term-to-simplify `(r1cs::r1cs-constraints-holdp ',constraints
                                                        ,(make-efficient-symbolic-valuation-for-alist r1cs-var-to-lifted-var-alist)
                                                        ',prime))
       ((acl2::when (and (not (eq :auto rules)) extra-rules))
        (er hard? 'lift-r1cs-fn ":rules and :extra-rules should not both be given.")
        (mv :bad-input nil state))
       ((acl2::when (and (not (eq :auto rules)) remove-rules))
        (er hard? 'lift-r1cs-fn ":rules and :remove-rules should not both be given.")
        (mv :bad-input nil state)))
    (acl2::def-simplified-fn name-of-defconst
                             term-to-simplify
                             ;; The extra rules:
                             (if (not (eq :auto rules))
                                 nil ;rules are given below, so extra-rules are not allowed
                               (append (lift-r1cs-rules)
                                       extra-rules))
                             remove-rules
                             rules ;to override the default
                             ;; nil ;rule-alists
                             ;; drop? but we need to know that all lookups of vars give integers:
                             ;; TODO: Use the more compact machinery for this?:
                             (fep-assumptions-for-vars lifted-vars prime)
                             ;; TODO: Add more functions to this?
                             ;; TODO: Make this once and store it?
                             (acl2::make-interpreted-function-alist '(r1cs::r1cs-constraint->a$inline
                                                                      r1cs::r1cs-constraint->b$inline
                                                                      r1cs::r1cs-constraint->c$inline
                                                                      assoc-equal ; called by r1cs::r1cs-constraint->a$inline, etc
                                                                      ;; todo: i had assoc here; should that be an error?
                                                                      mul
                                                                      neg
                                                                      add
                                                                      pfield::pos-fix
                                                                      pfield::fep)
                                                                    (w state))
                             monitor
                             memoizep
                             count-hitsp
                             ;; nil                             ;simplify-xorsp
                             print
                             whole-form
                             state)))

;; NOTE: Keep this in sync with lift-zcash-r1cs.
(acl2::defmacrodoc lift-r1cs (&whole whole-form
                                     name-of-defconst ; name of the defconst to create, will hold the lifted R1CS, in DAG form
                                     ;; r1cs ;todo: currentlty can't make the r1cs (due to prime tests?)
                                     vars ;; the variables of the R1CS to lift
                                     constraints ;; the constraints of the R1CS to lift
                                     prime ;; the prime of the R1CS to lift
                                     &key
                                     (package ':auto) ; package to use for vars
                                     (rules ':auto)
                                     (extra-rules 'nil)
                                     (remove-rules 'nil)
                                     (monitor 'nil)
                                     (memoizep 'nil) ;; memoization can slow down R1CS lifting a lot, due to many terms with the same single nodenum (the valuation?) being put into the same memo slot
                                     (count-hitsp 'nil)
                                     (print 'nil))
  `(acl2::make-event-quiet (lift-r1cs-fn ',name-of-defconst
                                         ,vars
                                         ,constraints
                                         ,prime
                                         ,package
                                         ,extra-rules
                                         ,remove-rules
                                         ,rules
                                         ,monitor
                                         ,memoizep
                                         ,count-hitsp
                                         ,print
                                         ',whole-form
                                         state))
  :parents (r1cs-verification-with-axe)
  :short "A tool to lift an R1CS into logic"
  :description "Lifts an R1CS into a logical term, represented as an Axe DAG.  Takes an R1CS, given as a list of variables, a list of constraints, and a prime.  Creates a constant DAG whose name is the @('name-of-defconst') input supplied by the user.  The lifting is done by applying the Axe Rewriter.  See also @(tsee r1cs-verification-with-axe)."
  :args ((name-of-defconst "The name of the defconst (a symbol) that will be created to hold the DAG.  This name should start and end with @('*').")
         (vars "A form that evaluates to the variables of the R1CS.")
         (constraints "A form that evaluates to the constraints of the R1CS.")
         (prime "A form that evaluates to the prime of the R1CS.")
         (package "The package to use for the variables of the DAG (a string), or @(':auto').  If @('package') is @(':auto'), the variables in the DAG are the same as the variables in the R1CS, except that keywords are changed to the ACL2 package (since keywords are not legal variable names in ACL2).")
         (rules "Either :auto, or a form that evaluates to a list of symbols.  If the latter, the given rules replace the default rules used for lifting.")
         (extra-rules "Rules to be added to the default rule set used for lifting.  A form that evaluates to a list of symbols.  May be non-@('nil') only when @('rules') is @(':auto').")
         (remove-rules "Rules to be removed from the default rule set used for lifting.  A form that evaluates to a list of symbols.  May be non-@('nil') only when @('rules') is @(':auto').")
         (monitor "Rules to monitor during rewriting.  A form that evaluates to a list of symbols")
         (memoizep "Whether to perform memoization during rewriting.  A boolean.  This may actually slow down the lifting process.")
         (count-hitsp "Whether to count rule hits during rewriting (may cause rewriting to be somewhat slower).  A boolean.")
         (print "Axe print argument") ;todo: document
         ))
