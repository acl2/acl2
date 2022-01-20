; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "../language/abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unique-variables
  :parents (transformations)
  :short "The condition in which all the variable names are distinct."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('Disambiguator') transformation described in
     [Solidity: Internals: The Optimizer: Yul-Based Optimizer Module:
      Preprocessing: Disambiguator],
     makes all the variable and function names globally unique.")
   (xdoc::p
    "Here we capture this uniqueness property for variables;
     the uniqueness property for functions
     is captured in @(see unique-functions).
     We formalize this property via ACL2 functions on statements, blocks, etc.
     that take as arguments the variable names encountered so far,
     check that the names of the variables
     introduced by the statement (or block etc.)
     are not among those,
     and update the set of encountered variable names
     with the names of the introduced variables.
     Thus, the set of variable names encountered so far is threaded through.
     We do not need to define any ACL2 functions on expressions,
     in order to capture this property,
     because expressions do not introduce new variables."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-unique-vars ((var identifierp) (allvars identifier-setp))
  :returns (new-allvars identifier-set-resultp)
  :short "Check that a variable is unique."
  :long
  (xdoc::topstring
   (xdoc::p
    "Check that it does not occur in the set of all variables found so far,
     and add it to that set if successful.")
   (xdoc::p
    "This is very similar to @(tsee add-var),
     but it has a different purpose."))
  (if (set::in (identifier-fix var) (identifier-set-fix allvars))
      (err (list :non-unique-var (identifier-fix var)))
    (set::insert (identifier-fix var) (identifier-set-fix allvars)))
  :hooks (:fix)
  ///

  (defruled var-unique-vars-to-set-insert
    (b* ((allvars1 (var-unique-vars var allvars)))
      (implies (not (resulterrp allvars1))
               (equal allvars1
                      (set::insert (identifier-fix var)
                                   (identifier-set-fix allvars)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-list-unique-vars ((vars identifier-listp) (allvars identifier-setp))
  :returns (new-allvars identifier-set-resultp)
  :short "Check that all the variables in a list are unique."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee var-unique-vars) to lists.")
   (xdoc::p
    "This is very similar to @(tsee add-vars),
     but it has a different purpose."))
  (b* (((when (endp vars)) (identifier-set-fix allvars))
       ((ok allvars) (var-unique-vars (car vars) allvars)))
    (var-list-unique-vars (cdr vars) allvars))
  :hooks (:fix)
  ///

  (defruled var-list-unique-vars-to-set-list-insert
    (b* ((allvars1 (var-list-unique-vars vars allvars)))
      (implies (not (resulterrp allvars1))
               (equal allvars1
                      (set::list-insert (identifier-list-fix vars)
                                        (identifier-set-fix allvars)))))
    :enable (set::list-insert
             var-unique-vars-to-set-insert)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines statements/blocks/cases/fundefs-unique-vars
  :short "Mutually recursive functions that check
          the uniqueness of variable names in
          statements, blocks, cases, and function definitions."

  (define statement-unique-vars ((stmt statementp) (allvars identifier-setp))
    :returns (new-allvars identifier-set-resultp)
    :short "Check that a statement has unique variable names."
    (statement-case
     stmt
     :block (block-unique-vars stmt.get allvars)
     :variable-single (var-unique-vars stmt.name allvars)
     :variable-multi (var-list-unique-vars stmt.names allvars)
     :assign-single (identifier-set-fix allvars)
     :assign-multi (identifier-set-fix allvars)
     :funcall (identifier-set-fix allvars)
     :if (block-unique-vars stmt.body allvars)
     :for (b* (((ok allvars) (block-unique-vars stmt.init allvars))
               ((ok allvars) (block-unique-vars stmt.update allvars))
               ((ok allvars) (block-unique-vars stmt.body allvars)))
            allvars)
     :switch (b* (((ok allvars) (swcase-list-unique-vars stmt.cases allvars))
                  ((ok allvars) (block-option-unique-vars stmt.default allvars)))
               allvars)
     :leave (identifier-set-fix allvars)
     :break (identifier-set-fix allvars)
     :continue (identifier-set-fix allvars)
     :fundef (fundef-unique-vars stmt.get allvars))
    :measure (statement-count stmt))

  (define statement-list-unique-vars ((stmts statement-listp)
                                      (allvars identifier-setp))
    :returns (new-allvars identifier-set-resultp)
    :short "Check that a list of statements has unique variable names."
    (b* (((when (endp stmts)) (identifier-set-fix allvars))
         ((ok allvars) (statement-unique-vars (car stmts) allvars))
         ((ok allvars) (statement-list-unique-vars (cdr stmts) allvars)))
      allvars)
    :measure (statement-list-count stmts))

  (define block-unique-vars ((block blockp) (allvars identifier-setp))
    :returns (new-allvars identifier-set-resultp)
    :short "Check that a block has unique variable names."
    (statement-list-unique-vars (block->statements block) allvars)
    :measure (block-count block))

  (define block-option-unique-vars ((block? block-optionp)
                                    (allvars identifier-setp))
    :returns (new-allvars identifier-set-resultp)
    :short "Check that an optional block has unique variable names."
    (block-option-case block?
                       :some (block-unique-vars (block-option-some->val block?)
                                                allvars)
                       :none (identifier-set-fix allvars))
    :measure (block-option-count block?))

  (define swcase-unique-vars ((case swcasep) (allvars identifier-setp))
    :returns (new-allvars identifier-set-resultp)
    :short "Check that a switch case has unique variable names."
    (block-unique-vars (swcase->body case) allvars)
    :measure (swcase-count case))

  (define swcase-list-unique-vars ((cases swcase-listp) (allvars identifier-setp))
    :returns (new-allvars identifier-set-resultp)
    :short "Check that a list of switch cases has unique variable names."
    (b* (((when (endp cases)) (identifier-set-fix allvars))
         ((ok allvars) (swcase-unique-vars (car cases) allvars))
         ((ok allvars) (swcase-list-unique-vars (cdr cases) allvars)))
      allvars)
    :measure (swcase-list-count cases))

  (define fundef-unique-vars ((fundef fundefp) (allvars identifier-setp))
    :returns (new-allvars identifier-set-resultp)
    :short "Check that a function definition has unique variable names."
    (b* (((fundef fundef) fundef)
         ((ok allvars) (var-list-unique-vars (append fundef.inputs
                                                     fundef.outputs)
                                             allvars)))
      (block-unique-vars fundef.body allvars))
    :measure (fundef-count fundef))

  :flag-local nil

  :verify-guards nil ; done below
  ///
  (verify-guards statement-unique-vars)

  (fty::deffixequiv-mutual statements/blocks/cases/fundefs-unique-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection statements/blocks/cases/fundefs-unique-vars-extend
  :short "The @('...-unique-vars') functions extend the set of variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if they return a new set of variables (i.e. not an error),
     the new set is a superset of (or equal to) the initial set."))

  (defthm-statements/blocks/cases/fundefs-unique-vars-flag

    (defthm statement-unique-vars-extend
      (implies (identifier-setp allvars)
               (b* ((allvars1 (statement-unique-vars stmt allvars)))
                 (implies (not (resulterrp allvars1))
                          (set::subset allvars allvars1))))
      :flag statement-unique-vars)

    (defthm statement-list-unique-vars-extend
      (implies (identifier-setp allvars)
               (b* ((allvars1 (statement-list-unique-vars stmts allvars)))
                 (implies (not (resulterrp allvars1))
                          (set::subset allvars allvars1))))
      :flag statement-list-unique-vars)

    (defthm block-unique-vars-extend
      (implies (identifier-setp allvars)
               (b* ((allvars1 (block-unique-vars block allvars)))
                 (implies (not (resulterrp allvars1))
                          (set::subset allvars allvars1))))
      :flag block-unique-vars)

    (defthm block-option-unique-vars-extend
      (implies (identifier-setp allvars)
               (b* ((allvars1 (block-option-unique-vars block? allvars)))
                 (implies (not (resulterrp allvars1))
                          (set::subset allvars allvars1))))
      :flag block-option-unique-vars)

    (defthm swcase-unique-vars-extend
      (implies (identifier-setp allvars)
               (b* ((allvars1 (swcase-unique-vars case allvars)))
                 (implies (not (resulterrp allvars1))
                          (set::subset allvars allvars1))))
      :flag swcase-unique-vars)

    (defthm swcase-list-unique-vars-extend
      (implies (identifier-setp allvars)
               (b* ((allvars1 (swcase-list-unique-vars cases allvars)))
                 (implies (not (resulterrp allvars1))
                          (set::subset allvars allvars1))))
      :flag swcase-list-unique-vars)

    (defthm fundef-unique-vars-extend
      (implies (identifier-setp allvars)
               (b* ((allvars1 (fundef-unique-vars fundef allvars)))
                 (implies (not (resulterrp allvars1))
                          (set::subset allvars allvars1))))
      :flag fundef-unique-vars)

    :hints (("Goal"
             :in-theory (e/d (statement-unique-vars
                              statement-list-unique-vars
                              block-unique-vars
                              block-option-unique-vars
                              swcase-unique-vars
                              swcase-list-unique-vars
                              fundef-unique-vars
                              set::subset-transitive
                              var-unique-vars-to-set-insert
                              var-list-unique-vars-to-set-list-insert
                              (:forward-chaining set::subset-of-list-insert))
                             ((:rewrite set::subset-of-list-insert)))))))
