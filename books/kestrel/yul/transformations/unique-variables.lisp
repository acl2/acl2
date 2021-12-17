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
  :short "The condition in which all the variable namess are distinct."
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
     is captured elsewhere.
     We formalize this property via ACL2 functions on statements, blocks, etc.
     that take as arguments the variable names encountered so far,
     check that the names of the variables
     introduced by the statement (or block etc.)
     are not among those,
     and update the set of encountered variable names
     with the names of the introduced variables.
     Thus, the set of variable names encountered so far is threaded through.
     We do no need to define any ACL2 functions on expressions,
     in order to capture this property,
     because expressions do not introduce new variables."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines statements/blocks/cases/fundefs-unique-vars
  :short "Mutually recursive functions that check
          the uniqueness of variable names in
          statements, blocks, cases, and function definitions."

  (define statement-unique-vars ((stmt statementp) (vars identifier-setp))
    :returns (new-vars identifier-set-resultp)
    :short "Check that a statement has unique variable names."
    (statement-case
     stmt
     :block (block-unique-vars stmt.get vars)
     :variable-single (if (not (set::in stmt.name (identifier-set-fix vars)))
                          (set::insert stmt.name (identifier-set-fix vars))
                        (err (list :duplicate-var stmt.name)))
     :variable-multi (if (set::list-notin stmt.names (identifier-set-fix vars))
                         (set::list-insert stmt.names (identifier-set-fix vars))
                       (err (list :duplicate-vars stmt.names)))
     :assign-single (identifier-set-fix vars)
     :assign-multi (identifier-set-fix vars)
     :funcall (identifier-set-fix vars)
     :if (block-unique-vars stmt.body vars)
     :for (b* (((ok vars) (block-unique-vars stmt.init vars))
               ((ok vars) (block-unique-vars stmt.update vars))
               ((ok vars) (block-unique-vars stmt.body vars)))
            vars)
     :switch (b* (((ok vars) (swcase-list-unique-vars stmt.cases vars))
                  ((ok vars) (block-option-unique-vars stmt.default vars)))
               vars)
     :leave (identifier-set-fix vars)
     :break (identifier-set-fix vars)
     :continue (identifier-set-fix vars)
     :fundef (fundef-unique-vars stmt.get vars))
    :measure (statement-count stmt))

  (define statement-list-unique-vars ((stmts statement-listp)
                                      (vars identifier-setp))
    :returns (new-vars identifier-set-resultp)
    :short "Check that a list of statements has unique variable names."
    (b* (((when (endp stmts)) (identifier-set-fix vars))
         ((ok vars) (statement-unique-vars (car stmts) vars))
         ((ok vars) (statement-list-unique-vars (cdr stmts) vars)))
      vars)
    :measure (statement-list-count stmts))

  (define block-unique-vars ((block blockp) (vars identifier-setp))
    :returns (new-vars identifier-set-resultp)
    :short "Check that a block has unique variable names."
    (statement-list-unique-vars (block->statements block) vars)
    :measure (block-count block))

  (define block-option-unique-vars ((block? block-optionp)
                                    (vars identifier-setp))
    :returns (new-vars identifier-set-resultp)
    :short "Check that an optional block has unique variable names."
    (block-option-case block?
                       :some (block-unique-vars (block-option-some->val block?)
                                                vars)
                       :none (identifier-set-fix vars))
    :measure (block-option-count block?))

  (define swcase-unique-vars ((case swcasep) (vars identifier-setp))
    :returns (new-vars identifier-set-resultp)
    :short "Check that a switch case has unique variable names."
    (block-unique-vars (swcase->body case) vars)
    :measure (swcase-count case))

  (define swcase-list-unique-vars ((cases swcase-listp) (vars identifier-setp))
    :returns (new-vars identifier-set-resultp)
    :short "Check that a list of switch cases has unique variable names."
    (b* (((when (endp cases)) (identifier-set-fix vars))
         ((ok vars) (swcase-unique-vars (car cases) vars))
         ((ok vars) (swcase-list-unique-vars (cdr cases) vars)))
      vars)
    :measure (swcase-list-count cases))

  (define fundef-unique-vars ((fundef fundefp) (vars identifier-setp))
    :returns (new-vars identifier-set-resultp)
    :short "Check that a function definition has unique variable names."
    (b* (((fundef fundef) fundef)
         ((unless (set::list-notin fundef.inputs (identifier-set-fix vars)))
          (err (list :duplicate-vars fundef.inputs)))
         (vars (set::list-insert fundef.inputs (identifier-set-fix vars)))
         ((unless (set::list-notin fundef.outputs (identifier-set-fix vars)))
          (err (list :duplicate-vars fundef.outputs)))
         (vars (set::list-insert fundef.outputs (identifier-set-fix vars))))
      (block-unique-vars fundef.body vars))
    :measure (fundef-count fundef))

  :flag-local nil

  :verify-guards nil ; done below
  ///
  (verify-guards statement-unique-vars)

  (fty::deffixequiv-mutual statements/blocks/cases/fundefs-unique-vars))
