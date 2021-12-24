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

(defxdoc+ unique-functions
  :parents (transformations)
  :short "The condition in which all the function namess are distinct."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('Disambiguator') transformation described in
     [Solidity: Internals: The Optimizer: Yul-Based Optimizer Module:
      Preprocessing: Disambiguator],
     makes all the variable and function names globally unique.")
   (xdoc::p
    "Here we capture this uniqueness property for functions;
     the uniqueness property for variables
     is captured in @(see unique-variables).
     We formalize this property via ACL2 functions on statements, blocks, etc.
     that take as arguments the function names encountered so far,
     check that the names of the functions
     introduced by the statement (or block etc.)
     are not among those,
     and update the set of encountered function names
     with the names of the introduced functions.
     Thus, the set of function names encountered so far is threaded through.
     We do no need to define any ACL2 functions on expressions,
     in order to capture this property,
     because expressions do not introduce new functions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines statements/blocks/cases/fundefs-unique-funs
  :short "Mutually recursive functions that check
          the uniqueness of function names in
          statements, blocks, cases, and function definitions."

  (define statement-unique-funs ((stmt statementp) (funs identifier-setp))
    :returns (new-funs identifier-set-resultp)
    :short "Check that a statement has unique function names."
    (statement-case
     stmt
     :block (block-unique-funs stmt.get funs)
     :variable-single (identifier-set-fix funs)
     :variable-multi (identifier-set-fix funs)
     :assign-single (identifier-set-fix funs)
     :assign-multi (identifier-set-fix funs)
     :funcall (identifier-set-fix funs)
     :if (block-unique-funs stmt.body funs)
     :for (b* (((ok funs) (block-unique-funs stmt.init funs))
               ((ok funs) (block-unique-funs stmt.update funs))
               ((ok funs) (block-unique-funs stmt.body funs)))
            funs)
     :switch (b* (((ok funs) (swcase-list-unique-funs stmt.cases funs))
                  ((ok funs) (block-option-unique-funs stmt.default funs)))
               funs)
     :leave (identifier-set-fix funs)
     :break (identifier-set-fix funs)
     :continue (identifier-set-fix funs)
     :fundef (fundef-unique-funs stmt.get funs))
    :measure (statement-count stmt))

  (define statement-list-unique-funs ((stmts statement-listp)
                                      (funs identifier-setp))
    :returns (new-funs identifier-set-resultp)
    :short "Check that a list of statements has unique function names."
    (b* (((when (endp stmts)) (identifier-set-fix funs))
         ((ok funs) (statement-unique-funs (car stmts) funs))
         ((ok funs) (statement-list-unique-funs (cdr stmts) funs)))
      funs)
    :measure (statement-list-count stmts))

  (define block-unique-funs ((block blockp) (funs identifier-setp))
    :returns (new-funs identifier-set-resultp)
    :short "Check that a block has unique function names."
    (statement-list-unique-funs (block->statements block) funs)
    :measure (block-count block))

  (define block-option-unique-funs ((block? block-optionp)
                                    (funs identifier-setp))
    :returns (new-funs identifier-set-resultp)
    :short "Check that an optional block has unique function names."
    (block-option-case block?
                       :some (block-unique-funs (block-option-some->val block?)
                                                funs)
                       :none (identifier-set-fix funs))
    :measure (block-option-count block?))

  (define swcase-unique-funs ((case swcasep) (funs identifier-setp))
    :returns (new-funs identifier-set-resultp)
    :short "Check that a switch case has unique function names."
    (block-unique-funs (swcase->body case) funs)
    :measure (swcase-count case))

  (define swcase-list-unique-funs ((cases swcase-listp) (funs identifier-setp))
    :returns (new-funs identifier-set-resultp)
    :short "Check that a list of switch cases has unique function names."
    (b* (((when (endp cases)) (identifier-set-fix funs))
         ((ok funs) (swcase-unique-funs (car cases) funs))
         ((ok funs) (swcase-list-unique-funs (cdr cases) funs)))
      funs)
    :measure (swcase-list-count cases))

  (define fundef-unique-funs ((fundef fundefp) (funs identifier-setp))
    :returns (new-funs identifier-set-resultp)
    :short "Check that a function definition has unique function names."
    (b* ((name (fundef->name fundef))
         ((when (set::in name (identifier-set-fix funs)))
          (err (list :duplicate-funs name)))
         (funs (set::insert name (identifier-set-fix funs))))
      (block-unique-funs (fundef->body fundef) funs))
    :measure (fundef-count fundef))

  :flag-local nil

  :verify-guards nil ; done below
  ///
  (verify-guards statement-unique-funs)

  (fty::deffixequiv-mutual statements/blocks/cases/fundefs-unique-funs))
