; Yul Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "renamings")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ renaming-functions
  :parents (transformations)
  :short "Renaming of functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see disambiguator) for background.")
   (xdoc::p
    "Here we characterize, relationally, the renaming of functions.
     This is analogous to the "
    (xdoc::seetopic "renaming-variables" "renaming of variables")
    ": see the discussion there, which also applies here by analogy."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-renamefun ((old identifierp) (new identifierp) (ren renamingp))
  :returns (_ resulterr-optionp)
  :short "Check if two function names are related by function renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check if the two function names form a pair in the renaming list."))
  (b* ((old (identifier-fix old))
       (new (identifier-fix new)))
    (if (member-equal (cons old new) (renaming->list ren))
        nil
      (err (list :mismatch old new (renaming-fix ren)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines expressions-renamefun
  :short "Mutually recursive ACL2 functions to check if expressions are
          related by function renaming."

  (define expression-renamefun ((old expressionp)
                                (new expressionp)
                                (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two expressions are
            related by function renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "Old and new expressions must be of the same kind,
       and have constituents recursively related.
       Literals and paths must be identical,
       since they reference no functions."))
    (expression-case
     old
     :path (if (expression-equiv old new)
               nil
             (err (list :mismatch
                    (expression-fix old)
                    (expression-fix new))))
     :literal (if (expression-equiv old new)
                  nil
                (err (list :mismatch
                       (expression-fix old)
                       (expression-fix new))))
     :funcall (b* (((unless (expression-case new :funcall))
                    (err (list :mismatch
                           (expression-fix old)
                           (expression-fix new))))
                   ((expression-funcall new) new))
                (funcall-renamefun old.get new.get ren)))
    :measure (expression-count old))

  (define expression-list-renamefun ((old expression-listp)
                                     (new expression-listp)
                                     (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two lists of expressions are
            related by function renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two lists must have the same length,
       and corresponding elements must be related."))
    (b* (((when (endp old))
          (if (endp new)
              nil
            (err (list :mismatch-extra-new (expression-list-fix new)))))
         ((when (endp new))
          (err (list :mismatch-extra-old (expression-list-fix old))))
         ((ok &) (expression-renamefun (car old) (car new) ren)))
      (expression-list-renamefun (cdr old) (cdr new) ren))
    :measure (expression-list-count old))

  (define funcall-renamefun ((old funcallp)
                             (new funcallp)
                             (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two function calls are
            related by function renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "The function names must be related,
       and the arguments must be related."))
    (b* (((funcall old) old)
         ((funcall new) new)
         ((ok &) (fun-renamefun old.name new.name ren)))
      (expression-list-renamefun old.args new.args ren))
    :measure (funcall-count old))

  ///

  (fty::deffixequiv-mutual expressions-renamefun))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expression-option-renamefun ((old expression-optionp)
                                     (new expression-optionp)
                                     (ren renamingp))
  :returns (_ resulterr-optionp)
  :short "Check if two optional expressions are
          related by function renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "Either both expressions must be present or both must be absent.
     If present, they must be related."))
  (expression-option-case
   old
   :none (if (expression-option-case new :none)
             nil
           (err (list :mismatch
                  (expression-option-fix old)
                  (expression-option-fix new))))
   :some (expression-option-case
          new
          :none (err (list :mismatch
                       (expression-option-fix old)
                       (expression-option-fix new)))
          :some (expression-renamefun (expression-option-some->val old)
                                      (expression-option-some->val new)
                                      ren)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funcall-option-renamefun ((old funcall-optionp)
                                  (new funcall-optionp)
                                  (ren renamingp))
  :returns (_ resulterr-optionp)
  :short "Check if two optional function calls are
          related by function renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "Either both function calls must be present or both must be absent.
     If present, they must be related."))
  (funcall-option-case
   old
   :none (if (funcall-option-case new :none)
             nil
           (err (list :mismatch
                  (funcall-option-fix old)
                  (funcall-option-fix new))))
   :some (funcall-option-case
          new
          :none (err (list :mismatch
                       (funcall-option-fix old)
                       (funcall-option-fix new)))
          :some (funcall-renamefun (funcall-option-some->val old)
                                   (funcall-option-some->val new)
                                   ren)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-fun-to-fun-renaming ((old identifierp)
                                 (new identifierp)
                                 (ren renamingp))
  :returns (new-ren renaming-resultp)
  :short "Add a function name to a function renaming list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is quite analogous to @(tsee add-var-to-var-renaming).
     See its documentation."))
  (b* ((old (identifier-fix old))
       (new (identifier-fix new))
       (list (renaming->list ren))
       ((when (member-equal old (strip-cars list)))
        (err (list :old-fun-already-in-scope old new (renaming-fix ren))))
       ((when (member-equal new (strip-cdrs list)))
        (err (list :new-fun-already-in-scope old new (renaming-fix ren)))))
    (renaming (cons (cons old new) list)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-funs-to-fun-renaming ((old identifier-listp)
                                  (new identifier-listp)
                                  (ren renamingp))
  :returns (new-ren renaming-resultp)
  :short "Add the function names in a list to a function renaming list."
  (b* (((when (endp old))
        (if (endp new)
            (renaming-fix ren)
          (err (list :mismatch-extra-new (identifier-list-fix new)))))
       ((when (endp new))
        (err (list :mismatch-extra-old (identifier-list-fix old))))
       ((ok ren) (add-fun-to-fun-renaming (car old) (car new) ren)))
    (add-funs-to-fun-renaming (cdr old) (cdr new) ren))
  :hooks (:fix)
  ///

  (defruled same-len-when-add-funs-to-fun-renaming
    (implies (not (resulterrp (add-funs-to-fun-renaming old new ren)))
             (equal (len new) (len old)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines statements/blocks/cases/fundefs-renamefun
  :short "Mutually recursive ACL2 functions to check if
          statements, blocks, cases, and function definitions are
          related by function renaming."

  (define statement-renamefun ((old statementp)
                               (new statementp)
                               (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two statements are
            related by function renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "In case of success,
       this function returns nothing,
       because we extend the funcion renaming
       only ephemerally, prior to processing blocks or loops.")
     (xdoc::p
      "Old and new statement must be of the same kind,
       and have constituents recursively related.")
     (xdoc::p
      "We treat the initialization blocks of a loop specially,
       as usual (e.g. in the static safety checks and in dynamic execution):
       we extend the renaming list according to
       the function definitions in the initialization block,
       and then we process the rest of the statement
       with the updated renaming list.
       However, the renaming list after the loop is the same as the one before:
       a loop does not permanently introduce new variables."))
    (statement-case
     old
     :block
     (b* (((unless (statement-case new :block))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-block new) new)
          ((ok &) (block-renamefun old.get new.get ren)))
       nil)
     :variable-single
     (b* (((unless (statement-case new :variable-single))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-variable-single new) new)
          ((unless (equal old.name new.name))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((ok &) (expression-option-renamefun old.init new.init ren)))
       nil)
     :variable-multi
     (b* (((unless (statement-case new :variable-multi))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-variable-multi new) new)
          ((unless (equal old.names new.names))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((ok &) (funcall-option-renamefun old.init new.init ren)))
       nil)
     :assign-single
     (b* (((unless (statement-case new :assign-single))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-assign-single new) new)
          ((unless (equal old.target new.target))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((ok &) (expression-renamefun old.value new.value ren)))
       nil)
     :assign-multi
     (b* (((unless (statement-case new :assign-multi))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-assign-multi new) new)
          ((unless (equal old.targets new.targets))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((ok &) (funcall-renamefun old.value new.value ren)))
       nil)
     :funcall
     (b* (((unless (statement-case new :funcall))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-funcall new) new)
          ((ok &) (funcall-renamefun old.get new.get ren)))
       nil)
     :if
     (b* (((unless (statement-case new :if))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-if new) new)
          ((ok &) (expression-renamefun old.test new.test ren))
          ((ok &) (block-renamefun old.body new.body ren)))
       nil)
     :for
     (b* (((unless (statement-case new :for))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-for new) new)
          (old-stmts (block->statements old.init))
          (new-stmts (block->statements new.init))
          (old-funs (fundef-list->name-list (statements-to-fundefs old-stmts)))
          (new-funs (fundef-list->name-list (statements-to-fundefs new-stmts)))
          ((ok ren) (add-funs-to-fun-renaming old-funs new-funs ren))
          ((ok &) (statement-list-renamefun old-stmts new-stmts ren))
          ((ok &) (expression-renamefun old.test new.test ren))
          ((ok &) (block-renamefun old.update new.update ren))
          ((ok &) (block-renamefun old.body new.body ren)))
       nil)
     :switch
     (b* (((unless (statement-case new :switch))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-switch new) new)
          ((ok &) (expression-renamefun old.target new.target ren))
          ((ok &) (swcase-list-renamefun old.cases new.cases ren))
          ((ok &) (block-option-renamefun old.default new.default ren)))
       nil)
     :leave
     (b* (((unless (statement-case new :leave))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new)))))
       nil)
     :break
     (b* (((unless (statement-case new :break))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new)))))
       nil)
     :continue
     (b* (((unless (statement-case new :continue))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new)))))
       nil)
     :fundef
     (b* (((unless (statement-case new :fundef))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-fundef new) new)
          ((ok &) (fundef-renamefun old.get new.get ren)))
       nil))
    :measure (statement-count old))

  (define statement-list-renamefun ((old statement-listp)
                                    (new statement-listp)
                                    (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two lists of statements are
            related by function renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two lists must have the same length
       and have corresponding elements related by the renaming."))
    (b* (((when (endp old))
          (if (endp new)
              nil
            (err (list :mismatch-extra-new (statement-list-fix new)))))
         ((when (endp new))
          (err (list :mismatch-extra-old (statement-list-fix old))))
         ((ok &) (statement-renamefun (car old) (car new) ren)))
      (statement-list-renamefun (cdr old) (cdr new) ren))
    :measure (statement-list-count old))

  (define block-renamefun ((old blockp)
                           (new blockp)
                           (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two blocks are
            related by function renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "First, we extend the function renaming
       according to the functions defined in the two blocks.
       Then we process the list of statements."))
    (b* ((old-stmts (block->statements old))
         (new-stmts (block->statements new))
         (old-fns (fundef-list->name-list (statements-to-fundefs old-stmts)))
         (new-fns (fundef-list->name-list (statements-to-fundefs new-stmts)))
         ((ok ren) (add-funs-to-fun-renaming old-fns new-fns ren))
         ((ok &) (statement-list-renamefun old-stmts new-stmts ren)))
      nil)
    :measure (block-count old))

  (define block-option-renamefun ((old block-optionp)
                                  (new block-optionp)
                                  (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two optional blocks are
            related by function renaming."
    (block-option-case
     old
     :none (if (block-option-case new :none)
               nil
             (err (list :mismatch
                    (block-option-fix old)
                    (block-option-fix new))))
     :some (block-option-case
            new
            :none (err (list :mismatch
                         (block-option-fix old)
                         (block-option-fix new)))
            :some (block-renamefun (block-option-some->val old)
                                   (block-option-some->val new)
                                   ren)))
    :measure (block-option-count old))

  (define swcase-renamefun ((old swcasep)
                            (new swcasep)
                            (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two switch cases are
            related by function renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "The value literals must be identical
       (since they do not contain functions),
       and the bodies must be related."))
    (b* (((unless (equal (swcase->value old)
                         (swcase->value new)))
          (err (list :mismatch-case-value
                (swcase->value old)
                (swcase->value new)))))
      (block-renamefun (swcase->body old) (swcase->body new) ren))
    :measure (swcase-count old))

  (define swcase-list-renamefun ((old swcase-listp)
                                 (new swcase-listp)
                                 (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two lists of switch cases are
            related by function renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two lists must have the same length
       and have corresponding elements related by the renaming."))
    (b* (((when (endp old))
          (if (endp new)
              nil
            (err (list :mismatch-extra-new (swcase-list-fix new)))))
         ((when (endp new))
          (err (list :mismatch-extra-old (swcase-list-fix old))))
         ((ok &) (swcase-renamefun (car old) (car new) ren)))
      (swcase-list-renamefun (cdr old) (cdr new) ren))
    :measure (swcase-list-count old))

  (define fundef-renamefun ((old fundefp)
                            (new fundefp)
                            (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two function definitions are
            related by function renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "When we process two function definitions,
       their association pair has already been added to the function renaming:
       see the treatment of blocks.
       The inputs and outputs must be the same.
       The bodies must be related by function renaming."))
    (b* (((ok &) (fun-renamefun (fundef->name old)
                                (fundef->name new)
                                ren))
         ((unless (equal (fundef->inputs old)
                         (fundef->inputs new)))
          (err (list :mismatch (fundef-fix old) (fundef-fix new))))
         ((unless (equal (fundef->outputs old)
                         (fundef->outputs new)))
          (err (list :mismatch (fundef-fix old) (fundef-fix new)))))
      (block-renamefun (fundef->body old) (fundef->body new) ren))
    :measure (fundef-count old))

  :verify-guards nil ; done below
  ///
  (verify-guards statement-renamefun)

  (fty::deffixequiv-mutual statements/blocks/cases/fundefs-renamefun)

  (defruled same-statement-kind-when-statement-renamefun
    (implies (not (resulterrp (statement-renamefun old new ren)))
             (equal (statement-kind new)
                    (statement-kind old)))
    :expand (statement-renamefun old new ren)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef-list-renamefun ((old fundef-listp)
                               (new fundef-listp)
                               (ren renamingp))
  :returns (_ resulterr-optionp)
  :short "Check if two lists of function definitions are
          related by function renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just a lifting of @(tsee fundef-renamefun) to lists.
     It does not add anything new to the definition of function renaming,
     but it is a useful derived concept.")
   (xdoc::p
    "We prove that if two lists of statements are related by function renaming,
     then the lists of function definitions extracted from the statements
     are also related by function renaming.
     We prove this by simultaneous induction on the two lists of statements."))
  (b* (((when (endp old))
        (if (endp new)
            nil
          (err (list :mismatch-extra-new (fundef-list-fix new)))))
       ((when (endp new))
        (err (list :mismatch-extra-old (fundef-list-fix old))))
       ((ok &) (fundef-renamefun (car old) (car new) ren)))
    (fundef-list-renamefun (cdr old) (cdr new) ren))
  :hooks (:fix)
  ///

  (defrule fundef-list-renamefun-of-statement-to-fundefs
    (implies (not (resulterrp (statement-list-renamefun old new ren)))
             (not (resulterrp
                   (fundef-list-renamefun (statements-to-fundefs old)
                                          (statements-to-fundefs new)
                                          ren))))
    :induct (acl2::cdr-cdr-induct old new)
    :enable (statement-renamefun
             statement-list-renamefun
             statements-to-fundefs
             same-statement-kind-when-statement-renamefun)

    :prep-books ((include-book "std/basic/inductions" :dir :system))))
