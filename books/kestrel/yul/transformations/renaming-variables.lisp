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

(defxdoc+ renaming-variables
  :parents (transformations)
  :short "Renaming of variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see disambiguator) for background.")
   (xdoc::p
    "Here we characterize, relationally, the renaming of variables.
     The predicate mentioned in @(see disambiguator),
     i.e. the one that relates original and transformed code,
     is actually a function that returns success or failure.
     More precisely, as with other aspects of Yul,
     it is a family of functions,
     with a member for each kind of Yul syntactic entity
     (expression, statement, etc.);
     however, for simplicity below we refer to this family as just a function.")
   (xdoc::p
    "This function cannot just operate on old and new code,
     intended as pieces of abstract syntax like expressions and statements.
     Since the code may reference variables
     defined outside the code being operated upon,
     we need, as additional arguments,
     information about how the variables in scope
     are renamed in the code being operated upon.
     This information is calculated
     by operating on the enclosing code,
     prior to recursively operating on the enclosed code.
     Thus, in case of success, in general this function returns
     updated renaming information."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-renamevar ((old identifierp) (new identifierp) (ren renamingp))
  :returns (_ resulterr-optionp)
  :short "Check if two variables are related by variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check if the two variables form a pair in the renaming list."))
  (b* ((old (identifier-fix old))
       (new (identifier-fix new)))
    (if (member-equal (cons old new) (renaming->list ren))
        nil
      (err (list :mismatch old new (renaming-fix ren)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-list-renamevar ((old identifier-listp)
                            (new identifier-listp)
                            (ren renamingp))
  :returns (_ resulterr-optionp)
  :short "Check if two lists of variables are related by variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists must have the same length,
     and corresponding elements must be related."))
  (b* (((when (endp old))
        (if (endp new)
            nil
          (err (list :mismatch-extra-new (identifier-list-fix new)))))
       ((when (endp new))
        (err (list :mismatch-extra-old (identifier-list-fix old))))
       ((ok &) (var-renamevar (car old) (car new) ren)))
    (var-list-renamevar (cdr old) (cdr new) ren))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define path-renamevar ((old pathp) (new pathp) (ren renamingp))
  :returns (_ resulterr-optionp)
  :short "Check if two paths are related by variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two paths must be both singletons,
     whose identifiers must be related."))
  (b* ((old-ids (path->get old))
       ((unless (and (consp old-ids)
                     (endp (cdr old-ids))))
        (err (list :non-singleton-old-path (path-fix old))))
       (old-id (car old-ids))
       (new-ids (path->get new))
       ((unless (and (consp new-ids)
                     (endp (cdr new-ids))))
        (err (list :non-singleton-old-path (path-fix new))))
       (new-id (car new-ids)))
    (var-renamevar old-id new-id ren))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define path-list-renamevar ((old path-listp) (new path-listp) (ren renamingp))
  :returns (_ resulterr-optionp)
  :short "Check if two lists of paths are
          related by variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists must have the same length,
     and corresponding elements must be related."))
  (b* (((when (endp old))
        (if (endp new)
            nil
          (err (list :mismatch-extra-new (path-list-fix new)))))
       ((when (endp new))
        (err (list :mismatch-extra-old (path-list-fix old))))
       ((ok &) (path-renamevar (car old) (car new) ren)))
    (path-list-renamevar (cdr old) (cdr new) ren))
  :hooks (:fix)
  ///

  (defruled same-len-when-path-list-renamevar
    (implies (not (resulterrp (path-list-renamevar old new ren)))
             (equal (len new) (len old)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines expressions-renamevar
  :short "Mutually recursive ACL2 functions to check if expressions are
          related by variable renaming."

  (define expression-renamevar ((old expressionp)
                                (new expressionp)
                                (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two expressions are
            related by variable renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "Old and new expressions must be of the same kind,
       and have constituents recursively related.
       Literals must be identical, since they have no variables."))
    (expression-case
     old
     :path (b* (((unless (expression-case new :path))
                 (err (list :mismatch
                        (expression-fix old)
                        (expression-fix new))))
                ((expression-path new) new))
             (path-renamevar old.get new.get ren))
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
                (funcall-renamevar old.get new.get ren)))
    :measure (expression-count old))

  (define expression-list-renamevar ((old expression-listp)
                                     (new expression-listp)
                                     (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two lists of expressions are
            related by variable renaming."
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
         ((ok &) (expression-renamevar (car old) (car new) ren)))
      (expression-list-renamevar (cdr old) (cdr new) ren))
    :measure (expression-list-count old))

  (define funcall-renamevar ((old funcallp)
                             (new funcallp)
                             (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two function calls are
            related by variable renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "The function names must be identical,
       and the arguments must be related."))
    (b* (((funcall old) old)
         ((funcall new) new)
         ((unless (equal old.name new.name))
          (err (list :mismatch (funcall-fix old) (funcall-fix new)))))
      (expression-list-renamevar old.args new.args ren))
    :measure (funcall-count old))

  :flag-local nil

  ///

  (fty::deffixequiv-mutual expressions-renamevar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expression-option-renamevar ((old expression-optionp)
                                     (new expression-optionp)
                                     (ren renamingp))
  :returns (_ resulterr-optionp)
  :short "Check if two optional expressions are
          related by variable renaming."
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
          :some (expression-renamevar (expression-option-some->val old)
                                      (expression-option-some->val new)
                                      ren)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funcall-option-renamevar ((old funcall-optionp)
                                  (new funcall-optionp)
                                  (ren renamingp))
  :returns (_ resulterr-optionp)
  :short "Check if two optional function calls are
          related by variable renaming."
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
          :some (funcall-renamevar (funcall-option-some->val old)
                                   (funcall-option-some->val new)
                                   ren)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-var-to-var-renaming ((old identifierp)
                                 (new identifierp)
                                 (ren renamingp))
  :returns (new-ren renaming-resultp)
  :short "Add a variable to a variable renaming list."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that the old variable is not already a key in the alist,
     and that the new variable is not already a value in the alist.
     This is always the case when processing statically safe code,
     because variables are addded to the renaming list as they get in scope,
     and the static safety checks ensure that
     only variables not in scope are added to the scope.
     In fact, by checking this,
     we are checking that the code does not shadow variables."))
  (b* ((old (identifier-fix old))
       (new (identifier-fix new))
       (list (renaming->list ren))
       ((when (member-equal old (strip-cars list)))
        (err (list :old-var-already-in-scope old new (renaming-fix ren))))
       ((when (member-equal new (strip-cdrs list)))
        (err (list :new-var-already-in-scope old new (renaming-fix ren)))))
    (renaming (cons (cons old new) list)))
  :hooks (:fix)
  ///

  (defrule subsetp-equal-of-add-var-to-var-renaming
    (b* ((ren1 (add-var-to-var-renaming old new ren)))
      (implies (not (resulterrp ren1))
               (subsetp-equal (renaming->list ren)
                              (renaming->list ren1)))))

  (defruled renaming-old/new-of-add-var-to-var-renaming
    (implies (and (identifierp old-var)
                  (identifierp new-var))
             (b* ((ren1 (add-var-to-var-renaming old-var new-var ren)))
               (implies (not (resulterrp ren1))
                        (and (equal (renaming-old ren1)
                                    (set::insert old-var (renaming-old ren)))
                             (equal (renaming-new ren1)
                                    (set::insert new-var (renaming-new ren)))))))
    :enable (renaming-old
             renaming-new
             mergesort))

  (defruled var-renamevar-when-add-var-to-var-renaming
    (b* ((ren1 (add-var-to-var-renaming old new ren)))
      (implies (not (resulterrp ren1))
               (not (resulterrp (var-renamevar old new ren1)))))
    :enable var-renamevar)

  (defruled var-renamevar-of-add-var-to-var-renaming-when-var-renamevar
    (b* ((ren1 (add-var-to-var-renaming old1 new1 ren)))
      (implies (and (not (resulterrp ren1))
                    (not (resulterrp (var-renamevar old new ren))))
               (not (resulterrp (var-renamevar old new ren1)))))
    :enable var-renamevar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-vars-to-var-renaming ((old identifier-listp)
                                  (new identifier-listp)
                                  (ren renamingp))
  :returns (new-ren renaming-resultp)
  :short "Add the variables in a list to a variable renaming list."
  (b* (((when (endp old))
        (if (endp new)
            (renaming-fix ren)
          (err (list :mismatch-extra-new (identifier-list-fix new)))))
       ((when (endp new))
        (err (list :mismatch-extra-old (identifier-list-fix old))))
       ((ok ren) (add-var-to-var-renaming (car old) (car new) ren)))
    (add-vars-to-var-renaming (cdr old) (cdr new) ren))
  :hooks (:fix)
  ///

  (defruled same-len-when-add-vars-to-var-renaming
    (implies (not (resulterrp (add-vars-to-var-renaming old new ren)))
             (equal (len new) (len old))))

  (defrule subsetp-equal-of-add-vars-to-var-renaming
    (b* ((ren1 (add-vars-to-var-renaming old new ren)))
      (implies (not (resulterrp ren1))
               (subsetp-equal (renaming->list ren)
                              (renaming->list ren1)))))

  (defruled var-renamevar-of-add-vars-to-var-renaming-when-var-renamevar
    (b* ((ren1 (add-vars-to-var-renaming old1 new1 ren)))
      (implies (and (not (resulterrp ren1))
                    (not (resulterrp (var-renamevar old new ren))))
               (not (resulterrp (var-renamevar old new ren1)))))
    :enable var-renamevar-of-add-var-to-var-renaming-when-var-renamevar)

  (defruled var-list-renamevar-when-add-vars-to-var-renaming
    (b* ((ren1 (add-vars-to-var-renaming old new ren)))
      (implies (not (resulterrp ren1))
               (not (resulterrp (var-list-renamevar old new ren1)))))
    :enable (var-list-renamevar
             var-renamevar-of-add-vars-to-var-renaming-when-var-renamevar
             var-renamevar-when-add-var-to-var-renaming)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines statements/blocks/cases/fundefs-renamevar
  :short "Mutually recursive ACL2 functions to check if
          statements, blocks, cases, and function definitions are
          related by variable renaming."

  (define statement-renamevar ((old statementp)
                               (new statementp)
                               (ren renamingp))
    :returns (new-ren renaming-resultp)
    :short "Check if two statements are
            related by variable renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "In case of success,
       this function returns a renaming list
       updated according to the variables introduced in the statement.")
     (xdoc::p
      "Old and new statement must be of the same kind,
       and have constituents recursively related.")
     (xdoc::p
      "Variable declarations extend the renaming list
       with additional associations.
       All the other kinds of statements
       leave the renaming list unchanged.")
     (xdoc::p
      "We treat the initialization blocks of a loop specially,
       as usual (e.g. in the static safety checks and in dynamic execution):
       we extend the renaming list according to
       the statements in the initialization block,
       and then we process the rest of the statement
       with the updated renaming list.
       However, the renaming list after the loop is the same as the one before:
       a loop does not permanently introduce new variables.")
     (xdoc::p
      "The ACL2 function to check function definitions
       does not take a renaming list as argument,
       because a function definition has a fresh variable scope."))
    (statement-case
     old
     :block
     (b* (((unless (statement-case new :block))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-block new) new)
          ((ok &) (block-renamevar old.get new.get ren)))
       (renaming-fix ren))
     :variable-single
     (b* (((unless (statement-case new :variable-single))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-variable-single new) new)
          ((ok &) (expression-option-renamevar old.init new.init ren)))
       (add-var-to-var-renaming old.name new.name ren))
     :variable-multi
     (b* (((unless (statement-case new :variable-multi))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-variable-multi new) new)
          ((ok &) (funcall-option-renamevar old.init new.init ren)))
       (add-vars-to-var-renaming old.names new.names ren))
     :assign-single
     (b* (((unless (statement-case new :assign-single))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-assign-single new) new)
          ((ok &) (path-renamevar old.target new.target ren))
          ((ok &) (expression-renamevar old.value new.value ren)))
       (renaming-fix ren))
     :assign-multi
     (b* (((unless (statement-case new :assign-multi))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-assign-multi new) new)
          ((ok &) (path-list-renamevar old.targets new.targets ren))
          ((ok &) (funcall-renamevar old.value new.value ren)))
       (renaming-fix ren))
     :funcall
     (b* (((unless (statement-case new :funcall))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-funcall new) new)
          ((ok &) (funcall-renamevar old.get new.get ren)))
       (renaming-fix ren))
     :if
     (b* (((unless (statement-case new :if))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-if new) new)
          ((ok &) (expression-renamevar old.test new.test ren))
          ((ok &) (block-renamevar old.body new.body ren)))
       (renaming-fix ren))
     :for
     (b* (((unless (statement-case new :for))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-for new) new)
          (old-stmts (block->statements old.init))
          (new-stmts (block->statements new.init))
          ((ok ren1) (statement-list-renamevar old-stmts new-stmts ren))
          ((ok &) (expression-renamevar old.test new.test ren1))
          ((ok &) (block-renamevar old.update new.update ren1))
          ((ok &) (block-renamevar old.body new.body ren1)))
       (renaming-fix ren))
     :switch
     (b* (((unless (statement-case new :switch))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-switch new) new)
          ((ok &) (expression-renamevar old.target new.target ren))
          ((ok &) (swcase-list-renamevar old.cases new.cases ren))
          ((ok &) (block-option-renamevar old.default new.default ren)))
       (renaming-fix ren))
     :leave
     (b* (((unless (statement-case new :leave))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new)))))
       (renaming-fix ren))
     :break
     (b* (((unless (statement-case new :break))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new)))))
       (renaming-fix ren))
     :continue
     (b* (((unless (statement-case new :continue))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new)))))
       (renaming-fix ren))
     :fundef
     (b* (((unless (statement-case new :fundef))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-fundef new) new)
          ((ok &) (fundef-renamevar old.get new.get)))
       (renaming-fix ren)))
    :measure (statement-count old))

  (define statement-list-renamevar ((old statement-listp)
                                    (new statement-listp)
                                    (ren renamingp))
    :returns (new-ren renaming-resultp)
    :short "Check if two lists of statements are
            related by variable renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two lists must have the same length,
       and have corresponding elements related by the renaming.
       The renaming list is updated and threaded through the statements."))
    (b* (((when (endp old))
          (if (endp new)
              (renaming-fix ren)
            (err (list :mismatch-extra-new (statement-list-fix new)))))
         ((when (endp new))
          (err (list :mismatch-extra-old (statement-list-fix old))))
         ((ok ren) (statement-renamevar (car old) (car new) ren)))
      (statement-list-renamevar (cdr old) (cdr new) ren))
    :measure (statement-list-count old))

  (define block-renamevar ((old blockp)
                           (new blockp)
                           (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two blocks are
            related by variable renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "We process the list of statements,
       discarding the final renaming list,
       because the scope of a block ends at the end of the block."))
    (b* ((old-stmts (block->statements old))
         (new-stmts (block->statements new))
         ((ok &) (statement-list-renamevar old-stmts new-stmts ren)))
      nil)
    :measure (block-count old))

  (define block-option-renamevar ((old block-optionp)
                                  (new block-optionp)
                                  (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two optional blocks are
            related by variable renaming."
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
            :some (block-renamevar (block-option-some->val old)
                                   (block-option-some->val new)
                                   ren)))
    :measure (block-option-count old))

  (define swcase-renamevar ((old swcasep)
                            (new swcasep)
                            (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two switch cases are
            related by variable renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "The value literals must be identical
       (since they do not contain variables),
       and the bodies must be related."))
    (b* (((unless (equal (swcase->value old)
                         (swcase->value new)))
          (err (list :mismatch-case-value
                 (swcase->value old)
                 (swcase->value new)))))
      (block-renamevar (swcase->body old) (swcase->body new) ren))
    :measure (swcase-count old))

  (define swcase-list-renamevar ((old swcase-listp)
                                 (new swcase-listp)
                                 (ren renamingp))
    :returns (_ resulterr-optionp)
    :short "Check if two lists of switch cases are
            related by variable renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two lists must have the same length,
       and have corresponding elements related by the renaming."))
    (b* (((when (endp old))
          (if (endp new)
              nil
            (err (list :mismatch-extra-new (swcase-list-fix new)))))
         ((when (endp new))
          (err (list :mismatch-extra-old (swcase-list-fix old))))
         ((ok &) (swcase-renamevar (car old) (car new) ren)))
      (swcase-list-renamevar (cdr old) (cdr new) ren))
    :measure (swcase-list-count old))

  (define fundef-renamevar ((old fundefp) (new fundefp))
    :returns (_ resulterr-optionp)
    :short "Check if two function definitions are
            related by variable renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "We initialize the renaming list according to the inputs and outputs,
       and then we process the bodies."))
    (b* (((unless (equal (fundef->name old)
                         (fundef->name new)))
          (err (list :mismatch-function-name
                 (fundef->name old)
                 (fundef->name new))))
         ((ok ren) (add-vars-to-var-renaming (fundef->inputs old)
                                             (fundef->inputs new)
                                             (renaming nil)))
         ((ok ren) (add-vars-to-var-renaming (fundef->outputs old)
                                             (fundef->outputs new)
                                             ren)))
      (block-renamevar (fundef->body old) (fundef->body new) ren))
    :measure (fundef-count old))

  :flag-local nil

  :verify-guards nil ; done below
  ///
  (verify-guards statement-renamevar)

  (fty::deffixequiv-mutual statements/blocks/cases/fundefs-renamevar)

  (local (include-book "std/basic/inductions" :dir :system))

  (defruled same-len-when-expression-list-renamevar
    (implies (not (resulterrp (expression-list-renamevar old new ren)))
             (equal (len old) (len new)))
    :enable expression-list-renamevar
    :induct (acl2::cdr-cdr-induct old new))

  (defruled expression-list-renamevar-of-append-error
    (implies (equal (len old) (len new))
             (equal (resulterrp (expression-list-renamevar (append old old1)
                                                           (append new new1)
                                                           ren))
                    (or (resulterrp (expression-list-renamevar old new ren))
                        (resulterrp (expression-list-renamevar old1 new1 ren)))))
    :enable expression-list-renamevar
    :induct (acl2::cdr-cdr-induct old new))

  (defruled expression-list-renamevar-of-rev-error
    (implies (equal (len old) (len new))
             (equal (resulterrp (expression-list-renamevar (rev old)
                                                           (rev new)
                                                           ren))
                    (resulterrp (expression-list-renamevar old new ren))))
    :induct (acl2::cdr-cdr-induct old new)
    :enable (rev
             expression-list-renamevar
             expression-list-renamevar-of-append-error))

  (defruled expression-list-renamevar-of-rev-not-error
    (implies (not (resulterrp (expression-list-renamevar old new ren)))
             (not (resulterrp (expression-list-renamevar (rev old)
                                                         (rev new)
                                                         ren))))
    :enable (expression-list-renamevar-of-rev-error
             same-len-when-expression-list-renamevar))

  (defruled same-statement-kind-when-statement-renamevar
    (implies (not (resulterrp (statement-renamevar old new ren)))
             (equal (statement-kind new)
                    (statement-kind old)))
    :expand (statement-renamevar old new ren))

  (defruled block-option-renamevar-of-nil-1-forward
    (implies (not (resulterrp (block-option-renamevar nil block ren)))
             (equal block nil))
    :rule-classes ((:forward-chaining
                    :trigger-terms
                    ((resulterrp (block-option-renamevar nil block ren))))))

  (defruled block-option-renamevar-of-nil-2-forward
    (implies (not (resulterrp (block-option-renamevar block nil ren)))
             (equal block nil))
    :rule-classes ((:forward-chaining
                    :trigger-terms
                    ((resulterrp (block-option-renamevar block nil ren))))))

  (defruled block-option-renamevar-when-nonnil
    (implies (and x y)
             (equal (block-option-renamevar x y ren)
                    (block-renamevar x y ren)))
    :expand (block-option-renamevar x y ren)
    :enable block-option-some->val)

  (defruled same-swcase->value-when-swcase-renamevar
    (implies (not (resulterrp (swcase-renamevar old new ren)))
             (equal (swcase->value new)
                    (swcase->value old)))
    :expand (swcase-renamevar old new ren))

  (defruled resulterrp-of-swcase-renamevar
    (equal (resulterrp (swcase-renamevar x y ren))
           (or (not (equal (swcase->value x)
                           (swcase->value y)))
               (resulterrp (block-renamevar (swcase->body x)
                                            (swcase->body y)
                                            ren)))))

  (defruled same-swcase-list->value-list-when-swcase-list-renamevar
    (implies (not (resulterrp (swcase-list-renamevar old new ren)))
             (equal (swcase-list->value-list new)
                    (swcase-list->value-list old)))
    :induct (acl2::cdr-cdr-induct old new)
    :enable same-swcase->value-when-swcase-renamevar)

  (defruled same-fundef->name-when-fundef-renamevar
    (implies (not (resulterrp (fundef-renamevar old new)))
             (equal (fundef->name new)
                    (fundef->name old)))
    :expand (fundef-renamevar old new))

  (defthm-statements/blocks/cases/fundefs-renamevar-flag

    (defthm subsetp-equal-of-statement-renamevar
      (b* ((ren1 (statement-renamevar old new ren)))
        (implies (not (resulterrp ren1))
                 (subsetp-equal (renaming->list ren)
                                (renaming->list ren1))))
      :flag statement-renamevar)

    (defthm subsetp-equal-of-statement-list-renamevar
      (b* ((ren1 (statement-list-renamevar old new ren)))
        (implies (not (resulterrp ren1))
                 (subsetp-equal (renaming->list ren)
                                (renaming->list ren1))))
      :flag statement-list-renamevar)

    (defthm subsetp-equal-of-block-renamevar
      t
      :rule-classes nil
      :flag block-renamevar)

    (defthm subsetp-equal-of-block-option-renamevar
      t
      :rule-classes nil
      :flag block-option-renamevar)

    (defthm subsetp-equal-of-swcase-renamevar
      t
      :rule-classes nil
      :flag swcase-renamevar)

    (defthm subsetp-equal-of-swcase-list-renamevar
      t
      :rule-classes nil
      :flag swcase-list-renamevar)

    (defthm subsetp-equal-of-fundef-renamevar
      t
      :rule-classes nil
      :flag fundef-renamevar)

    :hints (("Goal" :in-theory (enable statement-renamevar
                                       statement-list-renamevar)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef-list-renamevar ((old fundef-listp) (new fundef-listp))
  :returns (_ resulterr-optionp)
  :short "Check if two lists of function definitions are
          related by variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just a lifting of @(tsee fundef-renamevar) to lists.
     It does not add anything new to the definition of variable renaming,
     but it is a useful derived concept.")
   (xdoc::p
    "We prove that if two lists of statements are related by variable renaming,
     then the lists of function definitions extracted from the statements
     are also related by variable renaming.
     We prove this by simultaneous induction
     on the two lists of statements
     also involving the renaming and its updating
     according to the initial statements in the lists."))
  (b* (((when (endp old))
        (if (endp new)
            nil
          (err (list :mismatch-extra-new (fundef-list-fix new)))))
       ((when (endp new))
        (err (list :mismatch-extra-old (fundef-list-fix old))))
       ((ok &) (fundef-renamevar (car old) (car new))))
    (fundef-list-renamevar (cdr old) (cdr new)))
  :hooks (:fix)
  ///

  (defrule fundef-list-renamevar-of-statement-to-fundefs
    (implies (not (resulterrp (statement-list-renamevar old new ren)))
             (not (resulterrp
                   (fundef-list-renamevar (statements-to-fundefs old)
                                          (statements-to-fundefs new)))))
    :induct (ind old new ren)
    :enable (statement-renamevar
             statement-list-renamevar
             statements-to-fundefs
             same-statement-kind-when-statement-renamevar)

    :prep-lemmas

    ((defun ind (old new ren)
       (b* (((when (endp old)) nil)
            ((when (endp new)) nil)
            (ren (statement-renamevar (car old) (car new) ren))
            ((when (resulterrp ren)) nil))
         (ind (cdr old) (cdr new) ren))))))
