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

(defxdoc+ renaming-variables
  :parents (transformation)
  :short "Renaming of variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see disambiguator) for background.")
   (xdoc::p
    "Here we characterize, relationally, the renaming of variables.
     The predicate mentioned in @(see disambiguator),
     i.e. the one that related original and transformed code,
     is actually a function that returns success or failure.
     More precisely, as with other aspects of Yul,
     it is a family of functions,
     with a member of each kind of Yul syntactic entity
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
     updated renaming information.")
   (xdoc::p
    "The renaming information is captured as
     an omap from identifiers to identifiers.
     Its keys are the variables in scope in the old code;
     its values are the variables in scope in the new code.
     These facts hold because of the way the omap is threaded through,
     in the ACL2 code that defines the renaming relation.
     These facts are formally explicated and proved as part of the "
    (xdoc::seetopic "disambiguator-variables-safety"
                    "the proof of static safety preservation")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-renamevar ((old identifierp)
                       (new identifierp)
                       (ren identifier-identifier-mapp))
  :returns (_ resulterr-optionp)
  :short "Check if two variables are related by variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check is the two variables form an association pair in the omap."))
  (b* ((old (identifier-fix old))
       (new (identifier-fix new))
       (ren (identifier-identifier-map-fix ren)))
    (if (equal (omap::in old ren)
               (cons old new))
        nil
      (err (list :mismatch old new ren))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-list-renamevar ((old identifier-listp)
                            (new identifier-listp)
                            (ren identifier-identifier-mapp))
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

(define path-renamevar ((old pathp)
                        (new pathp)
                        (ren identifier-identifier-mapp))
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

(define path-list-renamevar ((old path-listp)
                             (new path-listp)
                             (ren identifier-identifier-mapp))
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
                                (ren identifier-identifier-mapp))
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
                                     (ren identifier-identifier-mapp))
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
                             (ren identifier-identifier-mapp))
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

  ///

  (fty::deffixequiv-mutual expressions-renamevar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expression-option-renamevar ((old expression-optionp)
                                     (new expression-optionp)
                                     (ren identifier-identifier-mapp))
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
                                  (ren identifier-identifier-mapp))
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
                                 (ren identifier-identifier-mapp))
  :returns (new-ren identifier-identifier-map-resultp)
  :short "Add a variable to a variable renaming map."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that the old variable is not already a key in the map.
     This is always the case when processing statically safe code,
     because variables are addded to the renaming map as they get in scope,
     and the static safety checks ensure that
     only variables not in scope are added to the scope.")
   (xdoc::p
    "We could consider omitting this check here,
     but having it facilitates some proofs."))
  (b* ((old (identifier-fix old))
       (new (identifier-fix new))
       (ren (identifier-identifier-map-fix ren)))
    (if (consp (omap::in old ren))
        (err (list :var-already-in-scope old new ren))
      (omap::update old new ren)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-vars-to-var-renaming ((old identifier-listp)
                                  (new identifier-listp)
                                  (ren identifier-identifier-mapp))
  :returns (new-ren identifier-identifier-map-resultp)
  :short "Add the variables in a list to a variable renaming map."
  (b* (((when (endp old))
        (if (endp new)
            (identifier-identifier-map-fix ren)
          (err (list :mismatch-extra-new (identifier-list-fix new)))))
       ((when (endp new))
        (err (list :mismatch-extra-old (identifier-list-fix old))))
       ((ok ren) (add-var-to-var-renaming (car old) (car new) ren)))
    (add-vars-to-var-renaming (cdr old) (cdr new) ren))
  :hooks (:fix)
  ///

  (defruled same-len-when-add-vars-to-var-renaming
    (implies (not (resulterrp (add-vars-to-var-renaming old new ren)))
             (equal (len new) (len old)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines statements/blocks/cases/fundefs-renamevar
  :short "Mutually recursive ACL2 functions to check if
          statements, blocks, cases, and function definitions are
          related by variable renaming."

  (define statement-renamevar ((old statementp)
                               (new statementp)
                               (ren identifier-identifier-mapp))
    :returns (new-ren identifier-identifier-map-resultp)
    :short "Check if two statements are
            related by variable renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "In case of success,
       this function returns a renaming map
       updated according to the variables introduced in the statement.")
     (xdoc::p
      "Old and new statement must be of the same kind,
       and have constituents recursively related.")
     (xdoc::p
      "Variable declarations extend the renaming map
       with additional associations.
       All the other kinds of statements
       leave the renaming map unchanged.")
     (xdoc::p
      "We treat the initialization blocks of a loop specially,
       as usual (e.g. in the static safety checks and in dynamic execution):
       we extend the renaming map according to
       the statements in the initialization block,
       and then we process the rest of the statement
       with the updated renaming map.
       However, the renaming map after the loop is the same as the one before:
       a loop does not permanently introduce new variables.")
     (xdoc::p
      "The ACL2 function to check function definitions
       does not take a renaming map as argument,
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
       (identifier-identifier-map-fix ren))
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
       (identifier-identifier-map-fix ren))
     :assign-multi
     (b* (((unless (statement-case new :assign-multi))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-assign-multi new) new)
          ((ok &) (path-list-renamevar old.targets new.targets ren))
          ((ok &) (funcall-renamevar old.value new.value ren)))
       (identifier-identifier-map-fix ren))
     :funcall
     (b* (((unless (statement-case new :funcall))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-funcall new) new)
          ((ok &) (funcall-renamevar old.get new.get ren)))
       (identifier-identifier-map-fix ren))
     :if
     (b* (((unless (statement-case new :if))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-if new) new)
          ((ok &) (expression-renamevar old.test new.test ren))
          ((ok &) (block-renamevar old.body new.body ren)))
       (identifier-identifier-map-fix ren))
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
       (identifier-identifier-map-fix ren))
     :switch
     (b* (((unless (statement-case new :switch))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-switch new) new)
          ((ok &) (expression-renamevar old.target new.target ren))
          ((ok &) (swcase-list-renamevar old.cases new.cases ren))
          ((ok &) (block-option-renamevar old.default new.default ren)))
       (identifier-identifier-map-fix ren))
     :leave
     (b* (((unless (statement-case new :leave))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new)))))
       (identifier-identifier-map-fix ren))
     :break
     (b* (((unless (statement-case new :break))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new)))))
       (identifier-identifier-map-fix ren))
     :continue
     (b* (((unless (statement-case new :continue))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new)))))
       (identifier-identifier-map-fix ren))
     :fundef
     (b* (((unless (statement-case new :fundef))
           (err (list :mismatch
                  (statement-fix old)
                  (statement-fix new))))
          ((statement-fundef new) new)
          ((ok &) (fundef-renamevar old.get new.get)))
       (identifier-identifier-map-fix ren)))
    :measure (statement-count old))

  (define statement-list-renamevar ((old statement-listp)
                                    (new statement-listp)
                                    (ren identifier-identifier-mapp))
    :returns (new-ren identifier-identifier-map-resultp)
    :short "Check if two lists of statements are
            related by variable renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two lists must have the same length,
       and have corresponding elements related by the renaming.
       The renaming map is updated and threaded through the statements."))
    (b* (((when (endp old))
          (if (endp new)
              (identifier-identifier-map-fix ren)
            (err (list :mismatch-extra-new (statement-list-fix new)))))
         ((when (endp new))
          (err (list :mismatch-extra-old (statement-list-fix old))))
         ((ok ren) (statement-renamevar (car old) (car new) ren)))
      (statement-list-renamevar (cdr old) (cdr new) ren))
    :measure (statement-list-count old))

  (define block-renamevar ((old blockp)
                           (new blockp)
                           (ren identifier-identifier-mapp))
    :returns (_ resulterr-optionp)
    :short "Check if two blocks are
            related by variable renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "We process the list of statements,
       discarding the final renaming map,
       because the scope of a block ends at the end of the block."))
    (b* ((old-stmts (block->statements old))
         (new-stmts (block->statements new))
         ((ok &) (statement-list-renamevar old-stmts new-stmts ren)))
      nil)
    :measure (block-count old))

  (define block-option-renamevar ((old block-optionp)
                                  (new block-optionp)
                                  (ren identifier-identifier-mapp))
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
                            (ren identifier-identifier-mapp))
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
                                 (ren identifier-identifier-mapp))
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
      "We initialize the renaming map according to the inputs and outputs,
       and then we process the bodies."))
    (b* (((unless (equal (fundef->name old)
                         (fundef->name new)))
          (err (list :mismatch-function-name
                 (fundef->name old)
                 (fundef->name new))))
         ((ok ren) (add-vars-to-var-renaming (fundef->inputs old)
                                             (fundef->inputs new)
                                             nil))
         ((ok ren) (add-vars-to-var-renaming (fundef->outputs old)
                                             (fundef->outputs new)
                                             ren)))
      (block-renamevar (fundef->body old) (fundef->body new) ren))
    :measure (fundef-count old))

  :verify-guards nil ; done below
  ///
  (verify-guards statement-renamevar)

  (fty::deffixequiv-mutual statements/blocks/cases/fundefs-renamevar)

  (defruled same-statement-kind-when-statement-renamevar
    (implies (not (resulterrp (statement-renamevar old new ren)))
             (equal (statement-kind new)
                    (statement-kind old)))
    :expand (statement-renamevar old new ren))

  (defruled same-swcase->value-when-swcase-renamevar
    (implies (not (resulterrp (swcase-renamevar old new ren)))
             (equal (swcase->value new)
                    (swcase->value old)))
    :expand (swcase-renamevar old new ren))

  (defruled same-swcase-list->value-list-when-swcase-list-renamevar
    (implies (not (resulterrp (swcase-list-renamevar old new ren)))
             (equal (swcase-list->value-list new)
                    (swcase-list->value-list old)))
    :induct (acl2::cdr-cdr-induct old new)
    :enable same-swcase->value-when-swcase-renamevar
    :prep-books ((include-book "std/basic/inductions" :dir :system)))

  (defruled same-fundef->name-when-fundef-renamevar
    (implies (not (resulterrp (fundef-renamevar old new)))
             (equal (fundef->name new)
                    (fundef->name old)))
    :expand (fundef-renamevar old new)))

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
