; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../language/dynamic-semantics")

(include-book "../../representation/integer-operations")

(include-book "../test-star")

(include-book "syntaxp")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-pure-rules
  :short "Rules for @(tsee exec-expr-pure)."
  :long
  (xdoc::topstring
   (xdoc::p
    "For @('&&') and @('||'),
     we use the auxiliary function @('sint-from-boolean-with-error')
     as an intermediate rewriting stage.")
   (xdoc::p
    "We include the executable counterpart of @(tsee member-equal),
     needed to discharge the hypothesis of
     the rule for strict pure binary expressions.")
   (xdoc::p
    "We include executable counterparts of accessor functions for expressions,
     used to check the kind of expression and to retrieve its constituents.")
   (xdoc::p
    "Besides the rules for the large symbolic execution,
     whose names we put into the constant defined at the end,
     we also prove rules used in the new modular proofs.
     The latter rules avoid @(tsee if) in the right side,
     to avoid unwanted case splits;
     furthermore, they wrap the @(tsee if) tests into @(tsee test*)
     to prevent unwanted rewrites (see @(tsee atc-contextualize)).")
   (xdoc::p
    "We also include the function @('exec-arrsub-of-member'),
     which combines @(tsee exec-member) and @(tsee exec-arrsub),
     so that the execution of expressions of the form @('s.m[i]')
     (where @('s') is a structure,
     @('m') is the name of a member of the structure of array type,
     and @('i') is an index into the array)
     turn into this single function,
     which is the one that the @(tsee defstruct)-specific generated theorems
     turn into the shallowly embedded structure array member readers.")
   (xdoc::p
    "We also include the function @('exec-arrsub-of-memberp'),
     which combines @(tsee exec-memberp) and @(tsee exec-arrsub),
     so that the execution of expressions of the form @('s->m[i]')
     (where @('s') is a pointer to a structure,
     @('m') is the name of a member of the structure of array type,
     and @('i') is an index into the array)
     turn into this single function,
     which is the one that the @(tsee defstruct)-specific generated theorems
     turn into the shallowly embedded structure array member readers."))

  (define exec-arrsub-of-member ((str expr-valuep)
                                 (mem identp)
                                 (sub expr-valuep)
                                 (compst compustatep))
    :returns (eval expr-value-resultp)
    :parents nil
    (b* ((str (apconvert-expr-value str))
         ((when (errorp str)) str)
         (val-str (expr-value->value str))
         ((unless (value-case val-str :struct))
          (error (list :mistype-member
                       :required :struct
                       :supplied (type-of-value val-str))))
         (val-mem (value-struct-read mem val-str))
         ((when (errorp val-mem)) val-mem)
         (objdes-str (expr-value->object str))
         (objdes-mem (and objdes-str
                          (make-objdesign-member :super objdes-str :name mem)))
         (eval-mem (apconvert-expr-value (expr-value val-mem objdes-mem)))
         ((when (errorp eval-mem)) eval-mem)
         (val-mem (expr-value->value eval-mem))
         ((unless (value-case val-mem :pointer))
          (error (list :mistype-arrsub
                       :required :pointer
                       :supplied (type-of-value val-mem))))
         ((unless (value-pointer-validp val-mem))
          (error (list :invalid-pointer val-mem)))
         (objdes-mem (value-pointer->designator val-mem))
         (reftype (value-pointer->reftype val-mem))
         (array (read-object objdes-mem compst))
         ((when (errorp array))
          (error (list :array-not-found val-mem (compustate-fix compst))))
         ((unless (value-case array :array))
          (error (list :not-array val-mem (compustate-fix compst))))
         ((unless (equal reftype (value-array->elemtype array)))
          (error (list :mistype-array-read
                       :pointer reftype
                       :array (value-array->elemtype array))))
         (sub (apconvert-expr-value sub))
         ((when (errorp sub)) sub)
         (sub (expr-value->value sub))
         ((unless (value-integerp sub)) (error
                                         (list :mistype-array :index
                                               :required :integer
                                               :supplied (type-of-value sub))))
         (index (value-integer->get sub))
         ((when (< index 0)) (error (list :negative-array-index
                                          :array array
                                          :index sub)))
         (val (value-array-read index array))
         ((when (errorp val)) val)
         (elem-objdes (make-objdesign-element :super objdes-mem :index index)))
      (make-expr-value :value val :object elem-objdes))
    :hooks (:fix))

  (define exec-arrsub-of-memberp ((str expr-valuep)
                                  (mem identp)
                                  (sub expr-valuep)
                                  (compst compustatep))
    :returns (eval expr-value-resultp)
    :parents nil
    (b* ((str (apconvert-expr-value str))
         ((when (errorp str)) str)
         (str (expr-value->value str))
         ((unless (value-case str :pointer))
          (error (list :mistype-memberp
                       :required :pointer
                       :supplied (type-of-value str))))
         ((unless (value-pointer-validp str))
          (error (list :invalid-pointer str)))
         (objdes (value-pointer->designator str))
         (reftype (value-pointer->reftype str))
         (struct (read-object objdes compst))
         ((when (errorp struct))
          (error (list :struct-not-found str (compustate-fix compst))))
         ((unless (value-case struct :struct))
          (error (list :not-struct str (compustate-fix compst))))
         ((unless (equal reftype
                         (type-struct (value-struct->tag struct))))
          (error (list :mistype-struct-read
                       :pointer reftype
                       :array (type-struct (value-struct->tag struct)))))
         (val-mem (value-struct-read mem struct))
         ((when (errorp val-mem)) val-mem)
         (objdes-mem (make-objdesign-member :super objdes :name mem))
         (eval-mem (apconvert-expr-value (expr-value val-mem objdes-mem)))
         ((when (errorp eval-mem)) eval-mem)
         (val-mem (expr-value->value eval-mem))
         ((unless (value-case val-mem :pointer))
          (error (list :mistype-arrsub
                       :required :pointer
                       :supplied (type-of-value val-mem))))
         ((unless (value-pointer-validp val-mem))
          (error (list :invalid-pointer val-mem)))
         (objdes-mem (value-pointer->designator val-mem))
         (reftype (value-pointer->reftype val-mem))
         (array (read-object objdes-mem compst))
         ((when (errorp array))
          (error (list :array-not-found val-mem (compustate-fix compst))))
         ((unless (value-case array :array))
          (error (list :not-array val-mem (compustate-fix compst))))
         ((unless (equal reftype (value-array->elemtype array)))
          (error (list :mistype-array-read
                       :pointer reftype
                       :array (value-array->elemtype array))))
         (sub (apconvert-expr-value sub))
         ((when (errorp sub)) sub)
         (sub (expr-value->value sub))
         ((unless (value-integerp sub)) (error
                                         (list :mistype-array :index
                                               :required :integer
                                               :supplied (type-of-value sub))))
         (index (value-integer->get sub))
         ((when (< index 0)) (error (list :negative-array-index
                                          :array array
                                          :index sub)))
         (val (value-array-read index array))
         ((when (errorp val)) val)
         (elem-objdes (make-objdesign-element :super objdes-mem :index index)))
      (make-expr-value :value val :object elem-objdes))
    :hooks (:fix))

  (defruled exec-expr-pure-when-ident
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :ident))
             (equal (exec-expr-pure e compst)
                    (exec-ident (expr-ident->get e) compst)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-ident-no-syntaxp
    (implies (equal (expr-kind e) :ident)
             (equal (exec-expr-pure e compst)
                    (exec-ident (expr-ident->get e) compst)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-const
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :const))
             (equal (exec-expr-pure e compst)
                    (exec-const (expr-const->get e))))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-arrsub
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :arrsub)
                  (equal arr (expr-arrsub->arr e))
                  (not (expr-case arr :member))
                  (not (expr-case arr :memberp))
                  (equal evalarr (exec-expr-pure arr compst))
                  (expr-valuep evalarr)
                  (equal evalsub (exec-expr-pure (expr-arrsub->sub e) compst))
                  (expr-valuep evalsub))
             (equal (exec-expr-pure e compst)
                    (exec-arrsub evalarr evalsub compst)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-member
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :member)
                  (equal eval (exec-expr-pure (expr-member->target e) compst))
                  (expr-valuep eval))
             (equal (exec-expr-pure e compst)
                    (exec-member eval (expr-member->name e))))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-member-no-syntaxp
    (implies (and (equal (expr-kind e) :member)
                  (equal eval (exec-expr-pure (expr-member->target e) compst))
                  (expr-valuep eval))
             (equal (exec-expr-pure e compst)
                    (exec-member eval (expr-member->name e))))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-memberp
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :memberp)
                  (equal eval (exec-expr-pure (expr-memberp->target e) compst))
                  (expr-valuep eval))
             (equal (exec-expr-pure e compst)
                    (exec-memberp eval (expr-memberp->name e) compst)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-memberp-no-syntaxp
    (implies (and (equal (expr-kind e) :memberp)
                  (equal eval (exec-expr-pure (expr-memberp->target e) compst))
                  (expr-valuep eval))
             (equal (exec-expr-pure e compst)
                    (exec-memberp eval (expr-memberp->name e) compst)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-arrsub-of-member
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :arrsub)
                  (equal arr (expr-arrsub->arr e))
                  (expr-case arr :member)
                  (equal evalstr
                         (exec-expr-pure (expr-member->target arr) compst))
                  (expr-valuep evalstr)
                  (equal evalsub
                         (exec-expr-pure (expr-arrsub->sub e) compst))
                  (expr-valuep evalsub))
             (equal (exec-expr-pure e compst)
                    (exec-arrsub-of-member evalstr
                                           (expr-member->name arr)
                                           evalsub
                                           compst)))
    :expand ((exec-expr-pure e compst)
             (exec-expr-pure (expr-arrsub->arr e) compst))
    :enable (exec-member
             exec-arrsub
             exec-arrsub-of-member
             apconvert-expr-value
             not-errorp-when-expr-valuep))

  (defruled exec-expr-pure-when-arrsub-of-member-no-syntaxp
    (implies (and (equal (expr-kind e) :arrsub)
                  (equal arr (expr-arrsub->arr e))
                  (expr-case arr :member)
                  (equal evalstr
                         (exec-expr-pure (expr-member->target arr) compst))
                  (expr-valuep evalstr)
                  (equal evalsub
                         (exec-expr-pure (expr-arrsub->sub e) compst))
                  (expr-valuep evalsub))
             (equal (exec-expr-pure e compst)
                    (exec-arrsub-of-member evalstr
                                           (expr-member->name arr)
                                           evalsub
                                           compst)))
    :expand ((exec-expr-pure e compst)
             (exec-expr-pure (expr-arrsub->arr e) compst))
    :enable (exec-member
             exec-arrsub
             exec-arrsub-of-member
             apconvert-expr-value
             not-errorp-when-expr-valuep))

  (defruled exec-expr-pure-when-arrsub-of-memberp
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :arrsub)
                  (equal arr (expr-arrsub->arr e))
                  (expr-case arr :memberp)
                  (equal evalstr
                         (exec-expr-pure (expr-memberp->target arr) compst))
                  (expr-valuep evalstr)
                  (equal evalsub
                         (exec-expr-pure (expr-arrsub->sub e) compst))
                  (expr-valuep evalsub))
             (equal (exec-expr-pure e compst)
                    (exec-arrsub-of-memberp evalstr
                                            (expr-memberp->name arr)
                                            evalsub
                                            compst)))
    :expand ((exec-expr-pure e compst)
             (exec-expr-pure (expr-arrsub->arr e) compst))
    :enable (exec-memberp
             exec-arrsub
             exec-arrsub-of-memberp
             apconvert-expr-value
             not-errorp-when-expr-valuep)
    :disable equal-of-type-struct) ; <-- to reduce splits

  (defruled exec-expr-pure-when-arrsub-of-memberp-no-syntaxp
    (implies (and (equal (expr-kind e) :arrsub)
                  (equal arr (expr-arrsub->arr e))
                  (expr-case arr :memberp)
                  (equal evalstr
                         (exec-expr-pure (expr-memberp->target arr) compst))
                  (expr-valuep evalstr)
                  (equal evalsub
                         (exec-expr-pure (expr-arrsub->sub e) compst))
                  (expr-valuep evalsub))
             (equal (exec-expr-pure e compst)
                    (exec-arrsub-of-memberp evalstr
                                            (expr-memberp->name arr)
                                            evalsub
                                            compst)))
    :expand ((exec-expr-pure e compst)
             (exec-expr-pure (expr-arrsub->arr e) compst))
    :enable (exec-memberp
             exec-arrsub
             exec-arrsub-of-memberp
             apconvert-expr-value
             not-errorp-when-expr-valuep)
    :disable equal-of-type-struct) ; <-- to reduce splits

  (defruled exec-expr-pure-when-unary
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :unary)
                  (equal eval (exec-expr-pure (expr-unary->arg e) compst))
                  (expr-valuep eval))
             (equal (exec-expr-pure e compst)
                    (exec-unary (expr-unary->op e) eval compst)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-cast
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :cast)
                  (equal eval (exec-expr-pure (expr-cast->arg e) compst))
                  (expr-valuep eval))
             (equal (exec-expr-pure e compst)
                    (exec-cast (expr-cast->type e) eval)))
    :enable exec-expr-pure)

  (defruled exec-expr-pure-when-strict-pure-binary
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal op (expr-binary->op e))
                  (member-equal (binop-kind op)
                                '(:mul :div :rem :add :sub :shl :shr
                                  :lt :gt :le :ge :eq :ne
                                  :bitand :bitxor :bitior))
                  (equal eval1 (exec-expr-pure (expr-binary->arg1 e) compst))
                  (equal eval2 (exec-expr-pure (expr-binary->arg2 e) compst))
                  (expr-valuep eval1)
                  (expr-valuep eval2))
             (equal (exec-expr-pure e compst)
                    (exec-binary-strict-pure op eval1 eval2)))
    :enable (exec-expr-pure binop-purep))

  (defund sint-from-boolean-with-error (test)
    (if (errorp test)
        test
      (if test
          (expr-value (sint-from-integer 1) nil)
        (expr-value (sint-from-integer 0) nil))))

  (defruled exec-expr-pure-when-binary-logand
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal op (expr-binary->op e))
                  (equal (binop-kind op) :logand)
                  (equal arg1 (exec-expr-pure (expr-binary->arg1 e) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test1 (test-value (expr-value->value carg1)))
                  (booleanp test1))
             (equal (exec-expr-pure e compst)
                    (if test1
                        (sint-from-boolean-with-error
                         (b* ((arg2 (exec-expr-pure (expr-binary->arg2 e)
                                                    compst))
                              ((when (errorp arg2)) arg2)
                              (arg2 (apconvert-expr-value arg2))
                              ((when (errorp arg2)) arg2))
                           (test-value (expr-value->value arg2))))
                      (expr-value (sint-from-integer 0) nil))))
    :enable (exec-expr-pure binop-purep sint-from-boolean-with-error))

  (defruled exec-expr-pure-when-binary-logand-and-true
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal op (expr-binary->op e))
                  (equal (binop-kind op) :logand)
                  (equal arg1 (exec-expr-pure (expr-binary->arg1 e) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test1 (test-value (expr-value->value carg1)))
                  (booleanp test1)
                  (test* test1)
                  (equal arg2 (exec-expr-pure (expr-binary->arg2 e) compst))
                  (expr-valuep arg2)
                  (equal carg2 (apconvert-expr-value arg2))
                  (expr-valuep carg2)
                  (equal test2 (test-value (expr-value->value carg2)))
                  (booleanp test2))
             (equal (exec-expr-pure e compst)
                    (expr-value (sint-from-boolean test2) nil)))
    :do-not-induct t
    :enable (exec-expr-pure binop-purep test*))

  (defruled exec-expr-pure-when-binary-logand-and-false
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal op (expr-binary->op e))
                  (equal (binop-kind op) :logand)
                  (equal arg1 (exec-expr-pure (expr-binary->arg1 e) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test1 (test-value (expr-value->value carg1)))
                  (booleanp test1)
                  (test* (not test1)))
             (equal (exec-expr-pure e compst)
                    (expr-value (sint-from-integer 0) nil)))
    :enable (exec-expr-pure binop-purep test*))

  (defruled exec-expr-pure-when-binary-logor
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal op (expr-binary->op e))
                  (equal (binop-kind op) :logor)
                  (equal arg1 (exec-expr-pure (expr-binary->arg1 e) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test1 (test-value (expr-value->value carg1)))
                  (booleanp test1))
             (equal (exec-expr-pure e compst)
                    (if test1
                        (expr-value (sint-from-integer 1) nil)
                      (sint-from-boolean-with-error
                       (b* ((arg2 (exec-expr-pure (expr-binary->arg2 e)
                                                  compst))
                            ((when (errorp arg2)) arg2)
                            (arg2 (apconvert-expr-value arg2))
                            ((when (errorp arg2)) arg2))
                         (test-value (expr-value->value arg2)))))))
    :enable (exec-expr-pure binop-purep sint-from-boolean-with-error))

  (defruled exec-expr-pure-when-binary-logor-and-true
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal op (expr-binary->op e))
                  (equal (binop-kind op) :logor)
                  (equal arg1 (exec-expr-pure (expr-binary->arg1 e) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test1 (test-value (expr-value->value carg1)))
                  (booleanp test1)
                  (test* test1))
             (equal (exec-expr-pure e compst)
                    (expr-value (sint-from-integer 1) nil)))
    :enable (exec-expr-pure binop-purep test*))

  (defruled exec-expr-pure-when-binary-logor-and-false
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal op (expr-binary->op e))
                  (equal (binop-kind op) :logor)
                  (equal arg1 (exec-expr-pure (expr-binary->arg1 e) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test1 (test-value (expr-value->value carg1)))
                  (booleanp test1)
                  (test* (not test1))
                  (equal arg2 (exec-expr-pure (expr-binary->arg2 e) compst))
                  (expr-valuep arg2)
                  (equal carg2 (apconvert-expr-value arg2))
                  (expr-valuep carg2)
                  (equal test2 (test-value (expr-value->value carg2)))
                  (booleanp test2))
             (equal (exec-expr-pure e compst)
                    (expr-value (sint-from-boolean test2) nil)))
    :enable (exec-expr-pure binop-purep test*))

  (make-event
   `(defruled sint-from-boolean-with-error-when-booleanp
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'test)
                    (booleanp test))
               (equal (sint-from-boolean-with-error test)
                      (if test
                          (expr-value (sint-from-integer 1) nil)
                        (expr-value (sint-from-integer 0) nil))))
      :enable sint-from-boolean-with-error))

  (make-event
   `(defruled sint-from-boolean-with-error-when-booleanp-and-true
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'test)
                    (booleanp test)
                    (test* test))
               (equal (sint-from-boolean-with-error test)
                      (expr-value (sint-from-integer 1) nil)))
      :enable (sint-from-boolean-with-error test*)))

  (make-event
   `(defruled sint-from-boolean-with-error-when-booleanp-and-false
      (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'test)
                    (booleanp test)
                    (test* (not test)))
               (equal (sint-from-boolean-with-error test)
                      (expr-value (sint-from-integer 0) nil)))
      :enable (sint-from-boolean-with-error test*)))

  (defund exec-expr-pure-apconvert-no-object (e compst)
    (b* ((eval (exec-expr-pure e compst))
         ((when (errorp eval)) eval)
         (eval1 (apconvert-expr-value eval))
         ((when (errorp eval1)) eval1))
      (expr-value (expr-value->value eval1) nil)))

  (defruled exec-expr-pure-apconvert-no-object-open
    (implies (and (equal eval (exec-expr-pure e compst))
                  (expr-valuep eval)
                  (equal eval1 (apconvert-expr-value eval))
                  (expr-valuep eval1))
             (equal (exec-expr-pure-apconvert-no-object e compst)
                    (expr-value (expr-value->value eval1) nil)))
    :enable exec-expr-pure-apconvert-no-object)

  (defruled exec-expr-pure-when-cond
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :cond)
                  (equal arg1 (exec-expr-pure (expr-cond->test e) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test (test-value (expr-value->value carg1)))
                  (booleanp test))
             (equal (exec-expr-pure e compst)
                    (if test
                        (exec-expr-pure-apconvert-no-object
                         (expr-cond->then e) compst)
                      (exec-expr-pure-apconvert-no-object
                       (expr-cond->else e) compst))))
    :enable (exec-expr-pure
             exec-expr-pure-apconvert-no-object))

  (defruled exec-expr-pure-when-cond-and-true
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :cond)
                  (equal arg1 (exec-expr-pure (expr-cond->test e) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test (test-value (expr-value->value carg1)))
                  (booleanp test)
                  (test* test)
                  (equal eval (exec-expr-pure (expr-cond->then e) compst))
                  (expr-valuep eval)
                  (equal eval1 (apconvert-expr-value eval))
                  (expr-valuep eval1))
             (equal (exec-expr-pure e compst)
                    (expr-value (expr-value->value eval1) nil)))
    :enable (exec-expr-pure test*))

  (defruled exec-expr-pure-when-cond-and-false
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :cond)
                  (equal arg1 (exec-expr-pure (expr-cond->test e) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test (test-value (expr-value->value carg1)))
                  (booleanp test)
                  (test* (not test))
                  (equal eval (exec-expr-pure (expr-cond->else e) compst))
                  (expr-valuep eval)
                  (equal eval1 (apconvert-expr-value eval))
                  (expr-valuep eval1))
             (equal (exec-expr-pure e compst)
                    (expr-value (expr-value->value eval1) nil)))
    :enable (exec-expr-pure test*))

  (defval *atc-exec-expr-pure-rules*
    '(exec-expr-pure-when-ident
      exec-expr-pure-when-const
      exec-expr-pure-when-arrsub
      exec-expr-pure-when-member
      exec-expr-pure-when-memberp
      exec-expr-pure-when-arrsub-of-member
      exec-expr-pure-when-arrsub-of-memberp
      exec-expr-pure-when-unary
      exec-expr-pure-when-cast
      exec-expr-pure-when-strict-pure-binary
      exec-expr-pure-when-binary-logand
      exec-expr-pure-when-binary-logor
      sint-from-boolean-with-error-when-booleanp
      exec-expr-pure-apconvert-no-object-open
      exec-expr-pure-when-cond
      expr-valuep-of-expr-value
      expr-value->value-of-expr-value
      (:e member-equal)
      (:e expr-kind)
      (:e expr-ident->get)
      (:e expr-const->get)
      (:e expr-arrsub->arr)
      (:e expr-arrsub->sub)
      (:e expr-member->target)
      (:e expr-member->name)
      (:e expr-memberp->target)
      (:e expr-memberp->name)
      (:e expr-unary->op)
      (:e expr-unary->arg)
      (:e expr-cast->type)
      (:e expr-cast->arg)
      (:e expr-binary->op)
      (:e expr-binary->arg1)
      (:e expr-binary->arg2)
      (:e binop-kind)
      (:e expr-cond->test)
      (:e expr-cond->then)
      (:e expr-cond->else))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-pure-list-rules
  :short "Rules for @(tsee exec-expr-pure-list)."

  (defruled exec-expr-pure-list-of-nil
    (equal (exec-expr-pure-list nil compst)
           nil)
    :enable exec-expr-pure-list)

  (defruled exec-expr-pure-list-when-consp
    (implies (and (syntaxp (quotep es))
                  (consp es)
                  (equal eval (exec-expr-pure (car es) compst))
                  (expr-valuep eval)
                  (equal eval1 (apconvert-expr-value eval))
                  (expr-valuep eval1)
                  (equal val (expr-value->value eval1))
                  (equal vals (exec-expr-pure-list (cdr es) compst))
                  (value-listp vals))
             (equal (exec-expr-pure-list es compst)
                    (cons val vals)))
    :enable exec-expr-pure-list)

  (defval *atc-exec-expr-pure-list-rules*
    '(exec-expr-pure-list-of-nil
      exec-expr-pure-list-when-consp)))
