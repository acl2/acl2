; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2026 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "test-star")
(include-book "pure-expression-execution")
(include-book "syntaxp-for-expr-pure")

(include-book "../representation/integers")
(include-book "../representation/integer-operations")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ exec-expr-pure-openers
  :parents (proof-support)
  :short "Opener rules for @(tsee exec-expr-pure)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide rules for different kinds of expressions.")
   (xdoc::p
    "For the non-strict expressions
     (logical conjunction, logical disjunction, and ternary conditional),
     we provide both splitting rules (i.e. which produce @(tsee if)s)
     and non-splitting rules.
     The non-splitting rules use the @(tsee test*) wrapper for the tests,
     which can be enabled if desired;
     see @(tsee test*) for its rationale.
     Perhaps the splitting rules should use that as well.")
   (xdoc::p
    "We provide rules with @(tsee syntaxp) hypotheses saying that
     the ASTs (for test and body) being executed are quoted constants;
     these rules are suitable for symbolic execution of concrete code.
     We also provide versions without @(tsee syntaxp) hypotheses,
     for other uses.")
   (xdoc::p
    "We provide rulesets for some subsets of the rules.")
   (xdoc::p
    "Some of these rules rewrite to terms that contain
     ``intermediate'' functions that we introduce here,
     along with rules for these intermediate functions.
     We have found these intermediate functions useful in symbolic execution,
     e.g. to ``stage'' rewrites."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-arrsub-of-member ((str expr-valuep)
                               (mem identp)
                               (sub expr-valuep)
                               (compst compustatep))
  :returns (eval expr-value-resultp)
  :short "Combination of @(tsee exec-member) and @(tsee exec-arrsub)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for the execution of expressions of the form @('s.m[i]'),
     where @('s') is a structure,
     @('m') is the name of a member of the structure of array type,
     and @('i') is an index into the array.
     Our rules turn those execuctions into this single function.")
   (xdoc::p
    "In ATC, the @(tsee defstruct)-specific generated theorems
     turn calls of this function into
     the shallowly embedded structure array member readers."))
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
  :guard-hints (("Goal" :in-theory (enable (:e tau-system)))))

;;;;;;;;;;;;;;;;;;;;

(define exec-arrsub-of-memberp ((str expr-valuep)
                                (mem identp)
                                (sub expr-valuep)
                                (compst compustatep))
  :returns (eval expr-value-resultp)
  :short "Combination of @(tsee exec-memberp) and @(tsee exec-arrsub)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for the execution of expressions of the form @('s->m[i]'),
     where @('s') is a pointer to a structure,
     @('m') is the name of a member of the structure of array type,
     and @('i') is an index into the array.
     Our rules turn those execuctions into this single function.")
   (xdoc::p
    "In ATC, the @(tsee defstruct)-specific generated theorems
     turn calls of this function into
     the shallowly embedded structure array member readers."))
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
  :guard-hints (("Goal" :in-theory (enable (:e tau-system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-from-boolean-with-error ((test boolean-resultp))
  :returns (eval expr-value-resultp)
  :short "Intermediate function for non-strict binary operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('test') input to this function is
     the boolean result of executing the second operand of @('&&') or @('||'),
     when the first operand is insufficient to determine the final result.
     The usage of this function in the rules for @('&&') and @('||')
     should make the purpose of this function clearer.
     If the result is an error, it is propagated;
     otherwise, an @('int') expression value, with no object designator,
     is returned, based on the boolean.")
   (xdoc::p
    "We also provide some splitting and non-splitting opener rules."))
  (if (errorp test)
      test
    (if test
        (expr-value (sint-from-integer 1) nil)
      (expr-value (sint-from-integer 0) nil)))
  :hooks nil

  ///

  (make-event
   `(defruled sint-from-boolean-with-error-when-booleanp
      (implies (and ,(syntaxp-for-expr-pure 'test)
                    (booleanp test))
               (equal (sint-from-boolean-with-error test)
                      (if test
                          (expr-value (sint-from-integer 1) nil)
                        (expr-value (sint-from-integer 0) nil))))))

  (make-event
   `(defruled sint-from-boolean-with-error-when-booleanp-and-true
      (implies (and ,(syntaxp-for-expr-pure 'test)
                    (booleanp test)
                    (test* test))
               (equal (sint-from-boolean-with-error test)
                      (expr-value (sint-from-integer 1) nil)))))

  (make-event
   `(defruled sint-from-boolean-with-error-when-booleanp-and-false
      (implies (and ,(syntaxp-for-expr-pure 'test)
                    (booleanp test)
                    (test* (not test)))
               (equal (sint-from-boolean-with-error test)
                      (expr-value (sint-from-integer 0) nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-expr-pure-apconvert-no-object ((e exprp) (compst compustatep))
  :returns (eval expr-value-resultp)
  :short "Combination of @(tsee exec-expr-pure)
          and @(tsee apconvert-expr-value),
          without object designator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This calls @(tsee exec-expr-pure),
     propagating any error,
     then it calls @(tsee apconvert-expr-value),
     propagating any error,
     and then it returns an expression value without the object designator.
     We have found this useful for some symbolic executions.")
   (xdoc::p
    "We also provide an opener rule for this function."))
  (b* ((eval (exec-expr-pure e compst))
       ((when (errorp eval)) eval)
       (eval1 (apconvert-expr-value eval))
       ((when (errorp eval1)) eval1))
    (expr-value (expr-value->value eval1) nil))
  :guard-hints
  (("Goal"
    :in-theory (enable expr-valuep-when-expr-value-resultp-and-not-errorp)))

  ///

  (defruled exec-expr-pure-apconvert-no-object-open
    (implies (and (equal eval (exec-expr-pure e compst))
                  (expr-valuep eval)
                  (equal eval1 (apconvert-expr-value eval))
                  (expr-valuep eval1))
             (equal (exec-expr-pure-apconvert-no-object e compst)
                    (expr-value (expr-value->value eval1) nil)))
    :enable ((:e tau-system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-when-ident
  :short "Opener rule for identifier expressions."
  (implies (and (syntaxp (quotep e))
                (equal (expr-kind e) :ident))
           (equal (exec-expr-pure e compst)
                  (exec-ident (expr-ident->get e) compst)))
  :enable exec-expr-pure)

(defruled exec-expr-pure-when-ident-no-syntaxp
  :short "Opener rule for identifier expressions, without @(tsee syntaxp)."
  (implies (equal (expr-kind e) :ident)
           (equal (exec-expr-pure e compst)
                  (exec-ident (expr-ident->get e) compst)))
  :use exec-expr-pure-when-ident)

;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-when-const
  :short "Opener rule for constants as expressions."
  (implies (and (syntaxp (quotep e))
                (equal (expr-kind e) :const))
           (equal (exec-expr-pure e compst)
                  (exec-const (expr-const->get e))))
  :enable exec-expr-pure)

;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-when-arrsub
  :short "Opener rule for array subscript expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We exclude expressions where the array is a structure member,
     because we have different rules for that case."))
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
  :enable (exec-expr-pure (:e tau-system)))

;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-when-member
  :short "Opener rule for structure value member expressions."
  (implies (and (syntaxp (quotep e))
                (equal (expr-kind e) :member)
                (equal eval (exec-expr-pure (expr-member->target e) compst))
                (expr-valuep eval))
           (equal (exec-expr-pure e compst)
                  (exec-member eval (expr-member->name e))))
  :enable (exec-expr-pure  (:e tau-system)))

(defruled exec-expr-pure-when-member-no-syntaxp
  :short "Opener rule for structure value member expressions,
          without @(tsee syntaxp)."
  (implies (and (equal (expr-kind e) :member)
                (equal eval (exec-expr-pure (expr-member->target e) compst))
                (expr-valuep eval))
           (equal (exec-expr-pure e compst)
                  (exec-member eval (expr-member->name e))))
  :use exec-expr-pure-when-member)

;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-when-memberp
  :short "Opener rule for structure pointer member expressions."
  (implies (and (syntaxp (quotep e))
                (equal (expr-kind e) :memberp)
                (equal eval (exec-expr-pure (expr-memberp->target e) compst))
                (expr-valuep eval))
           (equal (exec-expr-pure e compst)
                  (exec-memberp eval (expr-memberp->name e) compst)))
  :enable (exec-expr-pure  (:e tau-system)))

(defruled exec-expr-pure-when-memberp-no-syntaxp
  :short "Opener rule for structure pointer member expressions,
          without @(tsee syntaxp)."
  (implies (and (equal (expr-kind e) :memberp)
                (equal eval (exec-expr-pure (expr-memberp->target e) compst))
                (expr-valuep eval))
           (equal (exec-expr-pure e compst)
                  (exec-memberp eval (expr-memberp->name e) compst)))
  :use exec-expr-pure-when-memberp)

;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-when-arrsub-of-member
  :short "Opener rule for array subscript expressions
          when the array is a strucrure value member."
  :long
  (xdoc::topstring
   (xdoc::p
    "This produces @(tsee exec-arrsub-of-member)."))
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
  :short "Opener rule for array subscript expressions
          when the array is a strucrure value member,
          without @(tsee syntaxp)."
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
  :use exec-expr-pure-when-arrsub-of-member)

;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-when-arrsub-of-memberp
  :short "Opener rule for array subscript expressions
          when the array is a strucrure pointer member."
  :long
  (xdoc::topstring
   (xdoc::p
    "This produces the @(tsee exec-arrsub-of-memberp) function."))
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
           not-errorp-when-expr-valuep))

(defruled exec-expr-pure-when-arrsub-of-memberp-no-syntaxp
  :short "Opener rule for array subscript expressions
          when the array is a strucrure pointer member,
          without @(tsee syntaxp)."
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
  :use exec-expr-pure-when-arrsub-of-memberp)

;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-when-unary
  :short "Opener rule for unary expressions."
  (implies (and (syntaxp (quotep e))
                (equal (expr-kind e) :unary)
                (equal eval (exec-expr-pure (expr-unary->arg e) compst))
                (expr-valuep eval))
           (equal (exec-expr-pure e compst)
                  (exec-unary (expr-unary->op e) eval compst)))
  :enable (exec-expr-pure (:e tau-system)))

;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-when-cast
  :short "Opener rule for unary expressions."
  (implies (and (syntaxp (quotep e))
                (equal (expr-kind e) :cast)
                (equal eval (exec-expr-pure (expr-cast->arg e) compst))
                (expr-valuep eval))
           (equal (exec-expr-pure e compst)
                  (exec-cast (expr-cast->type e) eval)))
  :enable (exec-expr-pure (:e tau-system)))

;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-when-strict-pure-binary
  :short "Opener rule for binary expressions."
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
  :enable (exec-expr-pure binop-purep (:e tau-system)))

;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-when-binary-logand-and-true
  :short "Opener non-splitting rule for logical conjunction expressions,
          when the first operand is true."
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
  :enable (exec-expr-pure
           binop-purep
           test*
           (:e tau-system)))

(defruled exec-expr-pure-when-binary-logand-and-false
  :short "Opener non-splitting rule for logical conjunction expressions,
          when the first operand is false."
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
  :enable (exec-expr-pure
           binop-purep
           test*
           (:e tau-system)))

(defruled exec-expr-pure-when-binary-logand
  :short "Opener splitting rule for logical conjunction expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This produces @(tsee sint-from-boolean-with-error)."))
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
  :enable (exec-expr-pure
           binop-purep
           sint-from-boolean-with-error
           (:e tau-system)))

;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-when-binary-logor-and-true
  :short "Opener non-splitting rule for logical disjunction expressions,
          when the first operand is true."
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
  :enable (exec-expr-pure
           binop-purep
           test*
           (:e tau-system)))

(defruled exec-expr-pure-when-binary-logor-and-false
  :short "Opener non-splitting rule for logical disjunction expressions,
          when the first operand is false."
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
  :enable (exec-expr-pure
           binop-purep
           test*
           (:e tau-system)))

(defruled exec-expr-pure-when-binary-logor
  :short "Opener splitting rule for logical disjunction expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This produces @(tsee sint-from-boolean-with-error)."))
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
  :enable (exec-expr-pure
           binop-purep
           sint-from-boolean-with-error
           (:e tau-system)))

;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-when-cond-and-true
  :short "Opener non-splitting rule for ternary conditional expressions,
          when the test operand is true."
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
  :enable (exec-expr-pure
           test*
           (:e tau-system)))

(defruled exec-expr-pure-when-cond-and-false
  :short "Opener non-splitting rule for ternary conditional expressions,
          when the test operand is false."
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
  :enable (exec-expr-pure
           test*
           (:e tau-system)))

(defruled exec-expr-pure-when-cond
  :short "Opener splitting rule for ternary conditional expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This produces @(tsee exec-expr-pure-apconvert-no-object)."))
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
           exec-expr-pure-apconvert-no-object
           (:e tau-system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *exec-expr-pure-openers*
  :short "List of opener rules for @(tsee exec-expr-pure)."
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
    exec-expr-pure-when-binary-logand-and-true
    exec-expr-pure-when-binary-logand-and-false
    exec-expr-pure-when-binary-logand
    exec-expr-pure-when-binary-logor-and-true
    exec-expr-pure-when-binary-logor-and-false
    exec-expr-pure-when-binary-logor
    exec-expr-pure-when-cond-and-true
    exec-expr-pure-when-cond-and-false
    exec-expr-pure-when-cond
    sint-from-boolean-with-error-when-booleanp-and-true
    sint-from-boolean-with-error-when-booleanp-and-false
    sint-from-boolean-with-error-when-booleanp
    exec-expr-pure-apconvert-no-object-open))

(defval *exec-expr-pure-openers-split*
  :short "List of opener splitting rules for @(tsee exec-expr-pure)."
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
    exec-expr-pure-when-cond
    sint-from-boolean-with-error-when-booleanp
    exec-expr-pure-apconvert-no-object-open))

(defval *exec-expr-pure-openers-nosplit*
  :short "List of opener non-splitting rules for @(tsee exec-expr-pure)."
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
    exec-expr-pure-when-binary-logand-and-true
    exec-expr-pure-when-binary-logand-and-false
    exec-expr-pure-when-binary-logor-and-true
    exec-expr-pure-when-binary-logor-and-false
    exec-expr-pure-when-cond-and-true
    exec-expr-pure-when-cond-and-false
    sint-from-boolean-with-error-when-booleanp-and-true
    sint-from-boolean-with-error-when-booleanp-and-false
    exec-expr-pure-apconvert-no-object-open))

;;;;;;;;;;;;;;;;;;;;

(make-event
 `(def-ruleset exec-expr-pure-openers
    ',*exec-expr-pure-openers*))

(make-event
 `(def-ruleset exec-expr-pure-openers-split
    ',*exec-expr-pure-openers-split*))

(make-event
 `(def-ruleset exec-expr-pure-openers-nosplit
    ',*exec-expr-pure-openers-nosplit*))
