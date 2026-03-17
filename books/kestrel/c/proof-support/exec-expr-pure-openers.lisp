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

(include-book "../representation/integers")

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
     is returned, based on the boolean."))
  (if (errorp test)
      test
    (if test
        (expr-value (sint-from-integer 1) nil)
      (expr-value (sint-from-integer 0) nil)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move here material from ../atc/symbolic-execution-rules/exec-expr-pure.lisp
