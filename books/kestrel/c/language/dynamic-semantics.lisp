; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "operations")
(include-book "computation-states")
(include-book "function-environments")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dynamic-semantics
  :parents (language)
  :short "A dynamic semantics of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "We distinguish between pure (i.e. side-effect-free) expressions
     and expressions that may have side effects.
     We allow the latter to appear only in certain parts of statements,
     and we put restrictions to ensure a predictable order of evaluation.
     Pure expressions may be evaluated in any order;
     we evaluate them left to right.")
   (xdoc::p
    "We formalize a big-step operational interpretive semantics.
     To ensure the termination of the ACL2 mutually recursive functions
     that formalize the execution of statements, function calls, etc.,
     these ACL2 functions take a limit on the depth of the recursive calls,
     which ends the recursion with an error when it reaches 0,
     which is decremented at each recursive call,
     and which is used as termination measure.
     Thus, a proof of total correctness
     (i.e. the code terminates and produces correct results)
     involves showing the existence of sufficiently large limit values,
     while a proof of partial correctness
     (i.e. the code produces correct results if it terminates)
     is relativized to the limit value not running out.
     The limit is an artifact of the formalization;
     it has no explicit counterpart in the execution state of the C code.")
   (xdoc::p
    "The current definition of this dynamic semantics
     may not be completely accurate in terms of
     execution of arbitrary C in the covered subset of C,
     in particular in the treatment of arrays.
     However, it is accurate for our current uses
     (namely, supporting proof generation in "
    (xdoc::seetopic "atc" "ATC")
    ". This dynamic semantics is work in progress;
     we plan to make it completely accurate
     for all the covered subset of C."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define apconvert-expr-value ((eval expr-valuep))
  :returns (eval1 expr-value-resultp)
  :short "Array-to-pointer conversion [C17:6.3.2.1/3] on expression values."
  :long
  (xdoc::topstring
   (xdoc::p
    "Under most circumstances,
     an array is converted to a pointer to the first element of the array
     [C17:6.3.2.1/3];
     indeed, arrays are used like pointers most of the time.")
   (xdoc::p
    "This cannot be formalized on values: we need expression values,
     because we need to know where the array is in storage
     (i.e. we need to know its object designator),
     so that we can construct a pointer to it.
     Non-array expression values are left unchanged.
     If the array has no object designator, we return an error;
     this should actually never happen (at least in our model),
     but we need to formulate and prove an invariant
     saying that every array expression value includes an object designator,
     which at the moment we do not have.")
   (xdoc::p
    "We make a slight approximation for now:
     instead of returning a pointer to the first element of the array,
     we return a pointer to the array.
     This is adequate in our current formalization of our C subset,
     because of the way we formalize array indexing
     (e.g. see @(tsee exec-arrsub));
     however, we plan to make this, and array indexing,
     consistent with full C.")
   (xdoc::p
    "The static counterpart of this is @(tsee apconvert-type)."))
  (b* (((expr-value eval) eval))
    (if (value-case eval.value :array)
        (if eval.object
            (make-expr-value
             :value (make-value-pointer
                     :core (pointer-valid eval.object)
                     :reftype (value-array->elemtype eval.value))
             :object nil)
          (error (list :array-without-designator (expr-value-fix eval))))
      (expr-value-fix eval)))

  ///

  (defruled c::apconvert-expr-value-when-not-array
    (implies (not (equal (c::value-kind (c::expr-value->value eval))
                         :array))
             (equal (c::apconvert-expr-value eval)
                    (c::expr-value-fix eval)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-iconst ((ic iconstp))
  :returns (val value-resultp)
  :short "Evaluate an integer constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to [C17:6.4.4.1/5]:
     based on the suffixes and the base,
     we find the first type that suffices to represent the value,
     in the lists indicated in the table,
     and we return the value of the found type.
     If the value is too large, we return an error.")
   (xdoc::p
    "This is the dynamic counterpart of @(tsee check-iconst)."))
  (b* (((iconst ic) ic)
       (error (error (list :iconst-out-of-range (iconst-fix ic)))))
    (if ic.unsignedp
        (iconst-length-case
         ic.length
         :none (cond ((uint-integerp ic.value) (value-uint ic.value))
                     ((ulong-integerp ic.value) (value-ulong ic.value))
                     ((ullong-integerp ic.value) (value-ullong ic.value))
                     (t error))
         :long (cond ((ulong-integerp ic.value) (value-ulong ic.value))
                     ((ullong-integerp ic.value) (value-ullong ic.value))
                     (t error))
         :llong (cond ((ullong-integerp ic.value) (value-ullong ic.value))
                      (t error)))
      (iconst-length-case
       ic.length
       :none (if (iconst-base-case ic.base :dec)
                 (cond ((sint-integerp ic.value) (value-sint ic.value))
                       ((slong-integerp ic.value) (value-slong ic.value))
                       ((sllong-integerp ic.value) (value-sllong ic.value))
                       (t error))
               (cond ((sint-integerp ic.value) (value-sint ic.value))
                     ((uint-integerp ic.value) (value-uint ic.value))
                     ((slong-integerp ic.value) (value-slong ic.value))
                     ((ulong-integerp ic.value) (value-ulong ic.value))
                     ((sllong-integerp ic.value) (value-sllong ic.value))
                     ((ullong-integerp ic.value) (value-ullong ic.value))
                     (t error)))
       :long (if (iconst-base-case ic.base :dec)
                 (cond ((slong-integerp ic.value) (value-slong ic.value))
                       ((sllong-integerp ic.value) (value-sllong ic.value))
                       (t error))
               (cond ((slong-integerp ic.value) (value-slong ic.value))
                     ((ulong-integerp ic.value) (value-ulong ic.value))
                     ((sllong-integerp ic.value) (value-sllong ic.value))
                     ((ullong-integerp ic.value) (value-ullong ic.value))
                     (t error)))
       :llong (if (iconst-base-case ic.base :dec)
                  (cond ((sllong-integerp ic.value) (value-sllong ic.value))
                        (t error))
                (cond ((sllong-integerp ic.value) (value-sllong ic.value))
                      ((ullong-integerp ic.value) (value-ullong ic.value))
                      (t error)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-const ((c constp))
  :returns (val value-resultp)
  :short "Evaluate a constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only support the evaluation of integer constants for now."))
  (const-case c
              :int (eval-iconst c.get)
              :float (error :exec-const-float)
              :enum (error :exec-const-enum)
              :char (error :exec-const-char)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-const ((c constp))
  :returns (eval expr-value-resultp)
  :short "Execute a constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just a wrapper of @(tsee eval-const)
     that returns an expression value (with no object designator),
     to formalize the execution of the constant as an expression."))
  (b* ((val (eval-const c))
       ((when (errorp val)) val))
    (make-expr-value :value val :object nil))
  :guard-hints (("Goal" :in-theory (enable (:e tau-system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-ident ((id identp) (compst compustatep))
  :returns (eval expr-value-resultp)
  :short "Execute a variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "We obtain the object designator of the variable, propagating errors.
     We read the value from the object designator,
     which is guaranteed to work as proved in @(tsee read-object)."))
  (b* ((objdes (objdesign-of-var id compst))
       ((unless objdes) (error (list :no-object-designator (ident-fix id))))
       (val (read-object objdes compst)))
    (make-expr-value :value val :object objdes))
  :guard-hints
  (("Goal" :in-theory (enable valuep-of-read-object-of-objdesign-of-var))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-address ((arg expr-valuep))
  :returns (eval expr-value-resultp)
  :short "Execute @('&') on an expression value [C17:6.5.3.2/1] [C17:6.5.3.2/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The expression that the operator @('&') is applied to
     must be an lvalue [C17:6.5.3.2/1],
     which in our formalization means that
     we apply this operator to an expression value (returned by the lvalue).
     The expression value must contain an object designator,
     because otherwise the argument expression was not an lvalue.
     We extract the object designator and we return a pointer value,
     whose type is determined by the value in the expression value.
     We return the value as an expression value without object designator,
     for uniformity with other ACL2 functions for expression execution.")
   (xdoc::p
    "Here we formalize the actual application of @('&')
     to the expression value returned by an expression.
     We do not formalize here the fact that @('&*E') is the same as @('E')
     in the sense in that case neither @('*') nor @('&') are evaluated
     [C17:6.5.3.2/4], whether the @('*') is explicit or implied by @('[]');
     we formalize that elsewhere,
     while here we assume that the argument expression of @('&')
     has been evaluated (because the special cases above do not hold),
     and the resulting expression value is passed here.")
   (xdoc::p
    "We perform no array-to-pointer conversion,
     because that conversion is not performed for the operand of @('&')
     [C17:6.3.2.1/3]."))
  (b* ((objdes (expr-value->object arg))
       ((unless objdes)
        (error (list :not-lvalue-result (expr-value-fix arg))))
       (type (type-of-value (expr-value->value arg))))
    (make-expr-value
     :value (make-value-pointer :core (pointer-valid objdes)
                                :reftype type)
     :object nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-indir ((arg expr-valuep) (compst compustatep))
  :returns (eval expr-value-resultp)
  :short "Execute @('*') on an expression value [C17:6.5.3.2/2] [C17:6.5.3.2/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "First we perform array-to-pointer conversion [C17:5.3.2.1/3].
     The value must be a pointer.
     If the pointer is not valid, it is an error.
     Otherwise, we read the object designated by the object designator,
     which is a value,
     and we return it as an expression value,
     taking the object designator from the pointer value."))
  (b* ((arg (apconvert-expr-value arg))
       ((when (errorp arg)) arg)
       (val (expr-value->value arg))
       ((unless (value-case val :pointer))
        (error (list :non-pointer-dereference (expr-value-fix arg))))
       ((unless (value-pointer-validp val))
        (error (list :invalid-pointer-dereference (expr-value-fix arg))))
       (objdes (value-pointer->designator val))
       (*val (read-object objdes compst))
       ((when (errorp *val)) *val))
    (make-expr-value :value *val :object objdes))
  :guard-hints (("Goal" :in-theory (enable (:e tau-system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-unary ((op unopp) (arg valuep))
  :guard (unop-nonpointerp op)
  :returns (val value-resultp)
  :short "Evaluate a unary operation that does not involve pointers,
          on a value, returning a value."
  (case (unop-kind op)
    (:plus (plus-value arg))
    (:minus (minus-value arg))
    (:bitnot (bitnot-value arg))
    (:lognot (lognot-value arg))
    (t (error (impossible))))
  :guard-hints (("Goal" :in-theory (enable unop-nonpointerp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-unary ((op unopp) (arg expr-valuep) (compst compustatep))
  :returns (eval expr-value-resultp)
  :short "Execute a unary operation on an expression value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This ACL2 function
     wraps @(tsee eval-unary) to take and return expression values,
     and covers the remaining two unary operators @('&') and @('*').
     Note that the only unary operator that needs an expression value
     (as opposed to just a value) is @('&'),
     and that only unary operator that returns an expression value
     (as opposed to just a value) is @('*').
     The other four unary operators only operate on values,
     as factored in @(tsee eval-unary).")
   (xdoc::p
    "Before calling @(tsee eval-unary),
     we perform array-to-pointer conversion [C17:5.3.2.1/3].
     The functions handle @('&') and @('*')
     perform that conversion as needed
     (specifically, @('&') does not, while @('*') does)."))
  (case (unop-kind op)
    (:address (exec-address arg))
    (:indir (exec-indir arg compst))
    (t (b* ((arg (apconvert-expr-value arg))
            ((when (errorp arg)) arg)
            (val (eval-unary op (expr-value->value arg)))
            ((when (errorp val)) val))
         (make-expr-value :value val :object nil))))
  :guard-hints (("Goal" :in-theory (enable unop-nonpointerp (:e tau-system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-binary-strict-pure ((op binopp) (arg1 valuep) (arg2 valuep))
  :guard (and (binop-strictp op)
              (binop-purep op))
  :returns (val value-resultp)
  :short "Evaluate a binary expression with a strict pure operator,
          on two values, returning a value."
  (case (binop-kind op)
    (:mul (mul-values arg1 arg2))
    (:div (div-values arg1 arg2))
    (:rem (rem-values arg1 arg2))
    (:add (add-values arg1 arg2))
    (:sub (sub-values arg1 arg2))
    (:shl (shl-values arg1 arg2))
    (:shr (shr-values arg1 arg2))
    (:lt (lt-values arg1 arg2))
    (:gt (gt-values arg1 arg2))
    (:le (le-values arg1 arg2))
    (:ge (ge-values arg1 arg2))
    (:eq (eq-values arg1 arg2))
    (:ne (ne-values arg1 arg2))
    (:bitand (bitand-values arg1 arg2))
    (:bitxor (bitxor-values arg1 arg2))
    (:bitior (bitior-values arg1 arg2))
    (t (error (impossible))))
  :guard-hints (("Goal" :in-theory (enable binop-strictp binop-purep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-binary-strict-pure ((op binopp)
                                 (arg1 expr-valuep)
                                 (arg2 expr-valuep))
  :guard (and (binop-strictp op)
              (binop-purep op))
  :returns (dval expr-value-resultp)
  :short "Execute a strict pure binary operation on expression values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This ACL2 function wraps @(tsee eval-binary-strict-pure)
     to take and return expression values.")
   (xdoc::p
    "First we perform array-to-pointer conversion [C17:5.3.2.1/3],
     on both operands."))
  (b* ((arg1 (apconvert-expr-value arg1))
       ((when (errorp arg1)) arg1)
       (arg2 (apconvert-expr-value arg2))
       ((when (errorp arg2)) arg2)
       (val1 (expr-value->value arg1))
       (val2 (expr-value->value arg2))
       (val (eval-binary-strict-pure op val1 val2))
       ((when (errorp val)) val))
    (make-expr-value :value val :object nil))
  :guard-hints (("Goal" :in-theory (enable (:e tau-system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-cast ((tyname tynamep) (arg valuep))
  :returns (val value-resultp)
  :short "Evaluate a type cast on a value."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only support casts between integer types.
     None involving pointers.")
   (xdoc::p
    "We reject casts to @('void'),
     because a scalar type is required [C17:6.5.4/2]."))
  (b* ((type (tyname-to-type tyname))
       ((unless (type-nonchar-integerp type))
        (error (list :cast-not-supported :to type)))
       ((unless (value-integerp arg))
        (error (list :cast-not-supported :from (value-fix arg))))
       (err (error (list :cast-undefined :from (value-fix arg) :to type)))
       (val (convert-integer-value arg type))
       ((when (errorp val)) err))
    val))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-cast ((tyname tynamep) (arg expr-valuep))
  :returns (eval expr-value-resultp)
  :short "Execute a type cast on an expression value."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform array-to-pointer conversion [C17:5.3.2.1/3] on the operand."))
  (b* ((arg (apconvert-expr-value arg))
       ((when (errorp arg)) arg)
       (val (eval-cast tyname (expr-value->value arg)))
       ((when (errorp val)) val))
    (make-expr-value :value val :object nil))
  :guard-hints (("Goal" :in-theory (enable (:e tau-system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-arrsub ((arr expr-valuep) (sub expr-valuep) (compst compustatep))
  :returns (eval expr-value-resultp)
  :short "Execute the array subscripting operation on expression values."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform array-to-pointer conversion [C17:5.3.2.1/3]
     on both operands.")
   (xdoc::p
    "The first operand must be a valid pointer to an array;
     the pointer must have the element type of the array.
     The second operand must be an integer value (of any integer type).
     The resulting index must be in range for the array,
     and the indexed element is returned as result,
     as an expression value whose object designator is for the array element.")
   (xdoc::p
    "This semantics is an approximation of the real one in C,
     but it is adequate to our C subset.
     In full C, an array subscripting expression @('a[i]')
     is equivalent to @('*(a+i)'),
     so @('a') should be really a pointer to the first element of the array,
     to which the index @('i') is added to obtain a pointer to the element.
     In our C subset, we have limited support for pointers,
     in particular there is no explicit pointer arithmetic,
     other than implicitly as array subscripting.
     So we have our own treatment of array subscipting here,
     in which the pointer is assumed to be to the array (not the first element),
     and the index is just used to obtain the element.
     This treatment is equivalent to the real one for our current purposes.")
   (xdoc::p
    "Note that, in full C, pointers are almost never to arrays,
     but rather they are to elements of arrays.
     The only way to get a pointer to an array as such is
     via @('&a') when @('a') is an array object name;
     except for this case, and for the case of an argument to @('sizeof'),
     as well as for string literals (currently not in our C subset),
     an array is always converted to a pointer to its first element
     [C17:6.3.2.1/3].")
   (xdoc::p
    "In any case, we plan to make our formal semantics
     more consistent with full C in the treatment of arrays."))
  (b* ((arr (apconvert-expr-value arr))
       ((when (errorp arr)) arr)
       (arr (expr-value->value arr))
       ((unless (value-case arr :pointer))
        (error (list :mistype-arrsub
                     :required :pointer
                     :supplied (type-of-value arr))))
       ((unless (value-pointer-validp arr))
        (error (list :invalid-pointer arr)))
       (objdes (value-pointer->designator arr))
       (reftype (value-pointer->reftype arr))
       (array (read-object objdes compst))
       ((when (errorp array))
        (error (list :array-not-found arr (compustate-fix compst))))
       ((unless (value-case array :array))
        (error (list :not-array arr (compustate-fix compst))))
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
       (elem-objdes (make-objdesign-element :super objdes :index index)))
    (make-expr-value :value val :object elem-objdes))
  :guard-hints (("Goal" :in-theory (enable (:e tau-system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-member ((str expr-valuep) (mem identp))
  :returns (eval expr-value-resultp)
  :short "Execute a structure member operation on an expression value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for the @('.') operator.
     We perform array-to-pointer conversion [C17:6.3.2.1/3] on the operand.
     The resulting operand must be a structure
     (it actually makes no difference whether we make this check
     before or after the array-to-pointer conversion,
     but we maintain the uniformity of always performing the conversion).
     The named member must be in the structure.
     The value associated to the member is returned.")
   (xdoc::p
    "If the structure expression value has an object designator,
     we return an expression value with the object designator
     obtained by adding the member to the one for the structure.
     If there is no object designator in the input,
     there is none in the output."))
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
                        (make-objdesign-member :super objdes-str :name mem))))
    (make-expr-value :value val-mem :object objdes-mem))
  :guard-hints (("Goal" :in-theory (enable (:e tau-system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-memberp ((str expr-valuep) (mem identp) (compst compustatep))
  :returns (eval expr-value-resultp)
  :short "Execute a structure pointer member operation
          on an expression value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for the @('->') operator.
     We perform array-to-pointer conversion [C17:6.3.2.1/3] on the operand.
     The resulting operand must be a valid pointer to a structure
     of type consistent with the structure.
     The named member must be in the structure.
     The value associated to the member is returned.")
   (xdoc::p
    "We return an expression value whose object designator is obtained
     by adding the member to the object designator in the pointer."))
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
       (val (value-struct-read mem struct))
       ((when (errorp val)) val)
       (objdes-mem (make-objdesign-member :super objdes :name mem)))
    (make-expr-value :value val :object objdes-mem))
  :guard-hints (("Goal" :in-theory (enable (:e tau-system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-expr-pure ((e exprp) (compst compustatep))
  :returns (eval expr-value-resultp)
  :short "Execute a pure expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an error if we encounter a non-pure expression.
     While function calls do not necessarily have side effects,
     establishing that requires looking at the function.
     Thus, for simplicity, we regard function calls to be non-pure,
     i.e. we return an error if we encounter them here.")
   (xdoc::p
    "We also reject pre/post-increment/decrement expressions,
     which are obviously non-pure.")
   (xdoc::p
    "When executing a ternary expression,
     we drop any object designators
     from the second or third expression's execution,
     because ternary expressions are not lvalues
     [C17:6.5.15/4, footnote 113].")
   (xdoc::p
    "Recall that our C abstract syntax does not cover
     all the possible C expressions yet.
     Thus, we may extend this ACL2 function
     with support for more kinds of pure expressions in the future.")
   (xdoc::p
    "If no error occurs, none of the expressions has side effects.
     Thus, the order in which the subexpressions are evaluated does not matter:
     we just proceed left to right.")
   (xdoc::p
    "We plan to remove this function,
     after moving (and suitably generalizing) its code to @(tsee exec-expr).
     The plan is for @(tsee exec-expr) to support the execution of
     expressions that are not necessarily pure
     but still have a well-defined order of evaluation.
     (Further extending our dynamic semantics
     to support multiple possible orders of evaluation
     is something we will look at further in the future.)"))
  (b* ((e (expr-fix e)))
    (expr-case
     e
     :ident (exec-ident e.get compst)
     :const (exec-const e.get)
     :arrsub (b* ((arr (exec-expr-pure e.arr compst))
                  ((when (errorp arr)) arr)
                  (sub (exec-expr-pure e.sub compst))
                  ((when (errorp sub)) sub))
               (exec-arrsub arr sub compst))
     :call (error (list :non-pure-expr e))
     :member (b* ((str (exec-expr-pure e.target compst))
                  ((when (errorp str)) str))
               (exec-member str e.name))
     :memberp (b* ((str (exec-expr-pure e.target compst))
                   ((when (errorp str)) str))
                (exec-memberp str e.name compst))
     :postinc (error (list :non-pure-expr e))
     :postdec (error (list :non-pure-expr e))
     :preinc (error (list :non-pure-expr e))
     :predec (error (list :non-pure-expr e))
     :unary (b* ((arg (exec-expr-pure e.arg compst))
                 ((when (errorp arg)) arg))
              (exec-unary e.op arg compst))
     :cast (b* ((arg (exec-expr-pure e.arg compst))
                ((when (errorp arg)) arg))
             (exec-cast e.type arg))
     :binary (b* (((unless (binop-purep e.op)) (error (list :non-pure-expr e))))
               (case (binop-kind e.op)
                 (:logand
                  (b* ((arg1 (exec-expr-pure e.arg1 compst))
                       ((when (errorp arg1)) arg1)
                       (arg1 (apconvert-expr-value arg1))
                       ((when (errorp arg1)) arg1)
                       (test1 (test-value (expr-value->value arg1)))
                       ((when (errorp test1)) test1)
                       ((when (not test1))
                        (make-expr-value :value (value-sint 0) :object nil))
                       (arg2 (exec-expr-pure e.arg2 compst))
                       ((when (errorp arg2)) arg2)
                       (arg2 (apconvert-expr-value arg2))
                       ((when (errorp arg2)) arg2)
                       (test2 (test-value (expr-value->value arg2)))
                       ((when (errorp test2)) test2))
                    (if test2
                        (make-expr-value :value (value-sint 1) :object nil)
                      (make-expr-value :value (value-sint 0) :object nil))))
                 (:logor
                  (b* ((arg1 (exec-expr-pure e.arg1 compst))
                       ((when (errorp arg1)) arg1)
                       (arg1 (apconvert-expr-value arg1))
                       ((when (errorp arg1)) arg1)
                       (test1 (test-value (expr-value->value arg1)))
                       ((when (errorp test1)) test1)
                       ((when test1)
                        (make-expr-value :value (value-sint 1) :object nil))
                       (arg2 (exec-expr-pure e.arg2 compst))
                       ((when (errorp arg2)) arg2)
                       (arg2 (apconvert-expr-value arg2))
                       ((when (errorp arg2)) arg2)
                       (test2 (test-value (expr-value->value arg2)))
                       ((when (errorp test2)) test2))
                    (if test2
                        (make-expr-value :value (value-sint 1) :object nil)
                      (make-expr-value :value (value-sint 0) :object nil))))
                 (t (b* ((arg1 (exec-expr-pure e.arg1 compst))
                         ((when (errorp arg1)) arg1)
                         (arg2 (exec-expr-pure e.arg2 compst))
                         ((when (errorp arg2)) arg2))
                      (exec-binary-strict-pure e.op arg1 arg2)))))
     :cond (b* ((test (exec-expr-pure e.test compst))
                ((when (errorp test)) test)
                (test (apconvert-expr-value test))
                ((when (errorp test)) test)
                (test (test-value (expr-value->value test)))
                ((when (errorp test)) test))
             (if test
                 (b* ((eval (exec-expr-pure e.then compst))
                      ((when (errorp eval)) eval)
                      (eval (apconvert-expr-value eval))
                      ((when (errorp eval)) eval))
                   (change-expr-value eval :object nil))
               (b* ((eval (exec-expr-pure e.else compst))
                    ((when (errorp eval)) eval)
                    (eval (apconvert-expr-value eval))
                    ((when (errorp eval)) eval))
                 (change-expr-value eval :object nil))))))
  :measure (expr-count e)
  :hints (("Goal" :in-theory (enable o-p o< o-finp)))
  :verify-guards nil ; done below

  ///

  (defret expr-value-resultp-of-exec-expr-pure-forward
    (expr-value-resultp eval)
    :rule-classes ((:forward-chaining
                    :trigger-terms ((exec-expr-pure e compst)))))

  (verify-guards exec-expr-pure
    :hints (("Goal" :in-theory (enable binop-strictp (:e tau-system)))))

  (defruled not-call-when-exec-expr-pure-not-error
    (implies (not (errorp (exec-expr-pure expr compst)))
             (not (equal (expr-kind expr) :call)))
    :induct t)

  (defruled not-asg-when-exec-expr-pure-not-error
    (implies (not (errorp (exec-expr-pure expr compst)))
             (not (and (equal (expr-kind expr) :binary)
                       (equal (binop-kind (expr-binary->op expr)) :asg))))
    :induct t
    :enable binop-purep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-expr-pure-list ((es expr-listp) (compst compustatep))
  :returns (result
            value-list-resultp
            :hints (("Goal"
                     :induct t
                     :in-theory
                     (enable
                      valuep-when-value-resultp-and-not-errorp
                      value-listp-when-value-list-resultp-and-not-errorp))))
  :short "Execute a list of pure expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given that the expression have no side effects (if there is no error),
     the order of evaluation does not matter.
     Thus, we proceed left to right.")
   (xdoc::p
    "This ACL2 function is only used in situations
     in which we are interested in the values of the expressions,
     not their expression values (i.e. object designators, if any).
     Thus, we just return lists of values here.")
   (xdoc::p
    "In the situations in which this ACL2 function is used,
     we also need to perform array-to-pointer conversion [C17:6.3.2.1/3]."))
  (b* (((when (endp es)) nil)
       (eval (exec-expr-pure (car es) compst))
       ((when (errorp eval)) eval)
       (eval (apconvert-expr-value eval))
       ((when (errorp eval)) eval)
       (val (expr-value->value eval))
       (vals (exec-expr-pure-list (cdr es) compst))
       ((when (errorp vals)) vals))
    (cons val vals))
  :guard-hints (("Goal" :in-theory (enable (:e tau-system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-scope ((formals param-declon-listp) (actuals value-listp))
  :returns (result scope-resultp
                   :hints (("Goal"
                            :induct t
                            :in-theory
                            (enable scopep-when-scope-resultp-and-not-errorp))))
  :short "Initialize the variable scope for a function call."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through formal parameters and actual arguments,
     pairing them up into the scope.
     We return an error if they do not match in number or types,
     or if there are repeated parameters.
     Before the comparison,
     we adjust the parameter types
     and we perform array-to-pointer conversion on the argument types.")
   (xdoc::p
    "Prior to storing each actual, we remove its flexible array member, if any.
     See @(tsee remove-flexible-array-member)."))
  (b* ((formals (param-declon-list-fix formals))
       (actuals (value-list-fix actuals))
       ((when (endp formals))
        (if (endp actuals)
            nil
          (error (list :init-scope :extra-actuals actuals))))
       ((when (endp actuals))
        (error (list :init-scope :extra-formals formals)))
       (scope (init-scope (cdr formals) (cdr actuals)))
       ((when (errorp scope)) scope)
       (formal (car formals))
       (actual (car actuals))
       ((mv name tyname) (param-declon-to-ident+tyname formal))
       (formal-type (adjust-type (tyname-to-type tyname)))
       (actual-type (apconvert-type (type-of-value actual)))
       ((unless (equal formal-type actual-type))
        (error (list :formal-actual-mistype
                     :name name
                     :formal formal-type
                     :actual actual-type))))
    (if (omap::assoc name scope)
        (error (list :init-scope :duplicate-param name))
      (omap::update name (remove-flexible-array-member actual) scope)))
  :measure (len formals)
  :hints (("Goal" :in-theory (enable o-p
                                     o<
                                     o-finp
                                     endp
                                     cdr-of-param-declon-list-fix
                                     len)))
  :verify-guards nil ; done below
  ///
  (verify-guards init-scope
    :hints (("Goal" :in-theory (enable (:e tau-system))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-value-to-value ((type typep) (ival init-valuep))
  :returns (val value-resultp)
  :short "Turn an initialization value into a value of a given type."
  :long
  (xdoc::topstring
   (xdoc::p
    "Executing an initializer yields an initialization value,
     which determines a value for the object being initialized,
     as formalized by this ACL2 function.")
   (xdoc::p
    "If the initialization value consists of a single value,
     we require the value's type to match the given type,
     and we just return the underlying value.
     In our current C subset,
     it is always the case that the value is scalar, never aggregate.
     So, if the check on the type succeeds,
     it means that the given type is scalar too.")
   (xdoc::p
    "If the initialization value consists of a list of values,
     we require the given type to be an array type
     with either no size or size equal to the length of the list of values.
     We require all the values to have the array element type.
     We require that there is at least one value,
     since arrays cannot be empty in C.
     We create an array value from the values and return it."))
  (init-value-case
   ival
   :single (if (type-equiv (type-of-value ival.get) type)
               ival.get
             (error (list :init-value-mismatch
                          :required (type-fix type)
                          :supplied (init-value-fix ival))))
   :list (b* (((unless (type-case type :array))
               (error (list :init-value-type-mismatch
                            :required :array-type
                            :supplied (init-value-fix ival))))
              (elemtype (type-array->of type))
              ((unless (equal (type-list-of-value-list ival.get)
                              (repeat (len ival.get) elemtype)))
               (error (list :init-value-element-type-mismatch
                            :required elemtype
                            :supplied ival.get)))
              (size (type-array->size type))
              ((when (and size
                          (not (equal size (len ival.get)))))
               (error (list :init-value-size-mismatch
                            :required size
                            :supplied (len ival.get))))
              ((unless (consp ival.get))
               (error (list :init-value-empty-mismatch))))
           (make-value-array :elemtype elemtype :elements ival.get))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines exec
  :short "Mutually recursive functions for execution."
  :flag-local nil

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-fun ((fun identp)
                    (args value-listp)
                    (compst compustatep)
                    (fenv fun-envp)
                    (limit natp))
    :returns (mv (result value-option-resultp)
                 (new-compst compustatep))
    :parents (dynamic-semantics exec)
    :short "Execute a function on argument values."
    :long
    (xdoc::topstring
     (xdoc::p
      "We retrieve the information about the function from the environment.
       We initialize a scope with the argument values,
       and we push a frame onto the call stack.
       We execute the function body,
       which must return a result that matches the function's result type.
       We pop the frame and return the value of the function call as result."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
         (info (fun-env-lookup fun fenv))
         ((when (not info))
          (mv (error (list :function-undefined (ident-fix fun)))
              (compustate-fix compst)))
         ((fun-info info) info)
         (scope (init-scope info.params args))
         ((when (errorp scope)) (mv scope (compustate-fix compst)))
         (frame (make-frame :function fun :scopes (list scope)))
         (compst (push-frame frame compst))
         ((mv sval compst) (exec-block-item-list info.body
                                                  compst
                                                  fenv
                                                  (1- limit)))
         (compst (pop-frame compst))
         ((when (errorp sval)) (mv sval compst))
         (val? (stmt-value-case
                sval
                :none nil
                :return sval.value?))
         ((unless (equal (type-of-value-option val?)
                         (tyname-to-type info.result)))
          (mv (error (list :return-value-mistype
                           :required info.result
                           :supplied (type-of-value-option val?)))
              compst)))
      (mv val? compst))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-expr ((e exprp)
                     (compst compustatep)
                     (fenv fun-envp)
                     (limit natp))
    :returns (mv (eval expr-value-option-resultp)
                 (new-compst compustatep))
    :parents (dynamic-semantics exec)
    :short "Execute an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return an optional expression value,
       and a possibly updated computation state.
       The optional expression value is @('nil')
       for expressions that do not return a value or designate an object,
       e.g. calls of @('void') functions.")
     (xdoc::p
      "We support the execution of expressions whose order of evaluation
       is determined by [C17] or does not matter;
       we characterize this subset of the expressions conservatively,
       returning errors on expressions outside the characterization.
       As noted in @(tsee exec-expr-pure),
       we are in the process of moving the code from there to here,
       and we will eventually eliminate @(tsee exec-expr-pure);
       as we move the code here, we also generalize it
       in the sense of supporting the execution of more expressions,
       namely ones that are not pure but have
       a deterministic order of evaluation.")
     (xdoc::p
      "The code of this function starts by cases on expressions,
       but only covers some of the cases;
       the rest of the cases contain (some of) the old code of this function,
       which handles certain kinds of expressions.")
     (xdoc::p
      "Variables and constants are always deterministic,
       so they are supported in all cases.")
     (xdoc::p
      "If the expression is a function call,
       its arguments must be all pure expressions;
       if they were not, they might modify the function-valued expression.
       We execute the arguments and then the function.")
     (xdoc::p
      "A unary expression is always deterministic,
       because it has a single sub-expression.")
     (xdoc::p
      "If the expression is an assignment,
       the left-hand side must be a pure lvalue expression;
       if it were not pure,
       it could potentially change the value of the right-hand side,
       if evaluated before the right-hand side,
       so it is conservatively safe to require the left-hand side to be pure.
       We perform array-to-pointer conversion [C23:6.3.3.1]
       on the result of evaluating the left-hand side;
       this must yield an expression value with an object designator.
       The right-hand side must be a pure expression (lvalue or not),
       but if the left-hand side is just an identifier,
       then we allow the right-hand side to be any supported expression
       (we recursively call @(tsee exec-expr) on it).
       The latter relaxation is justified by the fact that,
       if the left-hand side is a variable,
       it the object that it designates is not affected
       by any side effect of the right-hand side
       (see @(see variable-resolution-preservation)):
       it is always the same variable,
       whose value may be affected by the right-hand side,
       but its value is not used for the assignment,
       as it is overwritten by the assignment.
       Array-to-pointer conversion [C23:6.3.3.1] is applied
       to the result of evaluating the right-hand side,
       which must return an expression value (not @('nil')).
       Note that the assignment itself is not an lvalue;
       its result is the value assigned by the assignment."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst))))
      (expr-case
       e
       :ident (mv (exec-ident e.get compst) (compustate-fix compst))
       :const (mv (exec-const e.get) (compustate-fix compst))
       :call (b* ((vals (exec-expr-pure-list e.args compst))
                  ((when (errorp vals)) (mv vals (compustate-fix compst)))
                  ((mv val? compst)
                   (exec-fun e.fun vals compst fenv (1- limit)))
                  ((when (errorp val?)) (mv val? compst)))
               (if val?
                   (mv (make-expr-value :value val? :object nil) compst)
                 (mv nil compst)))
       :unary (b* (((mv arg compst) (c::exec-expr e.arg compst fenv (1- limit)))
                   ((when (errorp arg)) (mv arg compst))
                   ((unless arg)
                    (mv (error (list :unary-void-expr e.arg)) compst)))
                (mv (exec-unary e.op arg compst) compst))
       :otherwise
       (b* (((when (expr-purep e))
             (mv (exec-expr-pure e compst) (compustate-fix compst)))
            ((when (and (expr-case e :binary)
                        (binop-case (expr-binary->op e) :asg)))
             (b* ((left (expr-binary->arg1 e))
                  (right (expr-binary->arg2 e))
                  (left-eval (exec-expr-pure left compst))
                  ((when (errorp left-eval))
                   (mv left-eval (compustate-fix compst)))
                  (left-eval (apconvert-expr-value left-eval))
                  ((when (errorp left-eval))
                   (mv left-eval (compustate-fix compst)))
                  (objdes (expr-value->object left-eval))
                  ((unless objdes)
                   (mv (error (list :not-lvalue left)) (compustate-fix compst)))
                  ((mv right-eval? compst)
                   (if (expr-case left :ident)
                       (exec-expr right compst fenv (1- limit))
                     (mv (exec-expr-pure right compst)
                         (compustate-fix compst))))
                  ((when (errorp right-eval?)) (mv right-eval? compst))
                  ((when (not right-eval?))
                   (mv (error (list :asg-void-expr right)) compst))
                  (right-eval right-eval?)
                  (right-eval (apconvert-expr-value right-eval))
                  ((when (errorp right-eval)) (mv right-eval compst))
                  (val (expr-value->value right-eval))
                  (compst/error (write-object objdes val compst))
                  ((when (errorp compst/error)) (mv compst/error compst))
                  (compst compst/error))
               (mv (make-expr-value :value val :object nil) compst))))
         (mv (error (list :expression-not-supported (expr-fix e)))
             (compustate-fix compst)))))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-stmt ((s stmtp)
                     (compst compustatep)
                     (fenv fun-envp)
                     (limit natp))
    :guard (> (compustate-frames-number compst) 0)
    :returns (mv (sval stmt-value-resultp)
                 (new-compst compustatep))
    :parents (dynamic-semantics exec)
    :short "Execute a statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we only support the execution of certain statements.")
     (xdoc::p
      "Since an expression statement discards
       the value returned by the expression (if any),
       there is no need to perform array-to-pointer conversion [C23:6.3.3.1].
       The fact that array-to-pointer conversion may return an error
       is just an artifact of our current model, which we plan to eliminate.")
     (xdoc::p
      "For a compound statement (i.e. a block),
       we enter a new (empty) scope prior to executing the block items,
       and we exit that scope after executing the block items.")
     (xdoc::p
      "An iteration statement forms a block [C17:6.8.5/5],
       so we must enter a new scope before it and exit the scope after it.
       We are currently not doing that for @('while') loops,
       but we plan to do that;
       at the moment it does not make a difference,
       given how we use the dynamic semantics."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
         (s (stmt-fix s)))
      (stmt-case
       s
       :labeled (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :compound (b* ((compst (enter-scope compst))
                      ((mv sval compst)
                       (exec-block-item-list s.items compst fenv (1- limit))))
                   (mv sval (exit-scope compst)))
       :expr (b* (((mv eval compst) (exec-expr s.get compst fenv (1- limit)))
                  ((when (errorp eval)) (mv eval compst)))
               (mv (stmt-value-none) compst))
       :null (mv (stmt-value-none) (compustate-fix compst))
       :if (b* ((test (exec-expr-pure s.test compst))
                ((when (errorp test)) (mv test (compustate-fix compst)))
                (test (apconvert-expr-value test))
                ((when (errorp test)) (mv test (compustate-fix compst)))
                (test (expr-value->value test))
                (test (test-value test))
                ((when (errorp test)) (mv test (compustate-fix compst))))
             (if test
                 (exec-stmt s.then compst fenv (1- limit))
               (mv (stmt-value-none) (compustate-fix compst))))
       :ifelse (b* ((test (exec-expr-pure s.test compst))
                    ((when (errorp test)) (mv test (compustate-fix compst)))
                    (test (apconvert-expr-value test))
                    ((when (errorp test)) (mv test (compustate-fix compst)))
                    (test (expr-value->value test))
                    (test (test-value test))
                    ((when (errorp test)) (mv test (compustate-fix compst))))
                 (if test
                     (exec-stmt s.then compst fenv (1- limit))
                   (exec-stmt s.else compst fenv (1- limit))))
       :switch (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :while (exec-stmt-while s.test s.body compst fenv (1- limit))
       :dowhile (b* ((compst (enter-scope compst))
                     ((mv sval compst)
                      (exec-stmt-dowhile s.body s.test compst fenv (1- limit)))
                     ((when (errorp sval)) (mv sval (exit-scope compst)))
                     (compst (exit-scope compst)))
                  (mv sval compst))
       :for (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :goto (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :continue (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :break (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :return (if (exprp s.value)
                   (b* (((mv eval? compst)
                         (exec-expr s.value compst fenv (1- limit)))
                        ((when (errorp eval?)) (mv eval? compst))
                        ((when (not eval?)) (mv (error (list :return-void-expr
                                                             s.value))
                                                compst))
                        (eval eval?)
                        (eval (apconvert-expr-value eval))
                        ((when (errorp eval)) (mv eval compst))
                        (val (expr-value->value eval)))
                     (mv (stmt-value-return val) compst))
                 (mv (stmt-value-return nil) (compustate-fix compst)))))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-stmt-while ((test exprp)
                           (body stmtp)
                           (compst compustatep)
                           (fenv fun-envp)
                           (limit natp))
    :guard (> (compustate-frames-number compst) 0)
    :returns (mv (sval stmt-value-resultp)
                 (new-compst compustatep))
    :parents (dynamic-semantics exec)
    :short "Execute a @('while') statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "First, we execute the test.
       If it yields a 0 scalar, we return a @('nil') value result,
       because it means that the loop completes,
       and execution can proceed with any code after the loop.
       Otherwise, we recursively execute the body.
       We should push and then pop a scope,
       because the body of a loop forms a block [C17:6.8.5/5];
       we plan to do that, but currently that makes no difference
       given how we are using our dynamic semantics of C.
       If the body terminates with a @('return'),
       we terminate the loop with the same result.
       If the body does not terminate with a @('return'),
       we re-execute the loop,
       by calling this ACL2 function recursively."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
         (test-eval (exec-expr-pure test compst))
         ((when (errorp test-eval)) (mv test-eval (compustate-fix compst)))
         (test-eval (apconvert-expr-value test-eval))
         ((when (errorp test-eval)) (mv test-eval (compustate-fix compst)))
         (test-val (expr-value->value test-eval))
         (continuep (test-value test-val))
         ((when (errorp continuep)) (mv continuep (compustate-fix compst)))
         ((when (not continuep)) (mv (stmt-value-none) (compustate-fix compst)))
         ((mv sval compst) (exec-stmt body compst fenv (1- limit)))
         ((when (errorp sval)) (mv sval compst))
         ((when (stmt-value-case sval :return)) (mv sval compst)))
      (exec-stmt-while test body compst fenv (1- limit)))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-stmt-dowhile ((body stmtp)
                             (test exprp)
                             (compst compustatep)
                             (fenv fun-envp)
                             (limit natp))
    :guard (> (compustate-frames-number compst) 0)
    :returns (mv (sval stmt-value-resultp)
                 (new-compst compustatep))
    :parents (dynamic-semantics exec)
    :short "Execute a @('do-while') statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "First, we execute the body,
       pushing and then popping a scope,
       because the body forms a block [C17:6.8.5/5].
       If the body terminates with a @('return'),
       we end the execution of the loop with the same result.
       Otherwise, we execute the test.
       If it yields a 0 scalar, the loop terminates execution,
       with a statement value indicating non-@('return') termination.
       Otherwise, we re-execute the loop,
       by calling this ACL2 function recursively."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
         (compst (enter-scope compst))
         ((mv sval compst) (exec-stmt body compst fenv (1- limit)))
         ((when (errorp sval)) (mv sval (exit-scope compst)))
         (compst (exit-scope compst))
         ((when (stmt-value-case sval :return)) (mv sval compst))
         (test-eval (exec-expr-pure test compst))
         ((when (errorp test-eval)) (mv test-eval compst))
         (test-eval (apconvert-expr-value test-eval))
         ((when (errorp test-eval)) (mv test-eval compst))
         (test-val (expr-value->value test-eval))
         (continuep (test-value test-val))
         ((when (errorp continuep)) (mv continuep compst))
         ((when (not continuep)) (mv (stmt-value-none) compst)))
      (exec-stmt-dowhile body test compst fenv (1- limit)))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-initer ((initer initerp)
                       (compst compustatep)
                       (fenv fun-envp)
                       (limit natp))
    :guard (> (compustate-frames-number compst) 0)
    :returns (mv (result init-value-resultp)
                 (new-compst compustatep))
    :parents (dynamic-semantics exec)
    :short "Execute an initializer."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the initializer consists of a single expression,
       the expression must be a function call or a pure expression.
       If it is a function call, it must return a value (not @('nil')).")
     (xdoc::p
      "If the initializer consists of a list of expressions,
       the expressions must be pure,
       to avoid ambiguities with the order of evaluation."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst))))
      (initer-case
       initer
       :single
       (b* (((mv eval compst) (exec-expr initer.get compst fenv (1- limit)))
            ((when (errorp eval)) (mv eval compst))
            ((when (not eval))
             (mv (error (list :void-initializer (initer-fix initer)))
                 compst))
            (eval (apconvert-expr-value eval))
            ((when (errorp eval)) (mv eval compst))
            (val (expr-value->value eval))
            (ival (init-value-single val)))
         (mv ival compst))
       :list
       (b* ((vals (exec-expr-pure-list initer.get compst))
            ((when (errorp vals)) (mv vals (compustate-fix compst)))
            (ival (init-value-list vals)))
         (mv ival (compustate-fix compst)))))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-obj-declon ((declon obj-declonp)
                           (compst compustatep)
                           (fenv fun-envp)
                           (limit natp))
    :guard (> (compustate-frames-number compst) 0)
    :returns (new-compst compustate-resultp)
    :parents (dynamic-semantics exec)
    :short "Execute an object declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now this is only for object declarations in blocks,
       consistently with the guard of this function.")
     (xdoc::p
      "We ensure that the declaration
       has no @('extern') storage class specifier
       (we do not support that in blocks),
       then we execute the initializer (which we require here),
       then we add the variable to the top scope of the top frame.
       The initializer value must have the same type as the variable,
       which automatically excludes the case of the variable being @('void'),
       since @(tsee type-of-value) never returns @('void')
       (under its guard).
       For now we disallow array objects;
       these will be supported later."))
    (b* (((when (zp limit)) (error :limit))
         ((mv var scspec tyname init?)
          (obj-declon-to-ident+scspec+tyname+init declon))
         ((unless (scspecseq-case scspec :none))
          (error :unsupported-storage-class-specifier))
         (type (tyname-to-type tyname))
         ((when (type-case type :array)) (error :unsupported-local-array))
         ((when (not init?)) (error :unsupported-no-initializer))
         (init init?)
         ((mv ival compst) (exec-initer init compst fenv (1- limit)))
         ((when (errorp ival)) ival)
         (val (init-value-to-value type ival))
         ((when (errorp val)) val))
      (create-var var val compst))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-block-item ((item block-itemp)
                           (compst compustatep)
                           (fenv fun-envp)
                           (limit natp))
    :guard (> (compustate-frames-number compst) 0)
    :returns (mv (sval stmt-value-resultp)
                 (new-compst compustatep))
    :parents (dynamic-semantics exec)
    :short "Execute a block item."
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst))))
      (block-item-case
       item
       :declon (b* ((new-compst
                     (exec-obj-declon item.get compst fenv (1- limit)))
                    ((when (errorp new-compst))
                     (mv new-compst (compustate-fix compst))))
                 (mv (stmt-value-none) new-compst))
       :stmt (exec-stmt item.get compst fenv (1- limit))))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-block-item-list ((items block-item-listp)
                                (compst compustatep)
                                (fenv fun-envp)
                                (limit natp))
    :guard (> (compustate-frames-number compst) 0)
    :returns (mv (sval stmt-value-resultp)
                 (new-compst compustatep))
    :parents (dynamic-semantics exec)
    :short "Execute a list of block items."
    :long
    (xdoc::topstring
     (xdoc::p
      "We thread the computation state through the block items."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
         ((when (endp items)) (mv (stmt-value-none) (compustate-fix compst)))
         ((mv sval compst) (exec-block-item (car items) compst fenv (1- limit)))
         ((when (errorp sval)) (mv sval compst))
         ((when (stmt-value-case sval :return)) (mv sval compst)))
      (exec-block-item-list (cdr items) compst fenv (1- limit)))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :prepwork ((local
              (in-theory
               (enable
                value-optionp-when-value-option-resultp-and-not-errorp
                compustatep-when-compustate-resultp-and-not-errorp
                fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable o-p o< o-finp nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :returns-hints (("Goal" :in-theory (enable (:e tau-system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below
  ///

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual compustate-frames-number-of-exec
    (defret compustate-frames-number-of-exec-fun
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :fn exec-fun)
    (defret compustate-frames-number-of-exec-expr
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :fn exec-expr)
    (defret compustate-frames-number-of-exec-stmt
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-stmt)
    (defret compustate-frames-number-of-exec-stmt-while
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-stmt-while)
    (defret compustate-frames-number-of-exec-stmt-dowhile
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-stmt-dowhile)
    (defret compustate-frames-number-of-exec-initer
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-initer)
    (defret compustate-frames-number-of-exec-block-item
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-block-item)
    (defret compustate-frames-number-of-exec-obj-declon
      (implies (compustatep new-compst)
               (equal (compustate-frames-number new-compst)
                      (compustate-frames-number compst)))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-obj-declon)
    (defret compustate-frames-number-of-exec-block-item-list
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-block-item-list)
    :hints (("Goal"
             :in-theory (enable len (:e tau-system))
             :expand ((exec-fun fun args compst fenv limit)
                      (exec-expr e compst fenv limit)
                      (exec-stmt s compst fenv limit)
                      (exec-initer initer compst fenv limit)
                      (exec-obj-declon declon compst fenv limit)
                      (exec-block-item item compst fenv limit)
                      (exec-block-item-list items compst fenv limit)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual compustate-scopes-numbers-of-exec
    (defret compustate-scopes-numbers-of-exec-fun
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :rule-classes nil
      :fn exec-fun)
    (defret compustate-scopes-numbers-of-exec-expr
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :fn exec-expr)
    (defret compustate-scopes-numbers-of-exec-stmt
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-stmt)
    (defret compustate-scopes-numbers-of-exec-stmt-while
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-stmt-while)
    (defret compustate-scopes-numbers-of-exec-stmt-dowhile
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-stmt-dowhile)
    (defret compustate-scopes-numbers-of-exec-initer
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-initer)
    (defret compustate-scopes-numbers-of-exec-obj-declon
      (implies (compustatep new-compst)
               (equal (compustate-scopes-numbers new-compst)
                      (compustate-scopes-numbers compst)))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-obj-declon)
    (defret compustate-scopes-numbers-of-exec-block-item
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-block-item)
    (defret compustate-scopes-numbers-of-exec-block-item-list
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-block-item-list)
    :hints (("Goal"
             :in-theory (enable len (:e tau-system))
             :expand ((exec-fun fun args compst fenv limit)
                      (exec-expr e compst fenv limit)
                      (exec-stmt s compst fenv limit)
                      (exec-stmt-while test body compst fenv limit)
                      (exec-initer initer compst fenv limit)
                      (exec-obj-declon declon compst fenv limit)
                      (exec-block-item item compst fenv limit)
                      (exec-block-item-list items compst fenv limit)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards exec-fun
    :hints
    (("Goal"
      :in-theory
      (enable
       (:e tau-system)
       len
       expr-value-optionp-when-expr-value-option-resultp-and-not-errorp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual exec
    :hints (("Goal" :in-theory (enable nfix)))))
