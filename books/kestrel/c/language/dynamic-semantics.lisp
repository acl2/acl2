; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "operations")
(include-book "computation-states")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dynamic-semantics
  :parents (language)
  :short "A dynamic semantics of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "We are in the process of reformulating and moving code from
     @('../atc/execution.lisp') to this file.")
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
     it has no explicit counterpart in the execution state of the C code."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-iconst ((ic iconstp))
  :returns (result value-resultp)
  :short "Execute an integer constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to [C:6.4.4.1/5]:
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
                      (t error))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-const ((c constp))
  :returns (result value-resultp)
  :short "Execute a constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only support the execution of integer constants for now."))
  (const-case c
              :int (exec-iconst c.get)
              :float (error :exec-const-float)
              :enum (error :exec-const-enum)
              :char (error :exec-const-char))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-ident ((id identp) (compst compustatep))
  :returns (result value-resultp)
  :short "Execute a variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read the variable's value (if any) from the computation state.
     If the value is an array, we return a pointer value for the array.
     As explained in @(tsee exec-arrsub),
     our treatment of pointers and arrays differs slightly from full C,
     but leads to equivalent results in our C subset.
     This is essentially like an array-to-pointer conversion,
     but with the pointer pointing to the whole array
     instead of the first element,
     and with the pointer type being the array element type.
     The object designator is just the variable:
     currently @(tsee exec-block-item) prohibits local arrays,
     so a variable that contains an array can only be a global one.
     All of this will be properly generalized eventually,
     to bring things more in line with full C."))
  (b* ((val (read-var id compst))
       ((when (errorp val)) val))
    (if (value-case val :array)
        (make-value-pointer :designator? (objdesign-variable id)
                            :reftype (value-array->elemtype val))
      val))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-unary ((op unopp) (arg valuep))
  :returns (result value-resultp)
  :short "Execute a unary operation."
  (unop-case op
             :address (error :todo)
             :indir (error :todo)
             :plus (plus-value arg)
             :minus (minus-value arg)
             :bitnot (bitnot-value arg)
             :lognot (lognot-value arg))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-binary-strict-pure ((op binopp) (arg1 valuep) (arg2 valuep))
  :guard (and (binop-strictp op)
              (binop-purep op))
  :returns (result value-resultp)
  :short "Execute a binary expression with a strict pure operator."
  :long
  (xdoc::topstring
   (xdoc::p
    "These operators are pure,
     so we just return a value as result (if there is no error)."))
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
  :guard-hints (("Goal" :in-theory (enable binop-strictp binop-purep)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-cast ((tyname tynamep) (arg valuep))
  :returns (result value-resultp)
  :short "Execute a cast expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only support casts between integer types.
     None involving pointers.")
   (xdoc::p
    "We reject casts to @('void'),
     because a scalar type is required [C:6.5.4/2]."))
  (b* ((type (tyname-to-type tyname))
       ((unless (type-nonchar-integerp type))
        (error (list :cast-not-supported :to type)))
       ((unless (value-integerp arg))
        (error (list :cast-not-supported :from (value-fix arg))))
       (err (error (list :cast-undefined :from (value-fix arg) :to type)))
       (val (convert-integer-value arg type))
       ((when (errorp val)) err))
    val)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-arrsub ((arr valuep) (sub valuep) (compst compustatep))
  :returns (result value-resultp)
  :short "Execute an array subscripting expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first operand must be a non-null pointer to an array;
     the pointer must have the element type of the array.
     The second operand must be an integer value (of any integer type).
     The resulting index must be in range for the array,
     and the indexed element is returned as result.")
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
     So we have our own treatment of array subscipting,
     in which the pointer is assumed to be to the array (not the first element),
     and the index is just used to obtain the element
     (note also that we always return values when evaluating expressions,
     we never return object designators for now).
     This treatment is equivalent to the real one for our purposes.
     Note also that, in full C, the type of the pointer to the array
     should be the array type, not the element type.
     But again, we are somewhat pretending that the pointer to the array
     is a pointer to the first element,
     which justifies the type of the pointer as the array element type.
     Note that, in full C, pointers are almost never to arrays,
     but rather they are to elements of arrays.
     The only way to get a pointer to an array as such is
     via @('&a') when @('a') is an array object name;
     except for this case, and for the case of an argument to @('sizeof'),
     as well as for string literals (currently not in our C subset),
     an array is always converted to a pointer to its first element
     [C:6.3.2.1/3]."))
  (b* (((unless (value-case arr :pointer))
        (error (list :mistype-arrsub
                     :required :pointer
                     :supplied (type-of-value arr))))
       ((when (value-pointer-nullp arr)) (error (list :null-pointer)))
       (objdes (value-pointer->designator arr))
       (reftype (value-pointer->reftype arr))
       (array (read-object objdes compst))
       ((when (errorp array))
        (error (list :array-not-found (value-fix arr) (compustate-fix compst))))
       ((unless (value-case array :array))
        (error (list :not-array (value-fix arr) (compustate-fix compst))))
       ((unless (equal reftype (value-array->elemtype array)))
        (error (list :mistype-array-read
                     :pointer reftype
                     :array (value-array->elemtype array))))
       ((unless (value-integerp sub)) (error
                                       (list :mistype-array :index
                                             :required :integer
                                             :supplied (type-of-value sub))))
       (index (value-integer->get sub))
       ((when (< index 0)) (error (list :negative-array-index
                                        :pointer (value-fix arr)
                                        :array array
                                        :index (value-fix sub)))))
    (value-array-read index array))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-member ((str valuep) (mem identp))
  :returns (result value-resultp)
  :short "Execute a structure member expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for the @('.') operator.
     The operand must be a structure.
     The named member must be in the structure.
     The value associated to the member is returned."))
  (b* (((unless (value-case str :struct))
        (error (list :mistype-member
                     :required :struct
                     :supplied (type-of-value str)))))
    (value-struct-read mem str))
  :hooks (:fix))
