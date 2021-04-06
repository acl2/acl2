; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "integer-values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-integer-operations
  :parents (atc-dynamic-semantics)
  :short "C integer operations for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define ACL2 functions that model C operations on integers.
     For now we define operations for (signed) integers only,
     but we will cover the unsigned integers soon as well.
     We only cover standard unsigned and signed integers (except @('_Bool').")
   (xdoc::p
    "As explained below, it suffices to introduce operations
     on integers of rank equal to or higher than @('int').")
   (xdoc::p
    "We introduce functions @('<type>-const')
     to construct integer constants.
     Following [C:6.4.4.1], these have non-negative values
     and may have only certain integer types,
     namely those with the same rank as @('int') or higher.
     Each takes a natural number as argument,
     which the guard further constrains to be representable in the type.")
   (xdoc::p
    "We introduce functions @('<type>-nonzerop')
     to turn integers into ACL2 booleans,
     i.e. to test whether the integers are not zero.
     These are used to represent shallowly embedded tests.
     Note that promoting [C:6.3.1.1/2] the integer arguments
     does not affect the result,
     so there is no need to define functions for
     types of rank lower than @('int').")
   (xdoc::p
    "We introduce one function @(tsee sint01)
     to turn ACL2 booleans into the @('int') 0 or 1 (for false and true).
     This function is used in the ACL2 representation of
     non-strict C conjunctions @('&&') and disjunctions @('||'),
     which always return @('int') 0 or 1 [C:6.5.13/3] [C:6.5.14/3].")
   (xdoc::p
    "We introduce functions for the unary and binary operators.
     For all the unary integer operators except @('!'),
     C promotes the operands [C:6.3.1.1/2] to types
     whose rank is that of @('int') or higher.
     Although C does not promote the operand of @('!'),
     note that performing an explicit promotion does not affect the result;
     thus, there is no need to define funtions for this operator
     for types of rank lower than @('int').
     For all the binary integer operators
     except @('<<'), @('>>'), @('&&'), and @('||'),
     C subjects the operands to the usual arithmetic conversions [C:6.3.1.8],
     which involve promoting them [C:6.3.1.1/2]
     and turning them into a common type of rank @('int') or higher:
     thus, it suffices to define functions for operands
     of the same type of rank @('int') or higher.
     C also promotes, individually, the operands of @('<<') and @('>>'),
     but without turning them into a common type:
     for now, for these shift operators, we define functions
     for operands of equal types of rank @('int') or higher.
     Although C does not promote the operands of @('&&') and @('||'),
     note that performing explicit promotions does not affect the result:
     thus, we only define functions for these operators
     for operands of equal types of rank @('int') or higher.")
   (xdoc::p
    "When the exact result of an aritmetic operation on signed integers
     is not representable in the signed integer type,
     the behavior is undefined [C:6.5/5]:
     our functions for signed integer operations
     have guards requiring the results to be representable.")
   (xdoc::p
    "Arithmetic on unsigned integers is modular [C:6.2.5/9].")
   (xdoc::p
    "The right operand of a signed shift operator
     must be non-negative and below the bit size of the left operand
     [C:6.5.7/3].
     The left operand, whens signed, must be non-negative.")
   (xdoc::p
    "For division and remainder,
     the guard also requires the divisor to be non-zero.")
   (xdoc::p
    "Note that the relational and equality operators,
     as well as the logical negation, conjunction, and disjunction operations,
     always return @('int'), regardless of the types of the operands.")
   (xdoc::p
    "The logical conjunction and disjunction operators defined here
     are strict versions, because they take two values as inputs.
     Non-strict versions are represented differently.")
   (xdoc::p
    "The bitwise operations assume a two's complement representation,
     which is consistent with "
    (xdoc::seetopic "atc-integer-values" "our model of integer values")
    "; these operations depend on the representation of integers [C:6.5/4]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ atc-def-integer-operations (type)
  (declare (xargs :guard (member-eq type '(:int :long :llong))))
  :short "Macro to generate the models of the C integer operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "The functions and theorems that form the model,
     for each of (@('unsigned') and @('signed'))
     @('int'), @('long'), and @('long long'),
     are quite similar in structure.
     Thus, we define and use this macro to introduce them."))

  (b* ((type-string (acl2::string-downcase
                     (if (eq type :llong) "LONG LONG" (symbol-name type))))
       (type-bits (acl2::packn-pos (list type "-BITS") 'atc))
       (stype (acl2::packn-pos (list "S" type) 'atc))
       (utype (acl2::packn-pos (list "U" type) 'atc))
       (stype-min (add-suffix stype "-MIN"))
       (stype-max (add-suffix stype "-MAX"))
       (utype-max (add-suffix utype "-MAX"))
       (stypep (add-suffix stype "P"))
       (utypep (add-suffix utype "P"))
       (stype-fix (add-suffix stype "-FIX"))
       (utype-fix (add-suffix utype "-FIX"))
       (stype->get (add-suffix stype "->GET"))
       (utype->get (add-suffix utype "->GET"))
       (stype-integerp (add-suffix stype "-INTEGERP"))
       (utype-integerp (add-suffix utype "-INTEGERP"))
       (stype-integerp-alt-def (add-suffix stype-integerp "-ALT-DEF"))
       (utype-integerp-alt-def (add-suffix utype-integerp "-ALT-DEF"))
       (stype-const (add-suffix stype "-CONST"))
       (utype-const (add-suffix utype "-CONST"))
       (stype-nonzerop (add-suffix stype "-NONZEROP"))
       (utype-nonzerop (add-suffix utype "-NONZEROP"))
       (stype-plus (add-suffix stype "-PLUS"))
       (utype-plus (add-suffix utype "-PLUS"))
       (stype-minus (add-suffix stype "-MINUS"))
       (utype-minus (add-suffix utype "-MINUS"))
       (stype-minus-okp (add-suffix stype-minus "-OKP"))
       (stype-bitnot (add-suffix stype "-BITNOT"))
       (utype-bitnot (add-suffix utype "-BITNOT"))
       (stype-lognot (add-suffix stype "-LOGNOT"))
       (utype-lognot (add-suffix utype "-LOGNOT"))
       (stype-add (add-suffix stype "-ADD"))
       (utype-add (add-suffix utype "-ADD"))
       (stype-add-okp (add-suffix stype-add "-OKP"))
       (stype-sub (add-suffix stype "-SUB"))
       (utype-sub (add-suffix utype "-SUB"))
       (stype-sub-okp (add-suffix stype-sub "-OKP"))
       (stype-mul (add-suffix stype "-MUL"))
       (utype-mul (add-suffix utype "-MUL"))
       (stype-mul-okp (add-suffix stype-mul "-OKP"))
       (stype-div (add-suffix stype "-DIV"))
       (utype-div (add-suffix utype "-DIV"))
       (stype-div-okp (add-suffix stype-div "-OKP"))
       (utype-div-okp (add-suffix utype-div "-OKP"))
       (stype-rem (add-suffix stype "-REM"))
       (utype-rem (add-suffix utype "-REM"))
       (stype-rem-okp (add-suffix stype-rem "-OKP"))
       (utype-rem-okp (add-suffix utype-rem "-OKP"))
       (stype-shl-stype (acl2::packn-pos (list stype "-SHL-" stype) 'atc))
       (utype-shl-utype (acl2::packn-pos (list utype "-SHL-" utype) 'atc))
       (stype-shl-stype-okp (add-suffix stype-shl-stype "-OKP"))
       (utype-shl-utype-okp (add-suffix utype-shl-utype "-OKP"))
       (stype-shr-stype (acl2::packn-pos (list stype "-SHR-" stype) 'atc))
       (utype-shr-utype (acl2::packn-pos (list utype "-SHR-" utype) 'atc))
       (stype-shr-stype-okp (add-suffix stype-shr-stype "-OKP"))
       (utype-shr-utype-okp (add-suffix utype-shr-utype "-OKP"))
       (stype-lt (add-suffix stype "-LT"))
       (utype-lt (add-suffix utype "-LT"))
       (stype-gt (add-suffix stype "-GT"))
       (utype-gt (add-suffix utype "-GT"))
       (stype-le (add-suffix stype "-LE"))
       (utype-le (add-suffix utype "-LE"))
       (stype-ge (add-suffix stype "-GE"))
       (utype-ge (add-suffix utype "-GE"))
       (stype-eq (add-suffix stype "-EQ"))
       (utype-eq (add-suffix utype "-EQ"))
       (stype-ne (add-suffix stype "-NE"))
       (utype-ne (add-suffix utype "-NE"))
       (stype-bitand (add-suffix stype "-BITAND"))
       (utype-bitand (add-suffix utype "-BITAND"))
       (stype-bitxor (add-suffix stype "-BITXOR"))
       (utype-bitxor (add-suffix utype "-BITXOR"))
       (stype-bitior (add-suffix stype "-BITIOR"))
       (utype-bitior (add-suffix utype "-BITIOR"))
       (stype-logand (add-suffix stype "-LOGAND"))
       (utype-logand (add-suffix utype "-LOGAND"))
       (stype-logor (add-suffix stype "-LOGOR"))
       (utype-logor (add-suffix utype "-LOGOR")))

    `(progn

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-const ((x natp))
         :guard (,stype-integerp x)
         :returns (result ,stypep)
         :short ,(concatenate 'string
                              "Integer constant of type @('signed "
                              type-string
                              "').")
         (,stype x))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-const ((x natp))
         :guard (,utype-integerp x)
         :returns (result ,utypep)
         :short ,(concatenate 'string
                              "Integer constant of type @('unsigned "
                              type-string
                              "').")
         (,utype x))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-nonzerop ((x ,stypep))
         :returns (yes/no booleanp)
         :short ,(concatenate 'string
                              "Check if a @('signed "
                              type-string
                              "') value is not 0.")
         (/= (,stype->get x) 0)
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-nonzerop ((x ,utypep))
         :returns (yes/no booleanp)
         :short ,(concatenate 'string
                              "Check if an @('unsigned "
                              type-string
                              "') value is not 0.")
         (/= (,utype->get x) 0)
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-plus ((x ,stypep))
         :returns (result ,stypep)
         :short ,(concatenate 'string
                              "Unary plus of @('signed "
                              type-string
                              "') values [C:6.5.3].")
         (,stype-fix x)
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-plus ((x ,utypep))
         :returns (result ,utypep)
         :short ,(concatenate 'string
                              "Unary plus of @('unsigned "
                              type-string
                              "') values [C:6.5.3].")
         (,utype-fix x)
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-minus-okp ((x ,stypep))
         :returns (yes/no booleanp)
         :short ,(concatenate 'string
                              "Check if unary minus of @('signed "
                              type-string
                              "') values is well-defined.")
         (,stype-integerp (- (,stype->get x)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-minus ((x ,stypep))
         :guard (,stype-minus-okp x)
         :returns (result ,stypep)
         :short ,(concatenate 'string
                              "Unary minus of @('signed "
                              type-string
                              "') values [C:6.5.3].")
         (,stype (- (,stype->get x)))
         :guard-hints (("Goal" :in-theory (enable ,stype-minus-okp)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-minus ((x ,utypep))
         :returns (result ,utypep)
         :short ,(concatenate 'string
                              "Unary minus of @('unsigned "
                              type-string
                              "') values [C:6.5.3].")
         (,utype (mod (- (,utype->get x))
                      (1+ (,utype-max))))
         :guard-hints (("Goal" :in-theory (enable ,utype-integerp-alt-def)))
         :hooks (:fix)
         :prepwork ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-bitnot ((x ,stypep))
         :returns (result ,stypep)
         :short ,(concatenate 'string
                              "Bitwise complement of @('signed "
                              type-string
                              "') values [C:6.5.3].")
         (,stype (lognot (,stype->get x)))
         :guard-hints (("Goal" :in-theory (enable ,stype-integerp-alt-def
                                                  ,stype->get
                                                  ,stypep
                                                  (:e ,stype-min)
                                                  (:e ,stype-max))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-bitnot ((x ,utypep))
         :returns (result ,utypep)
         :short ,(concatenate 'string
                              "Bitwise complement of @('unsigned "
                              type-string
                              "') values [C:6.5.3].")
         (,utype (mod (lognot (,utype->get x))
                      (1+ (,utype-max))))
         :guard-hints (("Goal" :in-theory (enable ,utype-integerp-alt-def)))
         :hooks (:fix)
         :prepwork ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-lognot ((x ,stypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Logical complement of @('signed "
                              type-string
                              "') values [C:6.5.3].")
         (if (= (,stype->get x) 0)
             (sint 1)
           (sint 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-lognot ((x ,utypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Logical complement of @('unsigned "
                              type-string
                              "') values [C:6.5.3].")
         (if (= (,utype->get x) 0)
             (sint 1)
           (sint 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-add-okp ((x ,stypep) (y ,stypep))
         :returns (yes/no booleanp)
         :short ,(concatenate 'string
                              "Check if addition of @('signed "
                              type-string
                              "') values is well-defined.")
         (,stype-integerp (+ (,stype->get x) (,stype->get y)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-add ((x ,stypep) (y ,stypep))
         :guard (,stype-add-okp x y)
         :returns (result ,stypep)
         :short ,(concatenate 'string
                              "Addition of @('signed "
                              type-string
                              "') values [C:6.5.6].")
         (,stype (+ (,stype->get x) (,stype->get y)))
         :guard-hints (("Goal" :in-theory (enable ,stype-add-okp)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-add ((x ,utypep) (y ,utypep))
         :returns (result ,utypep)
         :short ,(concatenate 'string
                              "Addition of @('unsigned "
                              type-string
                              "') values [C:6.5.6].")
         (,utype (mod (+ (,utype->get x) (,utype->get y))
                      (1+ (,utype-max))))
         :guard-hints (("Goal" :in-theory (enable ,utype-integerp-alt-def)))
         :hooks (:fix)
         :prepwork ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-sub-okp ((x ,stypep) (y ,stypep))
         :returns (yes/no booleanp)
         :short ,(concatenate 'string
                              "Check if subtraction of @('signed "
                              type-string
                              "') values is well-defined.")
         (,stype-integerp (- (,stype->get x) (,stype->get y)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-sub ((x ,stypep) (y ,stypep))
         :guard (,stype-sub-okp x y)
         :returns (result ,stypep)
         :short ,(concatenate 'string
                              "Subtraction of @('signed "
                              type-string
                              "') values [C:6.5.6].")
         (,stype (- (,stype->get x) (,stype->get y)))
         :guard-hints (("Goal" :in-theory (enable ,stype-sub-okp)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-sub ((x ,utypep) (y ,utypep))
         :returns (result ,utypep)
         :short ,(concatenate 'string
                              "Subtraction of @('unsigned "
                              type-string
                              "') values [C:6.5.6].")
         (,utype (mod (- (,utype->get x) (,utype->get y))
                      (1+ (,utype-max))))
         :guard-hints (("Goal" :in-theory (enable ,utype-integerp-alt-def)))
         :hooks (:fix)
         :prepwork ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-mul-okp ((x ,stypep) (y ,stypep))
         :returns (yes/no booleanp)
         :short ,(concatenate 'string
                              "Check if multiplication of @('signed "
                              type-string
                              "') values is well-defined.")
         (,stype-integerp (* (,stype->get x) (,stype->get y)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-mul ((x ,stypep) (y ,stypep))
         :guard (,stype-mul-okp x y)
         :returns (result ,stypep)
         :short ,(concatenate 'string
                              "Multiplication of @('signed "
                              type-string
                              "') values [C:6.5.5].")
         (,stype (* (,stype->get x) (,stype->get y)))
         :guard-hints (("Goal" :in-theory (enable ,stype-mul-okp)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-mul ((x ,utypep) (y ,utypep))
         :returns (result ,utypep)
         :short ,(concatenate 'string
                              "Multiplication of @('unsigned "
                              type-string
                              "') values [C:6.5.5].")
         (,utype (mod (* (,utype->get x) (,utype->get y))
                      (1+ (,utype-max))))
         :guard-hints (("Goal" :in-theory (enable ,utype-integerp-alt-def)))
         :hooks (:fix)
         :prepwork ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-div-okp ((x ,stypep) (y ,stypep))
         :returns (yes/no booleanp)
         :short ,(concatenate 'string
                              "Check if division of @('signed "
                              type-string
                              "') values is well-defined.")
         (and (not (equal (,stype->get y) 0))
              (,stype-integerp (truncate (,stype->get x) (,stype->get y))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-div ((x ,stypep) (y ,stypep))
         :guard (,stype-div-okp x y)
         :returns (result ,stypep)
         :short ,(concatenate 'string
                              "Division of @('signed "
                              type-string
                              "') values [C:6.5.5].")
         (,stype (truncate (,stype->get x) (,stype->get y)))
         :guard-hints (("Goal" :in-theory (enable ,stype-div-okp)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-div-okp ((x ,utypep) (y ,utypep))
         :returns (yes/no booleanp)
         (declare (ignore x))
         :short ,(concatenate 'string
                              "Check if division of @('unsigned "
                              type-string
                              "') values is well-defined.")
         (not (equal (,utype->get y) 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-div ((x ,utypep) (y ,utypep))
         :guard (,utype-div-okp x y)
         :returns (result ,utypep)
         :short ,(concatenate 'string
                              "Division of @('unsigned "
                              type-string
                              "') values [C:6.5.5].")
         (,utype (mod (truncate (,utype->get x) (,utype->get y))
                      (1+ (,utype-max))))
         :guard-hints (("Goal" :in-theory (enable ,utype-div-okp
                                                  ,utype-integerp-alt-def)))
         :hooks (:fix)
         :prepwork ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-rem-okp ((x ,stypep) (y ,stypep))
         :returns (yes/no booleanp)
         :short ,(concatenate 'string
                              "Check if remainder of @('signed "
                              type-string
                              "') values is well-defined.")
         (and (not (equal (,stype->get y) 0))
              (,stype-integerp (truncate (,stype->get x) (,stype->get y))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-rem ((x ,stypep) (y ,stypep))
         :guard (,stype-rem-okp x y)
         :returns (result ,stypep)
         :short ,(concatenate 'string
                              "Remainder of @('signed "
                              type-string
                              "') values [C:6.5.5].")
         (,stype (rem (,stype->get x) (,stype->get y)))
         :guard-hints (("Goal" :in-theory (enable ,stype-rem-okp
                                                  ,stype-integerp
                                                  ,stype->get
                                                  ,stypep)))
         :hooks (:fix)
         :prepwork ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-rem-okp ((x ,utypep) (y ,utypep))
         (declare (ignore x))
         :returns (yes/no booleanp)
         :short ,(concatenate 'string
                              "Check if remainder of @('unsigned "
                              type-string
                              "') values is well-defined.")
         (not (equal (,utype->get y) 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-rem ((x ,utypep) (y ,utypep))
         :guard (,utype-rem-okp x y)
         :returns (result ,utypep)
         :short ,(concatenate 'string
                              "Remainder of @('unsigned "
                              type-string
                              "') values [C:6.5.5].")
         (,utype (mod (rem (,utype->get x) (,utype->get y))
                      (1+ (,utype-max))))
         :guard-hints (("Goal" :in-theory (enable ,utype-rem-okp
                                                  ,utype-integerp-alt-def)))
         :hooks (:fix)
         :prepwork ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-shl-stype-okp ((x ,stypep) (y ,stypep))
         :returns (yes/no booleanp)
         :short ,(concatenate 'string
                              "Check if left shift of @('signed "
                              type-string
                              "') values by @('signed "
                              type-string
                              "') values is well-defined.")
         (and (integer-range-p 0 (,type-bits) (,stype->get y))
              (>= (,stype->get x) 0)
              (,stype-integerp (* (,stype->get x)
                                  (expt 2 (,stype->get y)))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-shl-stype ((x ,stypep) (y ,stypep))
         :guard (,stype-shl-stype-okp x y)
         :returns (result ,stypep)
         :short ,(concatenate 'string
                              "Left shift of @('signed "
                              type-string
                              "') values by @('signed "
                              type-string
                              "') values [C:6.5.7].")
         (,stype (* (,stype->get x)
                    (expt 2 (,stype->get y))))
         :guard-hints (("Goal" :in-theory (enable ,stype-shl-stype-okp)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-shl-utype-okp ((x ,utypep) (y ,utypep))
         (declare (ignore x))
         :returns (yes/no booleanp)
         :short ,(concatenate 'string
                              "Check if left shift of @('unsigned "
                              type-string
                              "') values by @('unsigned "
                              type-string
                              "') values is well-defined.")
         (integer-range-p 0 (,type-bits) (,utype->get y))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-shl-utype ((x ,utypep) (y ,utypep))
         :guard (,utype-shl-utype-okp x y)
         :returns (result ,utypep)
         :short ,(concatenate 'string
                              "Left shift of @('unsigned "
                              type-string
                              "') values by @('unsigned "
                              type-string
                              "') values [C:6.5.7].")
         (,utype (mod (* (,utype->get x)
                         (expt 2 (,utype->get y)))
                      (1+ (,utype-max))))
         :guard-hints (("Goal" :in-theory (enable ,utype-shl-utype-okp
                                                  ,utype-integerp-alt-def)))
         :hooks (:fix)
         :prepwork ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-shr-stype-okp ((x ,stypep) (y ,stypep))
         :returns (yes/no booleanp)
         :short ,(concatenate 'string
                              "Check if right shift of @('signed "
                              type-string
                              "') values by @('signed "
                              type-string
                              "') values is well-defined.")
         (and (integer-range-p 0 (,type-bits) (,stype->get y))
              (>= (,stype->get x) 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-shr-stype ((x ,stypep) (y ,stypep))
         :guard (,stype-shr-stype-okp x y)
         :returns (result ,stypep)
         :short ,(concatenate 'string
                              "Right shift of @('signed "
                              type-string
                              "') values by @('signed "
                              type-string
                              "') values [C:6.5.7].")
         (,stype (truncate (,stype->get x)
                           (expt 2 (,stype->get y))))
         :guard-hints (("Goal" :in-theory (enable ,stype-shr-stype-okp
                                                  ,stype-integerp
                                                  ,stype->get
                                                  ,stypep)))
         :hooks (:fix)
         :prepwork
         ((local (include-book "kestrel/arithmetic-light/expt" :dir :system))
          (local (include-book "kestrel/arithmetic-light/truncate" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-shr-utype-okp ((x ,utypep) (y ,utypep))
         (declare (ignore x))
         :returns (yes/no booleanp)
         :short ,(concatenate 'string
                              "Check if right shift of @('unsigned "
                              type-string
                              "') values by @('unsigned "
                              type-string
                              "') values is well-defined.")
         (integer-range-p 0 (,type-bits) (,utype->get y))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-shr-utype ((x ,utypep) (y ,utypep))
         :returns (result ,utypep)
         :short ,(concatenate 'string
                              "Left shift of @('unsigned "
                              type-string
                              "') values by @('unsigned "
                              type-string
                              "') values [C:6.5.7].")
         (,utype (mod (truncate (,utype->get x)
                                (expt 2 (,utype->get y)))
                      (1+ (,utype-max))))
         :guard-hints (("Goal" :in-theory (enable ,utype-shr-utype-okp
                                                  ,utype-integerp-alt-def)))
         :hooks (:fix)
         :prepwork ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-lt ((x ,stypep) (y ,stypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Less-than relation of @('signed "
                              type-string
                              "') values [C:6.5.8].")
         (if (< (,stype->get x) (,stype->get y))
             (sint 1)
           (sint 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-lt ((x ,utypep) (y ,utypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Less-than relation of @('unsigned "
                              type-string
                              "') values [C:6.5.8].")
         (if (< (,utype->get x) (,utype->get y))
             (sint 1)
           (sint 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-gt ((x ,stypep) (y ,stypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Greater-than relation of @('signed "
                              type-string
                              "') values [C:6.5.8].")
         (if (> (,stype->get x) (,stype->get y))
             (sint 1)
           (sint 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-gt ((x ,utypep) (y ,utypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Greater-than relation of @('unsigned "
                              type-string
                              "') values [C:6.5.8].")
         (if (> (,utype->get x) (,utype->get y))
             (sint 1)
           (sint 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-le ((x ,stypep) (y ,stypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Less-than-or-equal-to relation of @('signed "
                              type-string
                              "') values [C:6.5.8].")
         (if (<= (,stype->get x) (,stype->get y))
             (sint 1)
           (sint 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-le ((x ,utypep) (y ,utypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Less-than-or-equal-to relation of @('unsigned "
                              type-string
                              "') values [C:6.5.8].")
         (if (<= (,utype->get x) (,utype->get y))
             (sint 1)
           (sint 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-ge ((x ,stypep) (y ,stypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Greater-than-or-equal-to relation of @('signed "
                              type-string
                              "') values [C:6.5.8].")
         (if (>= (,stype->get x) (,stype->get y))
             (sint 1)
           (sint 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-ge ((x ,utypep) (y ,utypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Greater-than-or-equal-to relation of @('unsigned "
                              type-string
                              "') values [C:6.5.8].")
         (if (>= (,utype->get x) (,utype->get y))
             (sint 1)
           (sint 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-eq ((x ,stypep) (y ,stypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Equality of @('signed "
                              type-string
                              "') values [C:6.5.9].")
         (if (= (,stype->get x) (,stype->get y))
             (sint 1)
           (sint 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-eq ((x ,utypep) (y ,utypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Equality of @('unsigned "
                              type-string
                              "') values [C:6.5.9].")
         (if (= (,utype->get x) (,utype->get y))
             (sint 1)
           (sint 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-ne ((x ,stypep) (y ,stypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Non-equality of @('signed "
                              type-string
                              "') values [C:6.5.9].")
         (if (/= (,stype->get x) (,stype->get y))
             (sint 1)
           (sint 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-ne ((x ,utypep) (y ,utypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Non-equality of @('unsigned "
                              type-string
                              "') values [C:6.5.9].")
         (if (/= (,utype->get x) (,utype->get y))
             (sint 1)
           (sint 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-bitand ((x ,stypep) (y ,stypep))
         :returns (result ,stypep)
         :short ,(concatenate 'string
                              "Bitwise conjunction of @('signed "
                              type-string
                              "') values [C:6.5.10].")
         (,stype (logand (,stype->get x) (,stype->get y)))
         :guard-hints (("Goal" :in-theory (enable ,stype-integerp
                                                  ,stypep
                                                  ,stype->get)))
         :hooks (:fix)
         :prepwork ((local (include-book "ihs/logops-lemmas" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-bitand ((x ,utypep) (y ,utypep))
         :returns (result ,utypep)
         :short ,(concatenate 'string
                              "Bitwise conjunction of @('unsigned "
                              type-string
                              "') values [C:6.5.10].")
         (,utype (logand (,utype->get x) (,utype->get y)))
         :guard-hints (("Goal" :in-theory (enable ,utype-integerp
                                                  ,utypep
                                                  ,utype->get)))
         :hooks (:fix)
         :prepwork ((local (include-book "ihs/logops-lemmas" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-bitxor ((x ,stypep) (y ,stypep))
         :returns (result ,stypep)
         :short ,(concatenate 'string
                              "Bitwise exclusive disjunction of @('signed "
                              type-string
                              "') values [C:6.5.11].")
         (,stype (logxor (,stype->get x) (,stype->get y)))
         :guard-hints (("Goal" :in-theory (enable ,stype-integerp
                                                  ,stypep
                                                  ,stype->get)))
         :hooks (:fix)
         :prepwork
         ((local (include-book "centaur/bitops/ihs-extensions" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-bitxor ((x ,utypep) (y ,utypep))
         :returns (result ,utypep)
         :short ,(concatenate 'string
                              "Bitwise exclusive disjunction of @('unsigned "
                              type-string
                              "') values [C:6.5.10].")
         (,utype (logxor (,utype->get x) (,utype->get y)))
         :guard-hints (("Goal" :in-theory (enable ,utype-integerp
                                                  ,utypep
                                                  ,utype->get)))
         :hooks (:fix)
         :prepwork
         ((local (include-book "centaur/bitops/ihs-extensions" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-bitior ((x ,stypep) (y ,stypep))
         :returns (result ,stypep)
         :short ,(concatenate 'string
                              "Bitwise inclusive disjunction of @('signed "
                              type-string
                              "') values [C:6.5.12].")
         (,stype (logior (,stype->get x) (,stype->get y)))
         :hooks (:fix)
         :guard-hints (("Goal" :in-theory (enable ,stype-integerp
                                                  ,stypep
                                                  ,stype->get)))
         :prepwork
         ((local (include-book "centaur/bitops/ihs-extensions" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-bitior ((x ,utypep) (y ,utypep))
         :returns (result ,utypep)
         :short ,(concatenate 'string
                              "Bitwise inclusive disjunction of @('unsigned "
                              type-string
                              "') values [C:6.5.12].")
         (,utype (logior (,utype->get x) (,utype->get y)))
         :hooks (:fix)
         :guard-hints (("Goal" :in-theory (enable ,utype-integerp
                                                  ,utypep
                                                  ,utype->get)))
         :prepwork
         ((local (include-book "centaur/bitops/ihs-extensions" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-logand ((x ,stypep) (y ,stypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Logical conjunction of @('signed "
                              type-string
                              "') values [C:6.5.13].")
         (sint01 (and (,stype-nonzerop x) (,stype-nonzerop y)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-logand ((x ,utypep) (y ,utypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Logical conjunction of @('unsigned "
                              type-string
                              "') values [C:6.5.13].")
         (sint01 (and (,utype-nonzerop x) (,utype-nonzerop y)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-logor ((x ,stypep) (y ,stypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Logical disjunction of @('signed "
                              type-string
                              "') values [C:6.5.14].")
         (sint01 (or (,stype-nonzerop x) (,stype-nonzerop y)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-logor ((x ,utypep) (y ,utypep))
         :returns (result sintp)
         :short ,(concatenate 'string
                              "Logical disjunction of @('unsigned "
                              type-string
                              "') values [C:6.5.14].")
         (sint01 (or (,utype-nonzerop x) (,utype-nonzerop y)))
         :hooks (:fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint01 ((b booleanp))
  :returns (x sintp)
  :short "Turn an ACL2 boolean into an @('int') value 0 or 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is essentially (but not exactly) the inverse of @(tsee sint-nonzerop).
     Together with @(tsee sint-nonzerop),
     it can be used to represent in ACL2
     shallowly embedded C logical conjunctions and disjunctions,
     which must be integers in C,
     but must be booleans in ACL2 to represent their non-strictness."))
  (if b (sint 1) (sint 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(atc-def-integer-operations :int)

(atc-def-integer-operations :long)

(atc-def-integer-operations :llong)
