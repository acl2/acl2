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

(include-book "integer-conversions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-integer-operations
  :parents (atc-dynamic-semantics)
  :short "C integer operations for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define ACL2 functions that model C operations on
     the integer types supported in our model,
     namely the standard unsigned and signed integers, except @('_Bool').")
   (xdoc::p
    "We introduce functions @('<type>-const')
     to construct integer constants.
     Following [C:6.4.4.1], these have non-negative values
     and may have only certain integer types,
     namely those with the same rank as @('int') or higher.
     Thus we introduce a function for each integer type in those ranks.
     Each takes a natural number as argument,
     which the guard further constrains to be representable in the type.")
   (xdoc::p
    "We introduce functions @('<type>-nonzerop')
     to turn C integers into ACL2 booleans,
     i.e. to test whether the integers are not zero.
     These are used to represent shallowly embedded tests.
     We introduce a function for each integer type.")
   (xdoc::p
    "We introduce functions @('<type>-integer-value')
     to turn C integers into ACL2 integers.
     These are used as operands of certain C operations
     whose result does not depend on the C type of the operand,
     but rather just on its (mathematical) integer value.
     We define one function for each integer type.
     Even though these functions are essentially synonyms of
     the deconstructors of the fixtypes of the integer values,
     having a separate function provides more abstraction,
     should the fixtype representation be changed in the future.")
   (xdoc::p
    "We introduce a single function @(tsee sint01)
     to turn ACL2 booleans into the @('int') 0 or 1 (for false and true).
     This function is used in the ACL2 representation of
     non-strict C conjunctions @('&&') and disjunctions @('||'),
     which always return @('int') 0 or 1 [C:6.5.13/3] [C:6.5.14/3].
     We do not need similar functions for other types,
     because the 0 or 1 are always @('int')
     for operations like @('&&') and @('||').")
   (xdoc::p
    "We introduce functions for the unary and binary operators,
     as detailed below.")
   (xdoc::p
    "For each unary operator, we introduce a function for each integer type.
     The function takes an argument of that integer type,
     and returns a result of possibly different type.
     For all the unary integer operators except @('!'),
     C promotes operands [C:6.3.1.1/2] to types of rank @('int') or higher,
     and that is also the result of the operator.
     C does not promote the operand of @('!');
     this operator always returns an @('int').")
   (xdoc::p
    "For all the binary integer operators
     except @('<<'), @('>>'), @('&&'), and @('||'),
     C subjects the operands to the usual arithmetic conversions [C:6.3.1.8],
     which involve promoting them [C:6.3.1.1/2]
     and turning them into a common type of rank @('int') or higher:
     thus, it suffices to define functions for operands
     of the same type of rank @('int') or higher.
     C also promotes, individually, the operands of @('<<') and @('>>'),
     but without turning them into a common type;
     while the type of the first operand affects the result,
     only the (mathematical) integer value of the second operand does,
     and thus we introduce functions
     that take an ACL2 integer as the second operand.
     We also have functions
     that take a C integer as the second operand,
     of the same type as the first operand;.
     Although C does not promote the operands of @('&&') and @('||'),
     note that performing explicit promotions does not affect the result:
     thus, we only define functions for these operators
     for operands of equal types of rank @('int') or higher;
     we may actually remove these functions altogether,
     and always require their non-strict representation in ACL2.")
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
     The left operand, when signed, must be non-negative.")
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
     Non-strict versions are represented differently in ACL2.")
   (xdoc::p
    "The bitwise operations assume a two's complement representation,
     which is consistent with "
    (xdoc::seetopic "atc-integers" "our model of integer values")
    "; these operations depend on the C representation of integers [C:6.5/4]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-operations-1 (type)
  :guard (member-eq type *atc-integer-types*)
  :short "Event to generate the ACL2 models of
          the C integer operations that involve one integer type."

  (b* ((type-string (atc-integer-type-string type))
       (rtype (case type
                (schar 'sint)
                (uchar (if (<= (uchar-max) (sint-max)) 'sint 'uint))
                (sshort 'sint)
                (ushort (if (<= (ushort-max) (sint-max)) 'sint 'uint))
                (t type)))
       (type-bits (acl2::packn-pos (list (str::implode
                                          (cdr
                                           (str::explode
                                            (symbol-name type))))
                                         "-BITS")
                                   'atc))
       (typep (atc-integer-typep type))
       (type->get (atc-integer-type->get type))
       (type-mod (atc-integer-type-mod type))
       (type-integerp (atc-integer-type-integerp type))
       (type-integerp-alt-def (atc-integer-type-integerp-alt-def type))
       (type-fix (add-suffix type "-FIX"))
       (type-const (add-suffix type "-CONST"))
       (type-nonzerop (add-suffix type "-NONZEROP"))
       (type-integer-value (add-suffix type "-INTEGER-VALUE"))
       (plus-type (acl2::packn-pos (list "PLUS-" type) 'atc))
       (minus-type (acl2::packn-pos (list "MINUS-" type) 'atc))
       (minus-type-okp (add-suffix minus-type "-OKP"))
       (bitnot-type (acl2::packn-pos (list "BITNOT-" type) 'atc))
       (rtype-min (add-suffix rtype "-MIN"))
       (rtype-max (add-suffix rtype "-MAX"))
       (rtypep (atc-integer-typep rtype))
       (hirankp (member-eq type '(sint uint slong ulong sllong ullong)))
       (rtype-from-type (atc-integer-type-conv type rtype))
       (plus-rtype (acl2::packn-pos (list "PLUS-" rtype) 'atc))
       (minus-rtype (acl2::packn-pos (list "MINUS-" rtype) 'atc))
       (minus-rtype-okp (add-suffix minus-rtype "-OKP"))
       (bitnot-rtype (acl2::packn-pos (list "BITNOT-" rtype) 'atc))
       (type-signedp (atc-integer-type-signedp type))
       (rtype-signedp (atc-integer-type-signedp rtype))
       (lognot-type (acl2::packn-pos (list "LOGNOT-" type) 'atc))
       (shl-type (acl2::packn-pos (list "SHL-" type) 'atc))
       (shl-type-okp (add-suffix shl-type "-OKP"))
       (shl-rtype (acl2::packn-pos (list "SHL-" rtype) 'atc))
       (shl-rtype-okp (add-suffix shl-rtype "-OKP"))
       (shr-type (acl2::packn-pos (list "SHR-" type) 'atc))
       (shr-type-okp (add-suffix shr-type "-OKP"))
       (shr-rtype (acl2::packn-pos (list "SHR-" rtype) 'atc))
       (shr-rtype-okp (add-suffix shr-rtype "-OKP")))

    `(progn

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          hirankp
          `((define ,type-const ((x natp))
              :guard (,type-integerp x)
              :returns (result ,typep)
              :short ,(str::cat "Integer constant of " type-string ".")
              (,type x))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,type-nonzerop ((x ,typep))
         :returns (yes/no booleanp)
         :short ,(str::cat "Check if a value of " type-string " is not 0.")
         (/= (,type->get x) 0)
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,type-integer-value ((x ,typep))
         :returns (ival integerp)
         :short ,(str::cat "Turn a vaue of "
                           type-string
                           " into an ACL2 integer value.")
         (,type->get x)
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,plus-type ((x ,typep))
         :returns (result ,rtypep)
         :short ,(str::cat "Unary plus of a value of "
                           type-string
                           " [C:6.5.3].")
         ,(if hirankp
              `(,type-fix x)
            `(,plus-rtype (,rtype-from-type x)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          rtype-signedp
          `((define ,minus-type-okp ((x ,typep))
              :returns (yes/no booleanp)
              :short ,(str::cat "Check if the unary minus of a value of "
                                type-string
                                " is well-defined.")
              ,(if hirankp
                   `(,type-integerp (- (,type->get x)))
                 `(,minus-rtype-okp (,rtype-from-type x)))
              :hooks (:fix))))

       ;;;;;;;;;;;;;;;;;;;;

       (define ,minus-type ((x ,typep))
         ,@(and rtype-signedp `(:guard (,minus-type-okp x)))
         :returns (result ,rtypep)
         :short ,(str::cat "Unary minus of a value of "
                           type-string
                           " [C:6.5.3].")
         ,(if hirankp
              `(,(if type-signedp type type-mod) (- (,type->get x)))
            `(,minus-rtype (,rtype-from-type x)))
         ,@(and rtype-signedp
                `(:guard-hints (("Goal" :in-theory (enable ,minus-type-okp)))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,bitnot-type ((x ,typep))
         :returns (result ,rtypep)
         :short ,(str::cat "Bitwise complement of a value of "
                           type-string
                           " [C:6.5.3].")
         ,(if hirankp
              `(,(if type-signedp type type-mod) (lognot (,type->get x)))
            `(,bitnot-rtype (,rtype-from-type x)))
         ,@(and hirankp
                type-signedp
                `(:guard-hints
                  (("Goal" :in-theory (enable ,type-integerp-alt-def
                                              ,type->get
                                              ,typep
                                              (:e ,rtype-min)
                                              (:e ,rtype-max))))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,lognot-type ((x ,typep))
         :returns (result sintp)
         :short ,(str::cat "Logical complement of a value of "
                           type-string
                           " [C:6.5.3].")
         (sint01 (= (,type->get x) 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,shl-type-okp ((x ,typep) (y integerp))
         ,@(and hirankp
                (not type-signedp)
                `((declare (ignore x))))
         :returns (yes/no booleanp)
         :short ,(str::cat "Check if the left shift of a value of "
                           type-string
                           " is well-defined.")
         ,(if hirankp
              (if type-signedp
                  `(and (integer-range-p 0 (,type-bits) (ifix y))
                        (>= (,type->get x) 0)
                        (,type-integerp (* (,type->get x)
                                           (expt 2 (ifix y)))))
                `(integer-range-p 0 (,type-bits) (ifix y)))
            `(,shl-rtype-okp (,rtype-from-type x) (ifix y)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;

       (define ,shl-type ((x ,typep) (y integerp))
         :guard (,shl-type-okp x y)
         :returns (result ,rtypep)
         :short ,(str::cat "Left shift of a value of "
                           type-string
                           " [C:6.5.7].")
         ,(if hirankp
              `(,(if type-signedp type type-mod) (* (,type->get x)
                                                    (expt 2 (ifix y))))
            `(,shl-rtype (,rtype-from-type x) y))
         :guard-hints (("Goal" :in-theory (enable ,shl-type-okp)))
         ,@(and (not type-signedp)
                '(:prepwork
                  ((local (include-book "arithmetic-3/top" :dir :system)))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,shr-type-okp ((x ,typep) (y integerp))
         ,@(and hirankp
                (not type-signedp)
                `((declare (ignore x))))
         :returns (yes/no booleanp)
         :short ,(str::cat "Check if the right shift of a value of "
                           type-string
                           " is well-defined.")
         ,(if hirankp
              (if type-signedp
                  `(and (integer-range-p 0 (,type-bits) (ifix y))
                        (>= (,type->get x) 0))
                `(integer-range-p 0 (,type-bits) (ifix y)))
            `(,shr-rtype-okp (,rtype-from-type x) (ifix y)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;

       (define ,shr-type ((x ,typep) (y integerp))
         :guard (,shr-type-okp x y)
         :returns (result ,rtypep)
         :short ,(str::cat "Right shift of a value of "
                           type-string
                           " [C:6.5.7].")
         ,(if hirankp
              `(,(if type-signedp type type-mod) (truncate (,type->get x)
                                                           (expt 2 (ifix y))))
            `(,shr-rtype (,rtype-from-type x) y))
         :guard-hints (("Goal"
                        :in-theory (enable ,@(if (and hirankp
                                                      type-signedp)
                                                 (list shr-type-okp
                                                       type-integerp
                                                       type->get
                                                       typep)
                                               (list shr-type-okp)))))
         ,@(and
            type-signedp
            '(:prepwork
              ((local
                (include-book "kestrel/arithmetic-light/expt" :dir :system))
               (local
                (include-book "kestrel/arithmetic-light/truncate" :dir :system)))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint01 ((b booleanp))
  :returns (x sintp)
  :short "Turn an ACL2 boolean into an @('int') value 0 or 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is essentially (but not exactly) the inverse of @(tsee sint-nonzerop).
     Together with @(tsee sint-nonzerop) and other @('...-nonzerop') operations,
     it can be used to represent in ACL2
     shallowly embedded C logical conjunctions and disjunctions,
     which must be integers in C,
     but must be booleans in ACL2 to represent their non-strictness."))
  (if b (sint 1) (sint 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(progn
  ;; It is critical to generate the operations for SINT and UINT
  ;; before the ones for SCHAR and UCHAR and SSHORT and USHORT,
  ;; because the latter are defined in terms of the former.
  (make-event (atc-def-integer-operations-1 'sint))
  (make-event (atc-def-integer-operations-1 'uint))
  (make-event (atc-def-integer-operations-1 'slong))
  (make-event (atc-def-integer-operations-1 'ulong))
  (make-event (atc-def-integer-operations-1 'sllong))
  (make-event (atc-def-integer-operations-1 'ullong))
  (make-event (atc-def-integer-operations-1 'schar))
  (make-event (atc-def-integer-operations-1 'uchar))
  (make-event (atc-def-integer-operations-1 'sshort))
  (make-event (atc-def-integer-operations-1 'ushort)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ atc-def-integer-operations (type)
  (declare (xargs :guard (member-eq type '(:char :short :int :long :llong))))
  :short "Macro to generate the models of the C integer operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "The functions and theorems that form the model,
     for each of (@('unsigned') and @('signed'))
     @('char'), @('short'), @('int'), @('long'), and @('long long'),
     are quite similar in structure.
     Thus, we define and use this macro to introduce them.")
   (xdoc::p
    "For @('char') and @('short') we only generate a few operations.
     Due to the integer promotions and the usual arithmetic conversions,
     most operations are for the types of higher ranks."))

  (b* ((type-string (acl2::string-downcase
                     (if (eq type :llong) "LONG LONG" (symbol-name type))))
       (stype (acl2::packn-pos (list "S" type) 'atc))
       (utype (acl2::packn-pos (list "U" type) 'atc))
       (utype-max (add-suffix utype "-MAX"))
       (stypep (add-suffix stype "P"))
       (utypep (add-suffix utype "P"))
       (stype->get (add-suffix stype "->GET"))
       (utype->get (add-suffix utype "->GET"))
       (stype-integerp (add-suffix stype "-INTEGERP"))
       (utype-integerp (add-suffix utype "-INTEGERP"))
       (utype-integerp-alt-def (add-suffix utype-integerp "-ALT-DEF"))
       (stype-nonzerop (add-suffix stype "-NONZEROP"))
       (utype-nonzerop (add-suffix utype "-NONZEROP"))
       (stype-integer-value (add-suffix stype "-INTEGER-VALUE"))
       (utype-integer-value (add-suffix utype "-INTEGER-VALUE"))
       (add-stype-stype (acl2::packn-pos (list "ADD-" stype "-" stype) 'atc))
       (add-utype-utype (acl2::packn-pos (list "ADD-" utype "-" utype) 'atc))
       (add-stype-stype-okp (add-suffix add-stype-stype "-OKP"))
       (sub-stype-stype (acl2::packn-pos (list "SUB-" stype "-" stype) 'atc))
       (sub-utype-utype (acl2::packn-pos (list "SUB-" utype "-" utype) 'atc))
       (sub-stype-stype-okp (add-suffix sub-stype-stype "-OKP"))
       (mul-stype-stype (acl2::packn-pos (list "MUL-" stype "-" stype) 'atc))
       (mul-utype-utype (acl2::packn-pos (list "MUL-" utype "-" utype) 'atc))
       (mul-stype-stype-okp (add-suffix mul-stype-stype "-OKP"))
       (div-stype-stype (acl2::packn-pos (list "DIV-" stype "-" stype) 'atc))
       (div-utype-utype (acl2::packn-pos (list "DIV-" utype "-" utype) 'atc))
       (div-stype-stype-okp (add-suffix div-stype-stype "-OKP"))
       (div-utype-utype-okp (add-suffix div-utype-utype "-OKP"))
       (rem-stype-stype (acl2::packn-pos (list "REM-" stype "-" stype) 'atc))
       (rem-utype-utype (acl2::packn-pos (list "REM-" utype "-" utype) 'atc))
       (rem-stype-stype-okp (add-suffix rem-stype-stype "-OKP"))
       (rem-utype-utype-okp (add-suffix rem-utype-utype "-OKP"))
       (shl-stype (acl2::packn-pos (list "SHL-" stype) 'atc))
       (shl-utype (acl2::packn-pos (list "SHL-" utype) 'atc))
       (shl-stype-okp (add-suffix shl-stype "-OKP"))
       (shl-utype-okp (add-suffix shl-utype "-OKP"))
       (shr-stype (acl2::packn-pos (list "SHR-" stype) 'atc))
       (shr-utype (acl2::packn-pos (list "SHR-" utype) 'atc))
       (shr-stype-okp (add-suffix shr-stype "-OKP"))
       (shr-utype-okp (add-suffix shr-utype "-OKP"))
       (shl-stype-stype (acl2::packn-pos (list "SHL-" stype "-" stype) 'atc))
       (shl-utype-utype (acl2::packn-pos (list "SHL-" utype "-" utype) 'atc))
       (shl-stype-stype-okp (add-suffix shl-stype-stype "-OKP"))
       (shl-utype-utype-okp (add-suffix shl-utype-utype "-OKP"))
       (shr-stype-stype (acl2::packn-pos (list "SHR-" stype "-" stype) 'atc))
       (shr-utype-utype (acl2::packn-pos (list "SHR-" utype "-" utype) 'atc))
       (shr-stype-stype-okp (add-suffix shr-stype-stype "-OKP"))
       (shr-utype-utype-okp (add-suffix shr-utype-utype "-OKP"))
       (lt-stype-stype (acl2::packn-pos (list "LT-" stype "-" stype) 'atc))
       (lt-utype-utype (acl2::packn-pos (list "LT-" utype "-" utype) 'atc))
       (gt-stype-stype (acl2::packn-pos (list "GT-" stype "-" stype) 'atc))
       (gt-utype-utype (acl2::packn-pos (list "GT-" utype "-" utype) 'atc))
       (le-stype-stype (acl2::packn-pos (list "LE-" stype "-" stype) 'atc))
       (le-utype-utype (acl2::packn-pos (list "LE-" utype "-" utype) 'atc))
       (ge-stype-stype (acl2::packn-pos (list "GE-" stype "-" stype) 'atc))
       (ge-utype-utype (acl2::packn-pos (list "GE-" utype "-" utype) 'atc))
       (eq-stype-stype (acl2::packn-pos (list "EQ-" stype "-" stype) 'atc))
       (eq-utype-utype (acl2::packn-pos (list "EQ-" utype "-" utype) 'atc))
       (ne-stype-stype (acl2::packn-pos (list "NE-" stype "-" stype) 'atc))
       (ne-utype-utype (acl2::packn-pos (list "NE-" utype "-" utype) 'atc))
       (bitand-stype-stype (acl2::packn-pos (list "BITAND-" stype "-" stype) 'atc))
       (bitand-utype-utype (acl2::packn-pos (list "BITAND-" utype "-" utype) 'atc))
       (bitxor-stype-stype (acl2::packn-pos (list "BITXOR-" stype "-" stype) 'atc))
       (bitxor-utype-utype (acl2::packn-pos (list "BITXOR-" utype "-" utype) 'atc))
       (bitior-stype-stype (acl2::packn-pos (list "BITIOR-" stype "-" stype) 'atc))
       (bitior-utype-utype (acl2::packn-pos (list "BITIOR-" utype "-" utype) 'atc))
       (logand-stype-stype (acl2::packn-pos (list "LOGAND-" stype "-" stype) 'atc))
       (logand-utype-utype (acl2::packn-pos (list "LOGAND-" utype "-" utype) 'atc))
       (logor-stype-stype (acl2::packn-pos (list "LOGOR-" stype "-" stype) 'atc))
       (logor-utype-utype (acl2::packn-pos (list "LOGOR-" utype "-" utype) 'atc)))

    `(progn

       ,@(and
          (member-eq type '(:int :long :llong))
          `(

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,add-stype-stype-okp ((x ,stypep) (y ,stypep))
              :returns (yes/no booleanp)
              :short ,(concatenate 'string
                                   "Check if addition of @('signed "
                                   type-string
                                   "') values is well-defined.")
              (,stype-integerp (+ (,stype->get x) (,stype->get y)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,add-stype-stype ((x ,stypep) (y ,stypep))
              :guard (,add-stype-stype-okp x y)
              :returns (result ,stypep)
              :short ,(concatenate 'string
                                   "Addition of @('signed "
                                   type-string
                                   "') values [C:6.5.6].")
              (,stype (+ (,stype->get x) (,stype->get y)))
              :guard-hints (("Goal" :in-theory (enable ,add-stype-stype-okp)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,add-utype-utype ((x ,utypep) (y ,utypep))
              :returns (result ,utypep)
              :short ,(concatenate 'string
                                   "Addition of @('unsigned "
                                   type-string
                                   "') values [C:6.5.6].")
              (,utype (mod (+ (,utype->get x) (,utype->get y))
                           (1+ (,utype-max))))
              :guard-hints
              (("Goal" :in-theory (enable ,utype-integerp-alt-def)))
              :hooks (:fix)
              :prepwork
              ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,sub-stype-stype-okp ((x ,stypep) (y ,stypep))
              :returns (yes/no booleanp)
              :short ,(concatenate 'string
                                   "Check if subtraction of @('signed "
                                   type-string
                                   "') values is well-defined.")
              (,stype-integerp (- (,stype->get x) (,stype->get y)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,sub-stype-stype ((x ,stypep) (y ,stypep))
              :guard (,sub-stype-stype-okp x y)
              :returns (result ,stypep)
              :short ,(concatenate 'string
                                   "Subtraction of @('signed "
                                   type-string
                                   "') values [C:6.5.6].")
              (,stype (- (,stype->get x) (,stype->get y)))
              :guard-hints (("Goal" :in-theory (enable ,sub-stype-stype-okp)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,sub-utype-utype ((x ,utypep) (y ,utypep))
              :returns (result ,utypep)
              :short ,(concatenate 'string
                                   "Subtraction of @('unsigned "
                                   type-string
                                   "') values [C:6.5.6].")
              (,utype (mod (- (,utype->get x) (,utype->get y))
                           (1+ (,utype-max))))
              :guard-hints
              (("Goal" :in-theory (enable ,utype-integerp-alt-def)))
              :hooks (:fix)
              :prepwork
              ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,mul-stype-stype-okp ((x ,stypep) (y ,stypep))
              :returns (yes/no booleanp)
              :short ,(concatenate 'string
                                   "Check if multiplication of @('signed "
                                   type-string
                                   "') values is well-defined.")
              (,stype-integerp (* (,stype->get x) (,stype->get y)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,mul-stype-stype ((x ,stypep) (y ,stypep))
              :guard (,mul-stype-stype-okp x y)
              :returns (result ,stypep)
              :short ,(concatenate 'string
                                   "Multiplication of @('signed "
                                   type-string
                                   "') values [C:6.5.5].")
              (,stype (* (,stype->get x) (,stype->get y)))
              :guard-hints (("Goal" :in-theory (enable ,mul-stype-stype-okp)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,mul-utype-utype ((x ,utypep) (y ,utypep))
              :returns (result ,utypep)
              :short ,(concatenate 'string
                                   "Multiplication of @('unsigned "
                                   type-string
                                   "') values [C:6.5.5].")
              (,utype (mod (* (,utype->get x) (,utype->get y))
                           (1+ (,utype-max))))
              :guard-hints
              (("Goal" :in-theory (enable ,utype-integerp-alt-def)))
              :hooks (:fix)
              :prepwork
              ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,div-stype-stype-okp ((x ,stypep) (y ,stypep))
              :returns (yes/no booleanp)
              :short ,(concatenate 'string
                                   "Check if division of @('signed "
                                   type-string
                                   "') values is well-defined.")
              (and (not (equal (,stype->get y) 0))
                   (,stype-integerp (truncate (,stype->get x) (,stype->get y))))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,div-stype-stype ((x ,stypep) (y ,stypep))
              :guard (,div-stype-stype-okp x y)
              :returns (result ,stypep)
              :short ,(concatenate 'string
                                   "Division of @('signed "
                                   type-string
                                   "') values [C:6.5.5].")
              (,stype (truncate (,stype->get x) (,stype->get y)))
              :guard-hints (("Goal" :in-theory (enable ,div-stype-stype-okp)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,div-utype-utype-okp ((x ,utypep) (y ,utypep))
              :returns (yes/no booleanp)
              (declare (ignore x))
              :short ,(concatenate 'string
                                   "Check if division of @('unsigned "
                                   type-string
                                   "') values is well-defined.")
              (not (equal (,utype->get y) 0))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,div-utype-utype ((x ,utypep) (y ,utypep))
              :guard (,div-utype-utype-okp x y)
              :returns (result ,utypep)
              :short ,(concatenate 'string
                                   "Division of @('unsigned "
                                   type-string
                                   "') values [C:6.5.5].")
              (,utype (mod (truncate (,utype->get x) (,utype->get y))
                           (1+ (,utype-max))))
              :guard-hints
              (("Goal" :in-theory (enable ,div-utype-utype-okp
                                          ,utype-integerp-alt-def)))
              :hooks (:fix)
              :prepwork
              ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,rem-stype-stype-okp ((x ,stypep) (y ,stypep))
              :returns (yes/no booleanp)
              :short ,(concatenate 'string
                                   "Check if remainder of @('signed "
                                   type-string
                                   "') values is well-defined.")
              (and (not (equal (,stype->get y) 0))
                   (,stype-integerp (truncate (,stype->get x) (,stype->get y))))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,rem-stype-stype ((x ,stypep) (y ,stypep))
              :guard (,rem-stype-stype-okp x y)
              :returns (result ,stypep)
              :short ,(concatenate 'string
                                   "Remainder of @('signed "
                                   type-string
                                   "') values [C:6.5.5].")
              (,stype (rem (,stype->get x) (,stype->get y)))
              :guard-hints (("Goal" :in-theory (enable ,rem-stype-stype-okp
                                                       ,stype-integerp
                                                       ,stype->get
                                                       ,stypep)))
              :hooks (:fix)
              :prepwork
              ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,rem-utype-utype-okp ((x ,utypep) (y ,utypep))
              (declare (ignore x))
              :returns (yes/no booleanp)
              :short ,(concatenate 'string
                                   "Check if remainder of @('unsigned "
                                   type-string
                                   "') values is well-defined.")
              (not (equal (,utype->get y) 0))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,rem-utype-utype ((x ,utypep) (y ,utypep))
              :guard (,rem-utype-utype-okp x y)
              :returns (result ,utypep)
              :short ,(concatenate 'string
                                   "Remainder of @('unsigned "
                                   type-string
                                   "') values [C:6.5.5].")
              (,utype (mod (rem (,utype->get x) (,utype->get y))
                           (1+ (,utype-max))))
              :guard-hints
              (("Goal" :in-theory (enable ,rem-utype-utype-okp
                                          ,utype-integerp-alt-def)))
              :hooks (:fix)
              :prepwork
              ((local (include-book "arithmetic-3/top" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,shl-stype-stype-okp ((x ,stypep) (y ,stypep))
              :returns (yes/no booleanp)
              :short ,(concatenate 'string
                                   "Check if left shift of @('signed "
                                   type-string
                                   "') values by @('signed "
                                   type-string
                                   "') values is well-defined.")
              (,shl-stype-okp x (,stype-integer-value y))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,shl-stype-stype ((x ,stypep) (y ,stypep))
              :guard (,shl-stype-stype-okp x y)
              :returns (result ,stypep)
              :short ,(concatenate 'string
                                   "Left shift of @('signed "
                                   type-string
                                   "') values by @('signed "
                                   type-string
                                   "') values [C:6.5.7].")
              (,shl-stype x (,stype-integer-value y))
              :guard-hints (("Goal" :in-theory (enable ,shl-stype-stype-okp)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,shl-utype-utype-okp ((x ,utypep) (y ,utypep))
              :returns (yes/no booleanp)
              :short ,(concatenate 'string
                                   "Check if left shift of @('unsigned "
                                   type-string
                                   "') values by @('unsigned "
                                   type-string
                                   "') values is well-defined.")
              (,shl-utype-okp x (,utype-integer-value y))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,shl-utype-utype ((x ,utypep) (y ,utypep))
              :guard (,shl-utype-utype-okp x y)
              :returns (result ,utypep)
              :short ,(concatenate 'string
                                   "Left shift of @('unsigned "
                                   type-string
                                   "') values by @('unsigned "
                                   type-string
                                   "') values [C:6.5.7].")
              (,shl-utype x (,utype-integer-value y))
              :guard-hints (("Goal" :in-theory (enable ,shl-utype-utype-okp)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,shr-stype-stype-okp ((x ,stypep) (y ,stypep))
              :returns (yes/no booleanp)
              :short ,(concatenate 'string
                                   "Check if right shift of @('signed "
                                   type-string
                                   "') values by @('signed "
                                   type-string
                                   "') values is well-defined.")
              (,shr-stype-okp x (,stype-integer-value y))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,shr-stype-stype ((x ,stypep) (y ,stypep))
              :guard (,shr-stype-stype-okp x y)
              :returns (result ,stypep)
              :short ,(concatenate 'string
                                   "Right shift of @('signed "
                                   type-string
                                   "') values by @('signed "
                                   type-string
                                   "') values [C:6.5.7].")
              (,shr-stype x (,stype-integer-value y))
              :guard-hints (("Goal" :in-theory (enable ,shr-stype-stype-okp)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,shr-utype-utype-okp ((x ,utypep) (y ,utypep))
              :returns (yes/no booleanp)
              :short ,(concatenate 'string
                                   "Check if right shift of @('unsigned "
                                   type-string
                                   "') values by @('unsigned "
                                   type-string
                                   "') values is well-defined.")
              (,shr-utype-okp x (,utype-integer-value y))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,shr-utype-utype ((x ,utypep) (y ,utypep))
              :guard (,shr-utype-utype-okp x y)
              :returns (result ,utypep)
              :short ,(concatenate 'string
                                   "Left shift of @('unsigned "
                                   type-string
                                   "') values by @('unsigned "
                                   type-string
                                   "') values [C:6.5.7].")
              (,shr-utype x (,utype-integer-value y))
              :guard-hints (("Goal" :in-theory (enable ,shr-utype-utype-okp)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,lt-stype-stype ((x ,stypep) (y ,stypep))
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

            (define ,lt-utype-utype ((x ,utypep) (y ,utypep))
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

            (define ,gt-stype-stype ((x ,stypep) (y ,stypep))
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

            (define ,gt-utype-utype ((x ,utypep) (y ,utypep))
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

            (define ,le-stype-stype ((x ,stypep) (y ,stypep))
              :returns (result sintp)
              :short ,(concatenate
                       'string
                       "Less-than-or-equal-to relation of @('signed "
                       type-string
                       "') values [C:6.5.8].")
              (if (<= (,stype->get x) (,stype->get y))
                  (sint 1)
                (sint 0))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,le-utype-utype ((x ,utypep) (y ,utypep))
              :returns (result sintp)
              :short ,(concatenate
                       'string
                       "Less-than-or-equal-to relation of @('unsigned "
                       type-string
                       "') values [C:6.5.8].")
              (if (<= (,utype->get x) (,utype->get y))
                  (sint 1)
                (sint 0))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,ge-stype-stype ((x ,stypep) (y ,stypep))
              :returns (result sintp)
              :short ,(concatenate
                       'string
                       "Greater-than-or-equal-to relation of @('signed "
                       type-string
                       "') values [C:6.5.8].")
              (if (>= (,stype->get x) (,stype->get y))
                  (sint 1)
                (sint 0))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,ge-utype-utype ((x ,utypep) (y ,utypep))
              :returns (result sintp)
              :short ,(concatenate
                       'string
                       "Greater-than-or-equal-to relation of @('unsigned "
                       type-string
                       "') values [C:6.5.8].")
              (if (>= (,utype->get x) (,utype->get y))
                  (sint 1)
                (sint 0))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,eq-stype-stype ((x ,stypep) (y ,stypep))
              :returns (result sintp)
              :short ,(concatenate
                       'string
                       "Equality of @('signed "
                       type-string
                       "') values [C:6.5.9].")
              (if (= (,stype->get x) (,stype->get y))
                  (sint 1)
                (sint 0))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,eq-utype-utype ((x ,utypep) (y ,utypep))
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

            (define ,ne-stype-stype ((x ,stypep) (y ,stypep))
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

            (define ,ne-utype-utype ((x ,utypep) (y ,utypep))
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

            (define ,bitand-stype-stype ((x ,stypep) (y ,stypep))
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
              :prepwork
              ((local (include-book "ihs/logops-lemmas" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,bitand-utype-utype ((x ,utypep) (y ,utypep))
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
              :prepwork
              ((local (include-book "ihs/logops-lemmas" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,bitxor-stype-stype ((x ,stypep) (y ,stypep))
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
              ((local
                (include-book "centaur/bitops/ihs-extensions" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,bitxor-utype-utype ((x ,utypep) (y ,utypep))
              :returns (result ,utypep)
              :short ,(concatenate
                       'string
                       "Bitwise exclusive disjunction of @('unsigned "
                       type-string
                       "') values [C:6.5.10].")
              (,utype (logxor (,utype->get x) (,utype->get y)))
              :guard-hints (("Goal" :in-theory (enable ,utype-integerp
                                                       ,utypep
                                                       ,utype->get)))
              :hooks (:fix)
              :prepwork
              ((local
                (include-book "centaur/bitops/ihs-extensions" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,bitior-stype-stype ((x ,stypep) (y ,stypep))
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
              ((local
                (include-book "centaur/bitops/ihs-extensions" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,bitior-utype-utype ((x ,utypep) (y ,utypep))
              :returns (result ,utypep)
              :short ,(concatenate
                       'string
                       "Bitwise inclusive disjunction of @('unsigned "
                       type-string
                       "') values [C:6.5.12].")
              (,utype (logior (,utype->get x) (,utype->get y)))
              :hooks (:fix)
              :guard-hints (("Goal" :in-theory (enable ,utype-integerp
                                                       ,utypep
                                                       ,utype->get)))
              :prepwork
              ((local
                (include-book "centaur/bitops/ihs-extensions" :dir :system))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,logand-stype-stype ((x ,stypep) (y ,stypep))
              :returns (result sintp)
              :short ,(concatenate 'string
                                   "Logical conjunction of @('signed "
                                   type-string
                                   "') values [C:6.5.13].")
              (sint01 (and (,stype-nonzerop x) (,stype-nonzerop y)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,logand-utype-utype ((x ,utypep) (y ,utypep))
              :returns (result sintp)
              :short ,(concatenate 'string
                                   "Logical conjunction of @('unsigned "
                                   type-string
                                   "') values [C:6.5.13].")
              (sint01 (and (,utype-nonzerop x) (,utype-nonzerop y)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,logor-stype-stype ((x ,stypep) (y ,stypep))
              :returns (result sintp)
              :short ,(concatenate 'string
                                   "Logical disjunction of @('signed "
                                   type-string
                                   "') values [C:6.5.14].")
              (sint01 (or (,stype-nonzerop x) (,stype-nonzerop y)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (define ,logor-utype-utype ((x ,utypep) (y ,utypep))
              :returns (result sintp)
              :short ,(concatenate 'string
                                   "Logical disjunction of @('unsigned "
                                   type-string
                                   "') values [C:6.5.14].")
              (sint01 (or (,utype-nonzerop x) (,utype-nonzerop y)))
              :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(atc-def-integer-operations :char)

(atc-def-integer-operations :short)

(atc-def-integer-operations :int)

(atc-def-integer-operations :long)

(atc-def-integer-operations :llong)
