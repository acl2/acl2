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
(include-book "static-semantics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-integer-operations
  :parents (atc-dynamic-semantics)
  :short "A model of C integer operations for ATC."
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
    "We introduce functions for the unary and strict binary operators,
     as detailed below.
     We do not introduce functions for the non-strict binary operators,
     because those are modeled via ACL2's @(tsee and) and @(tsee or),
     which are also non-strict.")
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
     only the (mathematical) integer value of the second operand does.")
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
     The left operand, when signed, must be non-negative.
     These requirements are captured in the guards.")
   (xdoc::p
    "For division and remainder,
     the guard also requires the divisor to be non-zero.")
   (xdoc::p
    "The relational and equality operators,
     as well as the logical negation, conjunction, and disjunction operations,
     always return @('int'), regardless of the types of the operands.")
   (xdoc::p
    "The bitwise operations assume a two's complement representation,
     which is consistent with "
    (xdoc::seetopic "atc-integer-formats" "our model of integer values")
    "; these operations depend on the C representation of integers [C:6.5/4]."))
  :order-subtopics t
  :default-parent t)

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

(define atc-def-integer-operations-1 ((type1 typep))
  :guard (type-integerp type1)
  :returns (event pseudo-event-formp)
  :short "Event to generate the ACL2 models of
          the C integer operations that involve one integer type."
  :long
  (xdoc::topstring
   (xdoc::p
    "These include not only the unary operators,
     but also versions of the shift operators
     that take ACL2 integers as second operands.
     The latter are used in the definition of the shift operators
     whose second operands are C integers;
     see @(tsee atc-def-integer-operations-2).")
   (xdoc::p
    "For unary plus, unary minus, and bitwise complement,
     we generate different definitions based on whether
     the type has the rank of @('int') or higher, or not:
     if it does, we generate a definition that performs a direct computation;
     if it does not, we generate a definition that
     converts and then calls the function for the promoted type."))

  (b* ((type1-string (atc-integer-type-string type1))
       (type (promote-type type1))
       (samep (equal type type1))
       (signedp (type-signed-integerp type))
       (<type1>-bits (atc-integer-type-bits type1))
       (<type1> (atc-integer-type-fixtype type1))
       (<type1>p (pack <type1> 'p))
       (<type1>->get (pack <type1> '->get))
       (<type1>-mod (pack <type1> '-mod))
       (<type1>-integerp (pack <type1> '-integerp))
       (<type1>-integerp-alt-def (pack <type1>-integerp '-alt-def))
       (<type1>-fix (pack <type1> '-fix))
       (<type1>-const (pack <type1> '-const))
       (<type1>-nonzerop (pack <type1> '-nonzerop))
       (<type1>-integer-value (pack <type1> '-integer-value))
       (<type> (atc-integer-type-fixtype type))
       (<type>p (pack <type> 'p))
       (<type>-min (pack <type> '-min))
       (<type>-max (pack <type> '-max))
       (<type>-from-<type1> (pack <type> '-from- <type1>))
       (plus-<type1> (pack 'plus- <type1>))
       (plus-<type> (pack 'plus- <type>))
       (minus-<type1> (pack 'minus- <type1>))
       (minus-<type1>-okp (pack minus-<type1> '-okp))
       (minus-<type> (pack 'minus- <type>))
       (minus-<type>-okp (pack minus-<type> '-okp))
       (bitnot-<type1> (pack 'bitnot- <type1>))
       (bitnot-<type> (pack 'bitnot- <type>))
       (lognot-<type1> (pack 'lognot- <type1>))
       (shl-<type1> (pack 'shl- <type1>))
       (shl-<type1>-okp (pack shl-<type1> '-okp))
       (shl-<type> (pack 'shl- <type>))
       (shl-<type>-okp (pack shl-<type> '-okp))
       (shr-<type1> (pack 'shr- <type1>))
       (shr-<type1>-okp (pack shr-<type1> '-okp))
       (shr-<type> (pack 'shr- <type>))
       (shr-<type>-okp (pack shr-<type> '-okp)))

    `(progn

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          samep
          `((define ,<type1>-const ((x natp))
              :guard (,<type1>-integerp x)
              :returns (result ,<type1>p)
              :short ,(str::cat "Integer constant of " type1-string ".")
              (,<type1> x))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type1>-nonzerop ((x ,<type1>p))
         :returns (yes/no booleanp)
         :short ,(str::cat "Check if a value of " type1-string " is not 0.")
         (/= (,<type1>->get x) 0)
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type1>-integer-value ((x ,<type1>p))
         :returns (ival integerp)
         :short ,(str::cat "Turn a vaue of "
                           type1-string
                           " into an ACL2 integer value.")
         (,<type1>->get x)
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,plus-<type1> ((x ,<type1>p))
         :returns (result ,<type>p)
         :short ,(str::cat "Unary plus of a value of "
                           type1-string
                           " [C:6.5.3].")
         ,(if samep
              `(,<type1>-fix x)
            `(,plus-<type> (,<type>-from-<type1> x)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          signedp
          `((define ,minus-<type1>-okp ((x ,<type1>p))
              :returns (yes/no booleanp)
              :short ,(str::cat "Check if the unary minus of a value of "
                                type1-string
                                " is well-defined.")
              ,(if samep
                   `(,<type1>-integerp (- (,<type1>->get x)))
                 `(,minus-<type>-okp (,<type>-from-<type1> x)))
              :hooks (:fix))))

       ;;;;;;;;;;;;;;;;;;;;

       (define ,minus-<type1> ((x ,<type1>p))
         ,@(and signedp `(:guard (,minus-<type1>-okp x)))
         :returns (result ,<type>p)
         :short ,(str::cat "Unary minus of a value of "
                           type1-string
                           " [C:6.5.3].")
         ,(if samep
              `(,(if signedp <type1> <type1>-mod) (- (,<type1>->get x)))
            `(,minus-<type> (,<type>-from-<type1> x)))
         ,@(and
            signedp
            `(:guard-hints (("Goal" :in-theory (enable ,minus-<type1>-okp)))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,bitnot-<type1> ((x ,<type1>p))
         :returns (result ,<type>p)
         :short ,(str::cat "Bitwise complement of a value of "
                           type1-string
                           " [C:6.5.3].")
         ,(if samep
              `(,(if signedp <type1> <type1>-mod) (lognot (,<type1>->get x)))
            `(,bitnot-<type> (,<type>-from-<type1> x)))
         ,@(and samep
                signedp
                `(:guard-hints
                  (("Goal" :in-theory (enable ,<type1>-integerp-alt-def
                                              ,<type1>->get
                                              ,<type1>p
                                              (:e ,<type>-min)
                                              (:e ,<type>-max))))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,lognot-<type1> ((x ,<type1>p))
         :returns (result sintp)
         :short ,(str::cat "Logical complement of a value of "
                           type1-string
                           " [C:6.5.3].")
         (sint01 (= (,<type1>->get x) 0))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,shl-<type1>-okp ((x ,<type1>p) (y integerp))
         ,@(and samep
                (not signedp)
                `((declare (ignore x))))
         :returns (yes/no booleanp)
         :short ,(str::cat "Check if the left shift of a value of "
                           type1-string
                           " by an integer is well-defined.")
         ,(if samep
              (if signedp
                  `(and (integer-range-p 0 (,<type1>-bits) (ifix y))
                        (>= (,<type1>->get x) 0)
                        (,<type1>-integerp (* (,<type1>->get x)
                                              (expt 2 (ifix y)))))
                `(integer-range-p 0 (,<type1>-bits) (ifix y)))
            `(,shl-<type>-okp (,<type>-from-<type1> x) (ifix y)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;

       (define ,shl-<type1> ((x ,<type1>p) (y integerp))
         :guard (,shl-<type1>-okp x y)
         :returns (result ,<type>p)
         :short ,(str::cat "Left shift of a value of "
                           type1-string
                           " by an integer [C:6.5.7].")
         ,(if samep
              `(,(if signedp <type1> <type1>-mod) (* (,<type1>->get x)
                                                     (expt 2 (ifix y))))
            `(,shl-<type> (,<type>-from-<type1> x) y))
         :guard-hints (("Goal" :in-theory (enable ,shl-<type1>-okp)))
         ,@(and (not signedp)
                '(:prepwork
                  ((local (include-book "arithmetic-3/top" :dir :system)))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,shr-<type1>-okp ((x ,<type1>p) (y integerp))
         ,@(and samep
                (not signedp)
                `((declare (ignore x))))
         :returns (yes/no booleanp)
         :short ,(str::cat "Check if the right shift of a value of "
                           type1-string
                           " by an integer is well-defined.")
         ,(if samep
              (if signedp
                  `(and (integer-range-p 0 (,<type1>-bits) (ifix y))
                        (>= (,<type1>->get x) 0))
                `(integer-range-p 0 (,<type1>-bits) (ifix y)))
            `(,shr-<type>-okp (,<type>-from-<type1> x) (ifix y)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;

       (define ,shr-<type1> ((x ,<type1>p) (y integerp))
         :guard (,shr-<type1>-okp x y)
         :returns (result ,<type>p)
         :short ,(str::cat "Right shift of a value of "
                           type1-string
                           " by an integer C:6.5.7].")
         ,(if samep
              `(,(if signedp <type1> <type1>-mod) (truncate (,<type1>->get x)
                                                            (expt 2 (ifix y))))
            `(,shr-<type> (,<type>-from-<type1> x) y))
         :guard-hints (("Goal"
                        :in-theory (enable ,@(if (and samep
                                                      signedp)
                                                 (list shr-<type1>-okp
                                                       <type1>-integerp
                                                       <type1>->get
                                                       <type1>p)
                                               (list shr-<type1>-okp)))))
         ,@(and
            signedp
            '(:prepwork
              ((local
                (include-book "kestrel/arithmetic-light/expt" :dir :system))
               (local
                (include-book "kestrel/arithmetic-light/truncate" :dir :system)))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-operations-1-loop ((types type-listp))
  :guard (type-integer-listp types)
  :returns (events pseudo-event-form-listp)
  :short "Events to generate the ACL2 models of the C integer operations
          that involve each one integer type from a list."
  (cond ((endp types) nil)
        (t (cons (atc-def-integer-operations-1 (car types))
                 (atc-def-integer-operations-1-loop (cdr types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 ;; It is critical to generate the operations for SINT and UINT
 ;; before the ones for SCHAR and UCHAR and SSHORT and USHORT,
 ;; because the latter are defined in terms of the former.
 ;; See :DOC ATC-DEF-INTEGER-OPERATIONS-1.
 (b* ((types (list (type-sint)
                   (type-uint)
                   (type-slong)
                   (type-ulong)
                   (type-sllong)
                   (type-ullong)
                   (type-schar)
                   (type-uchar)
                   (type-sshort)
                   (type-ushort))))
   `(progn ,@(atc-def-integer-operations-1-loop types))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-operations-2 ((type1 typep) (type2 typep))
  :guard (and (type-integerp type1) (type-integerp type2))
  :guard-hints (("Goal" :in-theory (enable type-arithmeticp type-realp)))
  :returns (event pseudo-event-formp)
  :short "Event to generate the ACL2 models of
          the C integer operations that involve two integer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "These include all the strict binary operators;
     the non-strict ones are represented
     via ACL2's @(tsee and) and @(tsee or) instead
     (in combination with other ACL2 functions in our C model)."))

  (b* ((type1-string (atc-integer-type-string type1))
       (type2-string (atc-integer-type-string type2))
       (type (uaconvert-types type1 type2))
       (samep (and (equal type type1) (equal type type2)))
       (signedp (type-signed-integerp type))
       (ptype1 (promote-type type1))
       (<type1> (atc-integer-type-fixtype type1))
       (<type2> (atc-integer-type-fixtype type2))
       (<type> (atc-integer-type-fixtype type))
       (<ptype1> (atc-integer-type-fixtype ptype1))
       (<type1>p (pack <type1> 'p))
       (<type2>p (pack <type2> 'p))
       (<type>p (pack <type> 'p))
       (<ptype1>p (pack <ptype1> 'p))
       (<type1>->get (pack <type1> '->get))
       (<type2>->get (pack <type2> '->get))
       (<type>-mod (pack <type> '-mod))
       (<type2>-integer-value (pack <type2> '-integer-value))
       (<type>-integerp (pack <type> '-integerp))
       (<type>-from-<type1> (pack <type> '-from- <type1>))
       (<type>-from-<type2> (pack <type> '-from- <type2>))
       (add-<type1>-<type2> (pack 'add- <type1> '- <type2>))
       (add-<type1>-<type2>-okp (pack add-<type1>-<type2> '-okp))
       (add-<type>-<type> (pack 'add- <type> '- <type>))
       (add-<type>-<type>-okp (pack add-<type>-<type> '-okp))
       (sub-<type1>-<type2> (pack 'sub- <type1> '- <type2>))
       (sub-<type1>-<type2>-okp (pack sub-<type1>-<type2> '-okp))
       (sub-<type>-<type> (pack 'sub- <type> '- <type>))
       (sub-<type>-<type>-okp (pack sub-<type>-<type> '-okp))
       (mul-<type1>-<type2> (pack 'mul- <type1> '- <type2>))
       (mul-<type1>-<type2>-okp (pack mul-<type1>-<type2> '-okp))
       (mul-<type>-<type> (pack 'mul- <type> '- <type>))
       (mul-<type>-<type>-okp (pack mul-<type>-<type> '-okp))
       (div-<type1>-<type2> (pack 'div- <type1> '- <type2>))
       (div-<type1>-<type2>-okp (pack div-<type1>-<type2> '-okp))
       (div-<type>-<type> (pack 'div- <type> '- <type>))
       (div-<type>-<type>-okp (pack div-<type>-<type> '-okp))
       (rem-<type1>-<type2> (pack 'rem- <type1> '- <type2>))
       (rem-<type1>-<type2>-okp (pack rem-<type1>-<type2> '-okp))
       (rem-<type>-<type> (pack 'rem- <type> '- <type>))
       (rem-<type>-<type>-okp (pack rem-<type>-<type> '-okp))
       (shl-<type1>-<type2> (pack 'shl- <type1> '- <type2>))
       (shl-<type1>-<type2>-okp (pack shl-<type1>-<type2> '-okp))
       (shl-<type1> (pack 'shl- <type1>))
       (shl-<type1>-okp (pack shl-<type1> '-okp))
       (shr-<type1>-<type2> (pack 'shr- <type1> '- <type2>))
       (shr-<type1>-<type2>-okp (pack shr-<type1>-<type2> '-okp))
       (shr-<type1> (pack 'shr- <type1>))
       (shr-<type1>-okp (pack shr-<type1> '-okp))
       (lt-<type1>-<type2> (pack 'lt- <type1> '- <type2>))
       (lt-<type>-<type> (pack 'lt- <type> '- <type>))
       (gt-<type1>-<type2> (pack 'gt- <type1> '- <type2>))
       (gt-<type>-<type> (pack 'gt- <type> '- <type>))
       (le-<type1>-<type2> (pack 'le- <type1> '- <type2>))
       (le-<type>-<type> (pack 'le- <type> '- <type>))
       (ge-<type1>-<type2> (pack 'ge- <type1> '- <type2>))
       (ge-<type>-<type> (pack 'ge- <type> '- <type>))
       (eq-<type1>-<type2> (pack 'eq- <type1> '- <type2>))
       (eq-<type>-<type> (pack 'eq- <type> '- <type>))
       (ne-<type1>-<type2> (pack 'ne- <type1> '- <type2>))
       (ne-<type>-<type> (pack 'ne- <type> '- <type>))
       (bitand-<type1>-<type2> (pack 'bitand- <type1> '- <type2>))
       (bitand-<type>-<type> (pack 'bitand- <type> '- <type>))
       (bitxor-<type1>-<type2> (pack 'bitxor- <type1> '- <type2>))
       (bitxor-<type>-<type> (pack 'bitxor- <type> '- <type>))
       (bitior-<type1>-<type2> (pack 'bitior- <type1> '- <type2>))
       (bitior-<type>-<type> (pack 'bitior- <type> '- <type>)))

    `(progn

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          signedp
          `((define ,add-<type1>-<type2>-okp ((x ,<type1>p) (y ,<type2>p))
              :returns (yes/no booleanp)
              :short ,(str::cat "Check if the addition of a value of "
                                type1-string
                                " and a value of "
                                type2-string
                                " is well-defined.")
              ,(if samep
                   `(,<type>-integerp (+ (,<type1>->get x)
                                         (,<type2>->get y)))
                 `(,add-<type>-<type>-okp
                   ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
                   ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
              :hooks (:fix))))

       ;;;;;;;;;;;;;;;;;;;;

       (define ,add-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         ,@(and signedp `(:guard (,add-<type1>-<type2>-okp x y)))
         :returns (result ,<type>p)
         :short ,(str::cat "Addition of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.6].")
         ,(if samep
              `(,(if signedp <type> <type>-mod) (+ (,<type1>->get x)
                                                   (,<type2>->get y)))
            `(,add-<type>-<type>
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         ,@(and signedp
                `(:guard-hints
                  (("Goal" :in-theory (enable ,add-<type1>-<type2>-okp)))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          signedp
          `((define ,sub-<type1>-<type2>-okp ((x ,<type1>p) (y ,<type2>p))
              :returns (yes/no booleanp)
              :short ,(str::cat "Check if the subtraction of a value of "
                                type1-string
                                " and a value of "
                                type2-string
                                " is well-defined.")
              ,(if samep
                   `(,<type>-integerp (- (,<type1>->get x)
                                         (,<type2>->get y)))
                 `(,sub-<type>-<type>-okp
                   ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
                   ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
              :hooks (:fix))))

       ;;;;;;;;;;;;;;;;;;;;

       (define ,sub-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         ,@(and signedp `(:guard (,sub-<type1>-<type2>-okp x y)))
         :returns (result ,<type>p)
         :short ,(str::cat "Subtraction of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.6].")
         ,(if samep
              `(,(if signedp <type> <type>-mod) (- (,<type1>->get x)
                                                   (,<type2>->get y)))
            `(,sub-<type>-<type>
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         ,@(and signedp
                `(:guard-hints
                  (("Goal" :in-theory (enable ,sub-<type1>-<type2>-okp)))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          signedp
          `((define ,mul-<type1>-<type2>-okp ((x ,<type1>p) (y ,<type2>p))
              :returns (yes/no booleanp)
              :short ,(str::cat "Check if the multiplication of a value of "
                                type1-string
                                " and a value of "
                                type2-string
                                " is well-defined.")
              ,(if samep
                   `(,<type>-integerp (* (,<type1>->get x)
                                         (,<type2>->get y)))
                 `(,mul-<type>-<type>-okp
                   ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
                   ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
              :hooks (:fix))))

       ;;;;;;;;;;;;;;;;;;;;

       (define ,mul-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         ,@(and signedp `(:guard (,mul-<type1>-<type2>-okp x y)))
         :returns (result ,<type>p)
         :short ,(str::cat "Multiplication of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.5].")
         ,(if samep
              `(,(if signedp <type> <type>-mod) (* (,<type1>->get x)
                                                   (,<type2>->get y)))
            `(,mul-<type>-<type>
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         ,@(and signedp
                `(:guard-hints
                  (("Goal" :in-theory (enable ,mul-<type1>-<type2>-okp)))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,div-<type1>-<type2>-okp ((x ,<type1>p) (y ,<type2>p))
         ,@(and samep
                (not signedp)
                `((declare (ignore x))))
         :returns (yes/no booleanp)
         :short ,(str::cat "Check if the division of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " is well-defined.")
         ,(if samep
              (if signedp
                  `(and (not (equal (,<type2>->get y) 0))
                        (,<type>-integerp (truncate (,<type1>->get x)
                                                    (,<type2>->get y))))
                `(not (equal (,<type2>->get y) 0)))
            `(,div-<type>-<type>-okp
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;

       (define ,div-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         :guard (,div-<type1>-<type2>-okp x y)
         :returns (result ,<type>p)
         :short ,(str::cat "Division of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.5].")
         ,(if samep
              `(,(if signedp <type> <type>-mod) (truncate (,<type1>->get x)
                                                          (,<type2>->get y)))
            `(,div-<type>-<type>
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         :guard-hints (("Goal" :in-theory (enable ,div-<type1>-<type2>-okp)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,rem-<type1>-<type2>-okp ((x ,<type1>p) (y ,<type2>p))
         ,@(and samep
                (not signedp)
                `((declare (ignore x))))
         :returns (yes/no booleanp)
         :short ,(str::cat "Check if the remainder of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " is well-defined.")
         ,(if samep
              (if signedp
                  `(and (not (equal (,<type2>->get y) 0))
                        (,<type>-integerp (rem (,<type1>->get x)
                                               (,<type2>->get y))))
                `(not (equal (,<type2>->get y) 0)))
            `(,rem-<type>-<type>-okp
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;

       (define ,rem-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         :guard (,rem-<type1>-<type2>-okp x y)
         :returns (result ,<type>p)
         :short ,(str::cat "Remainder of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.5].")
         ,(if samep
              `(,(if signedp <type> <type>-mod) (rem (,<type1>->get x)
                                                     (,<type2>->get y)))
            `(,rem-<type>-<type>
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         :guard-hints (("Goal" :in-theory (enable ,rem-<type1>-<type2>-okp)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,shl-<type1>-<type2>-okp ((x ,<type1>p) (y ,<type2>p))
         :returns (yes/no booleanp)
         :short ,(str::cat "Check if the left shift of a value of "
                           type1-string
                           " by a value of "
                           type2-string
                           " is well-defined.")
         (,shl-<type1>-okp x (,<type2>-integer-value y))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;

       (define ,shl-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         :guard (,shl-<type1>-<type2>-okp x y)
         :returns (result ,<ptype1>p)
         :short ,(str::cat "Left shift of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.7].")
         (,shl-<type1> x (,<type2>-integer-value y))
         :guard-hints (("Goal" :in-theory (enable ,shl-<type1>-<type2>-okp)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,shr-<type1>-<type2>-okp ((x ,<type1>p) (y ,<type2>p))
         :returns (yes/no booleanp)
         :short ,(str::cat "Check if the right shift of a value of "
                           type1-string
                           " by a value of "
                           type2-string
                           " is well-defined.")
         (,shr-<type1>-okp x (,<type2>-integer-value y))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;

       (define ,shr-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         :guard (,shr-<type1>-<type2>-okp x y)
         :returns (result ,<ptype1>p)
         :short ,(str::cat "Right shift of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.7].")
         (,shr-<type1> x (,<type2>-integer-value y))
         :guard-hints (("Goal" :in-theory (enable ,shr-<type1>-<type2>-okp)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,lt-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         :returns (result sintp)
         :short ,(str::cat "Less-than relation of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.8].")
         ,(if samep
              `(if (< (,<type1>->get x)
                      (,<type2>->get y))
                   (sint 1)
                 (sint 0))
            `(,lt-<type>-<type>
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,gt-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         :returns (result sintp)
         :short ,(str::cat "Greater-than relation of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.8].")
         ,(if samep
              `(if (> (,<type1>->get x)
                      (,<type2>->get y))
                   (sint 1)
                 (sint 0))
            `(,gt-<type>-<type>
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,le-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         :returns (result sintp)
         :short ,(str::cat "Less-than-or-equal-to relation of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.8].")
         ,(if samep
              `(if (<= (,<type1>->get x)
                       (,<type2>->get y))
                   (sint 1)
                 (sint 0))
            `(,le-<type>-<type>
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,ge-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         :returns (result sintp)
         :short ,(str::cat "Greater-than-or-equal-to relation of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.8].")
         ,(if samep
              `(if (>= (,<type1>->get x)
                       (,<type2>->get y))
                   (sint 1)
                 (sint 0))
            `(,ge-<type>-<type>
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,eq-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         :returns (result sintp)
         :short ,(str::cat "Equality of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.9].")
         ,(if samep
              `(if (= (,<type1>->get x)
                      (,<type2>->get y))
                   (sint 1)
                 (sint 0))
            `(,eq-<type>-<type>
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,ne-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         :returns (result sintp)
         :short ,(str::cat "Non-equality of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.9].")
         ,(if samep
              `(if (/= (,<type1>->get x)
                       (,<type2>->get y))
                   (sint 1)
                 (sint 0))
            `(,ne-<type>-<type>
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,bitand-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         :returns (result ,<type>p)
         :short ,(str::cat "Bitwise conjunction of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.10].")
         ,(if samep
              `(,(if signedp <type> <type>-mod) (logand (,<type1>->get x)
                                                        (,<type2>->get y)))
            `(,bitand-<type>-<type>
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         :prepwork ((local (include-book "ihs/logops-lemmas" :dir :system)))
         ,@(and samep
                `(:guard-hints
                  (("Goal"
                    :in-theory (enable ,<type>-integerp ,<type>p ,<type1>->get)))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,bitxor-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         :returns (result ,<type>p)
         :short ,(str::cat "Bitwise exclusive disjunction of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.11].")
         ,(if samep
              `(,(if signedp <type> <type>-mod) (logxor (,<type1>->get x)
                                                        (,<type2>->get y)))
            `(,bitxor-<type>-<type>
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         :prepwork
         ((local (include-book "centaur/bitops/ihs-extensions" :dir :system)))
         ,@(and samep
                `(:guard-hints
                  (("Goal"
                    :in-theory (enable ,<type>-integerp ,<type>p ,<type1>->get)))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,bitior-<type1>-<type2> ((x ,<type1>p) (y ,<type2>p))
         :returns (result ,<type>p)
         :short ,(str::cat "Bitwise inclusive disjunction of a value of "
                           type1-string
                           " and a value of "
                           type2-string
                           " [C:6.5.12].")
         ,(if samep
              `(,(if signedp <type> <type>-mod) (logior (,<type1>->get x)
                                                        (,<type2>->get y)))
            `(,bitior-<type>-<type>
              ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
              ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
         :prepwork
         ((local (include-book "centaur/bitops/ihs-extensions" :dir :system)))
         ,@(and samep
                `(:guard-hints
                  (("Goal"
                    :in-theory (enable ,<type>-integerp ,<type>p ,<type1>->get)))))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-operations-2-loop-same ((types type-listp))
  :guard (type-integer-listp types)
  :returns (events pseudo-event-form-listp)
  (cond ((endp types) nil)
        (t (cons (atc-def-integer-operations-2 (car types) (car types))
                 (atc-def-integer-operations-2-loop-same (cdr types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-operations-2-loop-inner ((type typep)
                                                 (types type-listp))
  :guard (and (type-integerp type)
              (type-integer-listp types))
  :returns (events pseudo-event-form-listp)
  (cond ((endp types) nil)
        ((equal type (car types)) (atc-def-integer-operations-2-loop-inner
                                   type (cdr types)))
        (t (cons (atc-def-integer-operations-2 type (car types))
                 (atc-def-integer-operations-2-loop-inner type (cdr types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-operations-2-loop-outer ((types type-listp)
                                                 (types1 type-listp))
  :guard (and (type-integer-listp types)
              (type-integer-listp types1))
  :returns (events pseudo-event-form-listp)
  (cond ((endp types) nil)
        (t (append
            (atc-def-integer-operations-2-loop-inner (car types) types1)
            (atc-def-integer-operations-2-loop-outer (cdr types) types1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 (b* ((types (list (type-sint)
                   (type-uint)
                   (type-slong)
                   (type-ulong)
                   (type-sllong)
                   (type-ullong)
                   (type-schar)
                   (type-uchar)
                   (type-sshort)
                   (type-ushort))))
   `(progn ,@(atc-def-integer-operations-2-loop-same types)
           ,@(atc-def-integer-operations-2-loop-outer types types))))

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
       (stypep (add-suffix stype "P"))
       (utypep (add-suffix utype "P"))
       (stype-nonzerop (add-suffix stype "-NONZEROP"))
       (utype-nonzerop (add-suffix utype "-NONZEROP"))
       (logand-stype-stype (acl2::packn-pos (list "LOGAND-" stype "-" stype) 'atc))
       (logand-utype-utype (acl2::packn-pos (list "LOGAND-" utype "-" utype) 'atc))
       (logor-stype-stype (acl2::packn-pos (list "LOGOR-" stype "-" stype) 'atc))
       (logor-utype-utype (acl2::packn-pos (list "LOGOR-" utype "-" utype) 'atc)))

    `(progn

       ,@(and
          (member-eq type '(:int :long :llong))
          `(

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
