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

(include-book "integer-conversions")

(include-book "../language/static-semantics")

(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ representation-of-integer-operations
  :parents (representation)
  :short "A representation of C integer operations in ACL2."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is part of the "
    (xdoc::seetopic "representation" "shallow embedding")
    ".")
   (xdoc::p
    "We define ACL2 functions that model C operations on
     the integer types supported in our model,
     namely the standard unsigned and signed integers, except @('_Bool').")
   (xdoc::p
    "We introduce functions @('<type>-<base>-const')
     to construct integer constants.
     Following [C17:6.4.4.1], these have non-negative values
     and may have only certain integer types,
     namely those with the same rank as @('int') or higher.
     Thus we introduce three functions for each integer type in those ranks,
     one function per possible base (decimal, octal, hexadecimal).
     Each takes a natural number as argument,
     which the guard further constrains to be representable in the type.
     The three functions for the three bases have the same definition,
     but they represent syntactically different constants in C.")
   (xdoc::p
    "We introduce functions @('boolean-from-<type>')
     to turn C integers into ACL2 booleans,
     i.e. to test whether the integers are not zero.
     These are used to represent shallowly embedded tests.
     We introduce a function for each integer type.")
   (xdoc::p
    "We introduce a single function @(tsee sint-from-boolean)
     to turn ACL2 booleans into the @('int') 0 or 1 (for false and true).
     This function is used in the ACL2 representation of
     non-strict C conjunctions @('&&') and disjunctions @('||'),
     which always return @('int') 0 or 1 [C17:6.5.13/3] [C17:6.5.14/3].
     We do not need similar functions for other types,
     because the 0 or 1 are always @('int')
     for operations like @('&&') and @('||').")
   (xdoc::p
    "We introduce functions for the unary and strict pure binary operators,
     as detailed below.
     We do not introduce functions for the non-strict binary operators,
     because those are modeled via ACL2's @(tsee and) and @(tsee or),
     which are also non-strict.
     We do not introduce functions for the non-pure binary operators
     (i.e. assignments), because they are modeled differently in ACL2.")
   (xdoc::p
    "For each unary operator, we introduce a function for each integer type.
     The function takes an argument of that integer type,
     and returns a result of possibly different type.
     For all the unary integer operators except @('!'),
     C promotes operands [C17:6.3.1.1/2] to types of rank @('int') or higher,
     and that is also the result of the operator.
     C does not promote the operand of @('!');
     this operator always returns an @('int').")
   (xdoc::p
    "For all the binary integer operators
     except @('<<'), @('>>'), @('&&'), and @('||'),
     C subjects the operands to the usual arithmetic conversions [C17:6.3.1.8],
     which involve promoting them [C17:6.3.1.1/2]
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
     the behavior is undefined [C17:6.5/5]:
     our functions for signed integer operations
     have guards requiring the results to be representable.")
   (xdoc::p
    "Arithmetic on unsigned integers is modular [C17:6.2.5/9].")
   (xdoc::p
    "The right operand of a signed shift operator
     must be non-negative and below the bit size of the left operand
     [C17:6.5.7/3].
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
    (xdoc::seetopic "integer-formats" "our model of integer values")
    "; these operations depend on the C representation of integers [C17:6.5/4]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-from-boolean ((b booleanp))
  :returns (x sintp)
  :short "Turn an ACL2 boolean into an @('int') value 0 or 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is essentially (but not exactly)
     the inverse of @(tsee boolean-from-sint).
     Together with @(tsee boolean-from-sint)
     and other @('boolean-from-...') operations,
     it can be used to represent in ACL2
     shallowly embedded C logical conjunctions and disjunctions,
     which must be integers in C,
     but must be booleans in ACL2 to represent their non-strictness."))
  (if b (sint-from-integer 1) (sint-from-integer 0))
  :hooks (:fix)
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ defun-integer (name
                          &key
                          arg-type
                          arg1-type
                          arg2-type
                          guard
                          res-type
                          short
                          body
                          guard-hints
                          no-fix
                          prepwork)
  :short "Function definition macro specialized for C integer operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ACL2 functions that model the C integer operations (and their guards)
     have a fairly uniform structure.
     This macro generates functions with that structure.")
   (xdoc::p
    "The arguments of this macro are:")
   (xdoc::ul
    (xdoc::li
     "@('name') &mdash; The name of the function.")
    (xdoc::li
     "@('arg-type') &mdash; The argument type, for a unary function.
      The name is always @('x').")
    (xdoc::li
     "@('arg1-type') &mdash; The first argument type, for a binary function.
      The name is always @('x').")
    (xdoc::li
     "@('arg2-type') &mdash; The second argument type, for a binary function.
      The name is always @('y').")
    (xdoc::li
     "@('guard') &mdash; The guard, in addition to the argument type(s).")
    (xdoc::li
     "@('res-type') &mdash; The result type.")
    (xdoc::li
     "@('short') &mdash; The XDOC short string.")
    (xdoc::li
     "@('body') &mdash; The body of the function.")
    (xdoc::li
     "@('guard-hints') &mdash; Hints to verify guards.")
    (xdoc::li
     "@('no-fix') &mdash; Do not generate fixing theorem when non-@('nil')."))
   (xdoc::p
    "The presence (i.e. being non-@('nil')) of @('arg-type')
     determines whether the function is unary or binary.")
   (xdoc::p
    "Besides shortening the formulation of the function definitions,
     this macro results in both faster certification and faster inclusion
     compared to just using @(tsee define), which is not much more verbose.
     Give the large number of functions generated in this file,
     the savings are significant."))
  `(defsection ,name
     :short ,short
     ,@prepwork
     (defun ,name ,(if arg-type '(x) '(x y))
       (declare
        (xargs
         :guard (and ,@(and arg-type `((,arg-type x)))
                     ,@(and arg1-type `((,arg1-type x)))
                     ,@(and arg2-type `((,arg2-type y)))
                     ,@(and guard (list guard)))
         ,@(and guard-hints `(:guard-hints ,guard-hints))))
       ,body)
     (defthm ,(pack res-type '-of- name)
       (,res-type (,name ,@(if arg-type '(x) '(x y)))))
     ,@(and (not no-fix)
            `((fty::deffixequiv ,name
                :args ,(if arg-type
                           `((x ,arg-type))
                         `((x ,arg1-type) (y ,arg2-type))))))
     (in-theory (disable ,name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-integer-operations-1 ((type1 typep))
  :guard (type-nonchar-integerp type1)
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
     see @(tsee def-integer-operations-2).")
   (xdoc::p
    "For unary plus, unary minus, and bitwise complement,
     we generate different definitions based on whether
     the type has the rank of @('int') or higher, or not:
     if it does, we generate a definition that performs a direct computation;
     if it does not, we generate a definition that
     converts and then calls the function for the promoted type."))

  (b* ((type1-string (integer-type-xdoc-string type1))
       (type (promote-type type1))
       (samep (equal type type1))
       (signedp (type-signed-integerp type))
       (<type1>-bits (integer-type-bits-nulfun type1))
       (<type1> (integer-type-to-fixtype type1))
       (<type1>p (pack <type1> 'p))
       (integer-from-<type1> (pack 'integer-from- <type1>))
       (<type1>-from-integer (pack <type1> '-from-integer))
       (<type1>-from-integer-mod (pack <type1>-from-integer '-mod))
       (<type1>-integerp (pack <type1> '-integerp))
       (<type1>-integerp-alt-def (pack <type1>-integerp '-alt-def))
       (<type1>-fix (pack <type1> '-fix))
       (<type1>-dec-const (pack <type1> '-dec-const))
       (<type1>-oct-const (pack <type1> '-oct-const))
       (<type1>-hex-const (pack <type1> '-hex-const))
       (boolean-from-<type1> (pack 'boolean-from- <type1>))
       (<type> (integer-type-to-fixtype type))
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

       (set-ignore-ok t)
       (set-irrelevant-formals-ok t)

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          samep
          `((defun-integer
             ,<type1>-dec-const
             :arg-type natp
             :guard (,<type1>-integerp x)
             :res-type ,<type1>p
             :short ,(str::cat
                      "Decimal integer constant of " type1-string ".")
             :body (,<type1>-from-integer x)
             :no-fix t)))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          samep
          `((defun-integer
             ,<type1>-oct-const
             :arg-type natp
             :guard (,<type1>-integerp x)
             :res-type ,<type1>p
             :short ,(str::cat
                      "Octal integer constant of " type1-string ".")
             :body (,<type1>-from-integer x)
             :no-fix t)))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          samep
          `((defun-integer
             ,<type1>-hex-const
             :arg-type natp
             :guard (,<type1>-integerp x)
             :res-type ,<type1>p
             :short ,(str::cat
                      "Hexadecimal integer constant of " type1-string ".")
             :body (,<type1>-from-integer x)
             :no-fix t)))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,boolean-from-<type1>
        :arg-type ,<type1>p
        :res-type booleanp
        :short ,(str::cat "Check if a value of " type1-string " is not 0.")
        :body (/= (,integer-from-<type1> x) 0))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,plus-<type1>
        :arg-type ,<type1>p
        :res-type ,<type>p
        :short ,(str::cat "Unary plus of a value of "
                          type1-string
                          " [C17:6.5.3].")
        :body ,(if samep
                   `(,<type1>-fix x)
                 `(,plus-<type> (,<type>-from-<type1> x))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          signedp
          `((defun-integer
             ,minus-<type1>-okp
             :arg-type ,<type1>p
             :res-type booleanp
             :short ,(str::cat "Check if the unary minus of a value of "
                               type1-string
                               " is well-defined.")
             :body ,(if samep
                        `(,<type1>-integerp (- (,integer-from-<type1> x)))
                      `(,minus-<type>-okp (,<type>-from-<type1> x))))))

       ;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,minus-<type1>
        :arg-type ,<type1>p
        ,@(and signedp `(:guard (,minus-<type1>-okp x)))
        :res-type ,<type>p
        :short ,(str::cat "Unary minus of a value of "
                          type1-string
                          " [C17:6.5.3].")
        :body ,(if samep
                   `(,(if signedp
                          <type1>-from-integer
                        <type1>-from-integer-mod)
                     (- (,integer-from-<type1> x)))
                 `(,minus-<type> (,<type>-from-<type1> x)))
        ,@(and
           signedp
           `(:guard-hints (("Goal" :in-theory (enable ,minus-<type1>-okp))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,bitnot-<type1>
        :arg-type ,<type1>p
        :res-type ,<type>p
        :short ,(str::cat "Bitwise complement of a value of "
                          type1-string
                          " [C17:6.5.3].")
        :body ,(if samep
                   `(,(if signedp
                          <type1>-from-integer
                        <type1>-from-integer-mod)
                     (lognot (,integer-from-<type1> x)))
                 `(,bitnot-<type> (,<type>-from-<type1> x)))
        ,@(and samep
               signedp
               `(:guard-hints
                 (("Goal" :in-theory (enable ,<type1>-integerp-alt-def
                                             ,integer-from-<type1>
                                             ,<type1>p
                                             (:e ,<type>-min)
                                             (:e ,<type>-max)
                                             lognot
                                             ifix))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,lognot-<type1>
        :arg-type ,<type1>p
        :res-type sintp
        :short ,(str::cat "Logical complement of a value of "
                          type1-string
                          " [C17:6.5.3].")
        :body (sint-from-boolean (= (,integer-from-<type1> x) 0)))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,shl-<type1>-okp
        :arg1-type ,<type1>p
        :arg2-type integerp
        :res-type booleanp
        :short ,(str::cat "Check if the left shift of a value of "
                          type1-string
                          " by an integer is well-defined.")
        :body ,(if samep
                   (if signedp
                       `(and (integer-range-p 0 (,<type1>-bits) (ifix y))
                             (>= (,integer-from-<type1> x) 0)
                             (,<type1>-integerp (* (,integer-from-<type1> x)
                                                   (expt 2 (ifix y)))))
                     `(integer-range-p 0 (,<type1>-bits) (ifix y)))
                 `(,shl-<type>-okp (,<type>-from-<type1> x) (ifix y))))

       ;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,shl-<type1>
        :arg1-type ,<type1>p
        :arg2-type integerp
        :guard (,shl-<type1>-okp x y)
        :res-type ,<type>p
        :short ,(str::cat "Left shift of a value of "
                          type1-string
                          " by an integer [C17:6.5.7].")
        :body ,(if samep
                   `(,(if signedp
                          <type1>-from-integer
                        <type1>-from-integer-mod)
                     (* (,integer-from-<type1> x)
                        (expt 2 (ifix y))))
                 `(,shl-<type> (,<type>-from-<type1> x) y))
        :guard-hints (("Goal" :in-theory (enable ,shl-<type1>-okp
                                                 integer-range-p)))
        ,@(and (not signedp)
               '(:prepwork
                 ((local (include-book "arithmetic-3/top" :dir :system))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,shr-<type1>-okp
        :arg1-type ,<type1>p
        :arg2-type integerp
        :res-type booleanp
        :short ,(str::cat "Check if the right shift of a value of "
                          type1-string
                          " by an integer is well-defined.")
        :body ,(if samep
                   (if signedp
                       `(and (integer-range-p 0 (,<type1>-bits) (ifix y))
                             (>= (,integer-from-<type1> x) 0))
                     `(integer-range-p 0 (,<type1>-bits) (ifix y)))
                 `(,shr-<type>-okp (,<type>-from-<type1> x) (ifix y))))

       ;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,shr-<type1>
        :arg1-type ,<type1>p
        :arg2-type integerp
        :guard (,shr-<type1>-okp x y)
        :res-type ,<type>p
        :short ,(str::cat "Right shift of a value of "
                          type1-string
                          " by an integer [C17:6.5.7].")
        :body ,(if samep
                   `(,(if signedp
                          <type1>-from-integer
                        <type1>-from-integer-mod)
                     (truncate (,integer-from-<type1> x) (expt 2 (ifix y))))
                 `(,shr-<type> (,<type>-from-<type1> x) y))
        :guard-hints (("Goal"
                       :in-theory (enable ,@(if (and samep
                                                     signedp)
                                                (list shr-<type1>-okp
                                                      <type1>-integerp
                                                      integer-from-<type1>
                                                      <type1>p
                                                      'signed-byte-p
                                                      'integer-range-p)
                                              (list shr-<type1>-okp)))))
        ,@(and
           signedp
           '(:prepwork
             ((local
               (include-book "kestrel/arithmetic-light/expt" :dir :system))
              (local
               (include-book "kestrel/arithmetic-light/truncate" :dir :system))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ))

  :guard-hints (("Goal" :in-theory (enable type-arithmeticp
                                           type-realp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-integer-operations-1-loop ((types type-listp))
  :guard (type-nonchar-integer-listp types)
  :returns (events pseudo-event-form-listp)
  :short "Events to generate the ACL2 models of the C integer operations
          that involve each one integer type from a list."
  (cond ((endp types) nil)
        (t (cons (def-integer-operations-1 (car types))
                 (def-integer-operations-1-loop (cdr types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()
  (local (in-theory (enable bit-width-value-choices)))
  (make-event
   ;; It is critical to generate the operations for SINT and UINT
   ;; before the ones for SCHAR and UCHAR and SSHORT and USHORT,
   ;; because the latter are defined in terms of the former.
   ;; See :DOC DEF-INTEGER-OPERATIONS-1.
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
     `(progn ,@(def-integer-operations-1-loop types)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-integer-operations-2 ((type1 typep) (type2 typep))
  :guard (and (type-nonchar-integerp type1)
              (type-nonchar-integerp type2))
  :guard-hints (("Goal" :in-theory (enable type-arithmeticp type-realp)))
  :returns (event pseudo-event-formp)
  :short "Event to generate the ACL2 models of
          the C integer operations that involve two integer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "These include all the strict pure binary operators.")
   (xdoc::p
    "For all the operations except shifts,
     we treat two cases differently:
     when the two usual arithmetic conversions applied to the operand types
     yields the same as the two operand types (which must therefore be equal),
     we generate a definition that performs a direct computation;
     otherwise, we generate a definition that
     converts the operands to the common type
     and then calls the function for that type as operand types.
     For shift operations,
     we turn the second operand into an ACL2 integer
     and then we call the shift function
     generated by @(tsee def-integer-operations-1);
     the result has the promoted type of the first operand."))

  (b* ((type1-string (integer-type-xdoc-string type1))
       (type2-string (integer-type-xdoc-string type2))
       (type (uaconvert-types type1 type2))
       (samep (and (equal type type1) (equal type type2)))
       (signedp (type-signed-integerp type))
       (ptype1 (promote-type type1))
       (<type1> (integer-type-to-fixtype type1))
       (<type2> (integer-type-to-fixtype type2))
       (<type> (integer-type-to-fixtype type))
       (<ptype1> (integer-type-to-fixtype ptype1))
       (<type1>p (pack <type1> 'p))
       (<type2>p (pack <type2> 'p))
       (<type>p (pack <type> 'p))
       (<ptype1>p (pack <ptype1> 'p))
       (integer-from-<type1> (pack 'integer-from- <type1>))
       (integer-from-<type2> (pack 'integer-from- <type2>))
       (<type>-from-integer (pack <type> '-from-integer))
       (<type>-from-integer-mod (pack <type>-from-integer '-mod))
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

       (set-ignore-ok t)
       (set-irrelevant-formals-ok t)

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          signedp
          `((defun-integer
             ,add-<type1>-<type2>-okp
             :arg1-type ,<type1>p
             :arg2-type ,<type2>p
             :res-type booleanp
             :short ,(str::cat "Check if the addition of a value of "
                               type1-string
                               " and a value of "
                               type2-string
                               " is well-defined.")
             :body
             ,(if samep
                  `(,<type>-integerp (+ (,integer-from-<type1> x)
                                        (,integer-from-<type2> y)))
                `(,add-<type>-<type>-okp
                  ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
                  ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y)))))))

       ;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,add-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        ,@(and signedp `(:guard (,add-<type1>-<type2>-okp x y)))
        :res-type ,<type>p
        :short ,(str::cat "Addition of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.6].")
        :body
        ,(if samep
             `(,(if signedp
                    <type>-from-integer
                  <type>-from-integer-mod)
               (+ (,integer-from-<type1> x)
                  (,integer-from-<type2> y)))
           `(,add-<type>-<type>
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
        ,@(and signedp
               `(:guard-hints
                 (("Goal" :in-theory (enable ,add-<type1>-<type2>-okp))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          signedp
          `((defun-integer
             ,sub-<type1>-<type2>-okp
             :arg1-type ,<type1>p
             :arg2-type ,<type2>p
             :res-type booleanp
             :short ,(str::cat "Check if the subtraction of a value of "
                               type1-string
                               " and a value of "
                               type2-string
                               " is well-defined.")
             :body
             ,(if samep
                  `(,<type>-integerp (- (,integer-from-<type1> x)
                                        (,integer-from-<type2> y)))
                `(,sub-<type>-<type>-okp
                  ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
                  ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y)))))))

       ;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,sub-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        ,@(and signedp `(:guard (,sub-<type1>-<type2>-okp x y)))
        :res-type ,<type>p
        :short ,(str::cat "Subtraction of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.6].")
        :body
        ,(if samep
             `(,(if signedp
                    <type>-from-integer
                  <type>-from-integer-mod)
               (- (,integer-from-<type1> x)
                  (,integer-from-<type2> y)))
           `(,sub-<type>-<type>
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
        ,@(and signedp
               `(:guard-hints
                 (("Goal" :in-theory (enable ,sub-<type1>-<type2>-okp))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          signedp
          `((defun-integer
             ,mul-<type1>-<type2>-okp
             :arg1-type ,<type1>p
             :arg2-type ,<type2>p
             :res-type booleanp
             :short ,(str::cat "Check if the multiplication of a value of "
                               type1-string
                               " and a value of "
                               type2-string
                               " is well-defined.")
             :body
             ,(if samep
                  `(,<type>-integerp (* (,integer-from-<type1> x)
                                        (,integer-from-<type2> y)))
                `(,mul-<type>-<type>-okp
                  ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
                  ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y)))))))

       ;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,mul-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        ,@(and signedp `(:guard (,mul-<type1>-<type2>-okp x y)))
        :res-type ,<type>p
        :short ,(str::cat "Multiplication of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.5].")
        :body
        ,(if samep
             `(,(if signedp
                    <type>-from-integer
                  <type>-from-integer-mod)
               (* (,integer-from-<type1> x)
                  (,integer-from-<type2> y)))
           `(,mul-<type>-<type>
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
        ,@(and signedp
               `(:guard-hints
                 (("Goal" :in-theory (enable ,mul-<type1>-<type2>-okp))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,div-<type1>-<type2>-okp
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :res-type booleanp
        :short ,(str::cat "Check if the division of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " is well-defined.")
        :body
        ,(if samep
             (if signedp
                 `(and (not (equal (,integer-from-<type2> y) 0))
                       (,<type>-integerp (truncate (,integer-from-<type1> x)
                                                   (,integer-from-<type2> y))))
               `(not (equal (,integer-from-<type2> y) 0)))
           `(,div-<type>-<type>-okp
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y)))))

       ;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,div-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :guard (,div-<type1>-<type2>-okp x y)
        :res-type ,<type>p
        :short ,(str::cat "Division of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.5].")
        :body
        ,(if samep
             `(,(if signedp
                    <type>-from-integer
                  <type>-from-integer-mod)
               (truncate (,integer-from-<type1> x)
                         (,integer-from-<type2> y)))
           `(,div-<type>-<type>
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
        :guard-hints (("Goal" :in-theory (enable ,div-<type1>-<type2>-okp))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,rem-<type1>-<type2>-okp
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :res-type booleanp
        :short ,(str::cat "Check if the remainder of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " is well-defined.")
        :body
        ,(if samep
             (if signedp
                 `(and (not (equal (,integer-from-<type2> y) 0))
                       (,<type>-integerp (rem (,integer-from-<type1> x)
                                              (,integer-from-<type2> y))))
               `(not (equal (,integer-from-<type2> y) 0)))
           `(,rem-<type>-<type>-okp
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y)))))

       ;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,rem-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :guard (,rem-<type1>-<type2>-okp x y)
        :res-type ,<type>p
        :short ,(str::cat "Remainder of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.5].")
        :body
        ,(if samep
             `(,(if signedp
                    <type>-from-integer
                  <type>-from-integer-mod)
               (rem (,integer-from-<type1> x)
                    (,integer-from-<type2> y)))
           `(,rem-<type>-<type>
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
        :guard-hints (("Goal" :in-theory (enable ,rem-<type1>-<type2>-okp
                                                 ,@(and (not signedp)
                                                        (list 'rem))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,shl-<type1>-<type2>-okp
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :res-type booleanp
        :short ,(str::cat "Check if the left shift of a value of "
                          type1-string
                          " by a value of "
                          type2-string
                          " is well-defined.")
        :body (,shl-<type1>-okp x (,integer-from-<type2> y)))

       ;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,shl-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :guard (,shl-<type1>-<type2>-okp x y)
        :res-type ,<ptype1>p
        :short ,(str::cat "Left shift of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.7].")
        :body (,shl-<type1> x (,integer-from-<type2> y))
        :guard-hints (("Goal" :in-theory (enable ,shl-<type1>-<type2>-okp))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,shr-<type1>-<type2>-okp
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :res-type booleanp
        :short ,(str::cat "Check if the right shift of a value of "
                          type1-string
                          " by a value of "
                          type2-string
                          " is well-defined.")
        :body (,shr-<type1>-okp x (,integer-from-<type2> y)))

       ;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,shr-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :guard (,shr-<type1>-<type2>-okp x y)
        :res-type ,<ptype1>p
        :short ,(str::cat "Right shift of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.7].")
        :body (,shr-<type1> x (,integer-from-<type2> y))
        :guard-hints (("Goal" :in-theory (enable ,shr-<type1>-<type2>-okp))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,lt-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :res-type sintp
        :short ,(str::cat "Less-than relation of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.8].")
        :body
        ,(if samep
             `(if (< (,integer-from-<type1> x)
                     (,integer-from-<type2> y))
                  (sint-from-integer 1)
                (sint-from-integer 0))
           `(,lt-<type>-<type>
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y)))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,gt-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :res-type sintp
        :short ,(str::cat "Greater-than relation of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.8].")
        :body
        ,(if samep
             `(if (> (,integer-from-<type1> x)
                     (,integer-from-<type2> y))
                  (sint-from-integer 1)
                (sint-from-integer 0))
           `(,gt-<type>-<type>
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y)))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,le-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :res-type sintp
        :short ,(str::cat "Less-than-or-equal-to relation of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.8].")
        :body
        ,(if samep
             `(if (<= (,integer-from-<type1> x)
                      (,integer-from-<type2> y))
                  (sint-from-integer 1)
                (sint-from-integer 0))
           `(,le-<type>-<type>
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y)))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,ge-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :res-type sintp
        :short ,(str::cat "Greater-than-or-equal-to relation of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.8].")
        :body
        ,(if samep
             `(if (>= (,integer-from-<type1> x)
                      (,integer-from-<type2> y))
                  (sint-from-integer 1)
                (sint-from-integer 0))
           `(,ge-<type>-<type>
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y)))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,eq-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :res-type sintp
        :short ,(str::cat "Equality of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.9].")
        :body
        ,(if samep
             `(if (= (,integer-from-<type1> x)
                     (,integer-from-<type2> y))
                  (sint-from-integer 1)
                (sint-from-integer 0))
           `(,eq-<type>-<type>
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y)))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,ne-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :res-type sintp
        :short ,(str::cat "Non-equality of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.9].")
        :body
        ,(if samep
             `(if (/= (,integer-from-<type1> x)
                      (,integer-from-<type2> y))
                  (sint-from-integer 1)
                (sint-from-integer 0))
           `(,ne-<type>-<type>
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y)))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,bitand-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :res-type ,<type>p
        :short ,(str::cat "Bitwise conjunction of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.10].")
        :body
        ,(if samep
             `(,<type>-from-integer
               (logand (,integer-from-<type1> x)
                       (,integer-from-<type2> y)))
           `(,bitand-<type>-<type>
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
        ,@(and
           samep
           `(:prepwork
             ((local (include-book "ihs/logops-lemmas" :dir :system)))
             :guard-hints
             (("Goal"
               :in-theory (enable ,<type>-integerp
                                  ,<type>p
                                  ,integer-from-<type1>))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,bitxor-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :res-type ,<type>p
        :short ,(str::cat "Bitwise exclusive disjunction of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.11].")
        :body
        ,(if samep
             `(,<type>-from-integer
               (logxor (,integer-from-<type1> x)
                       (,integer-from-<type2> y)))
           `(,bitxor-<type>-<type>
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
        ,@(and
           samep
           `(:prepwork
             ((local (include-book "centaur/bitops/ihs-extensions" :dir :system)))
             :guard-hints
             (("Goal"
               :in-theory (enable ,<type>-integerp
                                  ,<type>p
                                  ,integer-from-<type1>))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defun-integer
        ,bitior-<type1>-<type2>
        :arg1-type ,<type1>p
        :arg2-type ,<type2>p
        :res-type ,<type>p
        :short ,(str::cat "Bitwise inclusive disjunction of a value of "
                          type1-string
                          " and a value of "
                          type2-string
                          " [C17:6.5.12].")
        :body
        ,(if samep
             `(,<type>-from-integer
               (logior (,integer-from-<type1> x)
                       (,integer-from-<type2> y)))
           `(,bitior-<type>-<type>
             ,(if (eq <type> <type1>) 'x `(,<type>-from-<type1> x))
             ,(if (eq <type> <type2>) 'y `(,<type>-from-<type2> y))))
        ,@(and
           samep
           `(:prepwork
             ((local (include-book "centaur/bitops/ihs-extensions" :dir :system)))
             :guard-hints
             (("Goal"
               :in-theory (enable ,<type>-integerp
                                  ,<type>p
                                  ,integer-from-<type1>))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-integer-operations-2-loop-same ((types type-listp))
  :guard (type-nonchar-integer-listp types)
  :returns (events pseudo-event-form-listp)
  :short "Events to generate the ACL2 models of
          the C integer operations that involve
          two identical integer types from a list."
  (cond ((endp types) nil)
        (t (cons (def-integer-operations-2 (car types) (car types))
                 (def-integer-operations-2-loop-same (cdr types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-integer-operations-2-loop-inner ((type typep)
                                                 (types type-listp))
  :guard (and (type-nonchar-integerp type)
              (type-nonchar-integer-listp types))
  :returns (events pseudo-event-form-listp)
  :short "Events to generate the ACL2 models of
          the C integer operations that involve
          an integer type as first operand
          and each of a list of integer types as second operand."
  :long
  (xdoc::topstring
   (xdoc::p
    "We skip the event if the two types are equal,
     because that case is already covered by
     @(tsee def-integer-operations-2-loop-same).")
   (xdoc::p
    "This is the inner loop for generating operations
     for all combinations of different operand types."))
  (cond ((endp types) nil)
        ((equal type (car types)) (def-integer-operations-2-loop-inner
                                   type (cdr types)))
        (t (cons (def-integer-operations-2 type (car types))
                 (def-integer-operations-2-loop-inner type (cdr types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-integer-operations-2-loop-outer ((types type-listp)
                                                 (types1 type-listp))
  :guard (and (type-nonchar-integer-listp types)
              (type-nonchar-integer-listp types1))
  :returns (events pseudo-event-form-listp)
  :short "Events to generate the ACL2 models of
          the C integer operations that involve
          each of a list of integer types as first operand
          and each of a list of integer types as second operand."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the outer loop for generating operations
     for all combinations of different operand types."))
  (cond ((endp types) nil)
        (t (append
            (def-integer-operations-2-loop-inner (car types) types1)
            (def-integer-operations-2-loop-outer (cdr types) types1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()
  (local (in-theory (enable bit-width-value-choices)))
  (make-event
   ;; It is critical to generate the operations for equal operand types
   ;; before the ones for different operand types,
   ;; because the latter are defined in terms of the former.
   ;; See :DOC DEF-INTEGER-OPERATIONS-2.
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
     `(progn ,@(def-integer-operations-2-loop-same types)
             ,@(def-integer-operations-2-loop-outer types types)))))
