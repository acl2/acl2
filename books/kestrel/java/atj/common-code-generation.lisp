; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

; Avoid failure for atj-gen-number in ACL2(r):
; cert_param: non-acl2r

(include-book "java-abstract-syntax")
(include-book "aij-notions")
(include-book "name-translation")
(include-book "test-structures")

(include-book "kestrel/utilities/strings/char-kinds" :dir :system)
(include-book "kestrel/utilities/strings/hexchars" :dir :system)
(include-book "std/strings/decimal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-common-code-generation
  :parents (atj-code-generation)
  :short "Code generation that is common to
          the deep and shallow embedding approaches."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-char-to-jhexcode ((char characterp))
  :returns (expr jexprp)
  :short "Turn an ACL2 character into
          a Java hexadecimal literal expression
          corresponding to the character code."
  (b* ((code (char-code char))
       ((mv hi-char lo-char) (ubyte8=>hexchars code))
       (hi-code (char-code hi-char))
       (lo-code (char-code lo-char)))
    (jexpr-literal
     (jliteral-integer
      (integer-literal-hex
       (make-hex-integer-literal
        :digits/uscores (list (hexdig/uscore-digit hi-code)
                              (hexdig/uscore-digit lo-code))
        :prefix-upcase-p nil
        :suffix? (optional-integer-type-suffix-none))))))
  :guard-hints (("Goal" :in-theory (enable ubyte8=>hexchars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection atj-chars-to-jhexcodes (x)
  :guard (character-listp x)
  :returns (exprs jexpr-listp)
  :short "Lift @(tsee atj-char-to-jhexcode) to lists."
  (atj-char-to-jhexcode x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jstring ((string stringp))
  :returns (expr jexprp)
  :short "Generate Java code to build a Java string from an ACL2 string."
  :long
  (xdoc::topstring
   (xdoc::p
    "Often, an ACL2 string can be turned into a Java string literal
     that is valid when pretty-printed.
     Examples are @('\"abc\"') or @('\"x-y @ 5.A\"').")
   (xdoc::p
    "However, if the ACL2 string includes characters like @('#\Return'),
     attempting to turn that into a Java string literal
     may result in an invalid one when pretty-printed.
     In this case, a safe way to build the Java string is
     via a Java character array with an initializer
     consisting of the codes of the ACL2 string.")
   (xdoc::p
    "If the ACL2 string consists of only pritable ASCII characters
     (i.e. space and visible ASCII characters),
     we turn it into a Java string literal.
     Otherwise, we turn it into a Java array creation expression
     that is passed as argument to a Java class instance creation expression
     for a @('String') object."))
  (b* ((chars (explode string)))
    (if (printable-charlist-p chars)
        (jexpr-literal-string string)
      (jexpr-newclass (jtype-class "String")
                      (list
                       (jexpr-newarray-init (jtype-char)
                                            (atj-chars-to-jhexcodes
                                             chars)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jboolean ((boolean booleanp))
  :returns (expr jexprp)
  :short "Generate Java code to build a Java @('boolean')
          from an ACL2 boolean."
  (if boolean
      (jexpr-literal-true)
    (jexpr-literal-false)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jchar ((char ubyte16p))
  :returns (expr jexprp)
  :short "Generate Java code to build a Java @('char')
          from an unsigned 16-bit ACL2 integer."
  :long
  (xdoc::topstring-p
   "We generate a character literal if the character is below 256,
    since currently our Java abstract syntax
    only supports 8-bit character literals.
    Otherwise, we cast the value to @('char').")
  (if (< char 256)
      (jexpr-literal-character (code-char char))
    (jexpr-cast (jtype-char) (jexpr-lit-int-dec-nouscores char))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jint ((integer sbyte32p))
  :returns (expr jexprp)
  :short "Generate Java code to build a Java @('int')
          from a signed 32-bit ACL2 integer."
  (if (< integer 0)
      (jexpr-unary (junop-uminus)
                   (jexpr-lit-int-dec-nouscores (- integer)))
    (jexpr-lit-int-dec-nouscores integer)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jbyte ((byte sbyte8p))
  :returns (expr jexprp)
  :short "Generate Java code to build a Java @('byte')
          from a signed 8-bit ACL2 integer."
  (jexpr-cast (jtype-byte) (atj-gen-jint byte))
  :guard-hints (("Goal" :in-theory (enable sbyte8p sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jshort ((short sbyte16p))
  :returns (expr jexprp)
  :short "Generate Java code to build a Java @('short')
          from a signed 16-bit signed ACL2 integer."
  (jexpr-cast (jtype-short) (atj-gen-jint short))
  :guard-hints (("Goal" :in-theory (enable sbyte16p sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jlong ((integer sbyte64p))
  :returns (expr jexprp)
  :short "Generate Java code to build a Java @('long')
          from a signed 64-bit ACL2 integer."
  (if (< integer 0)
      (jexpr-unary (junop-uminus)
                   (jexpr-lit-long-dec-nouscores (- integer)))
    (jexpr-lit-long-dec-nouscores integer)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jbigint ((integer integerp))
  :returns (expr jexprp)
  :short "Generate Java code to build a Java @('BigInteger')
          from an ACL2 integer."
  (b* ((string (if (< integer 0)
                   (str::cat "-" (str::nat-to-dec-string (- integer)))
                 (str::nat-to-dec-string integer))))
    (jexpr-newclass (jtype-class "BigInteger")
                    (list
                     (jexpr-literal-string string)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jboolean-array ((boolean-array boolean-arrayp))
  :returns (expr jexprp)
  :short "Generate Java code to build a Java @('boolean') array."
  (jexpr-newarray-init (jtype-boolean)
                       (atj-gen-jboolean-array-aux
                        (boolean-array->components boolean-array)))
  :prepwork
  ((define atj-gen-jboolean-array-aux ((booleans boolean-value-listp))
     :returns (exprs jexpr-listp)
     :parents nil
     (cond ((endp booleans) nil)
           (t (cons (atj-gen-jboolean (boolean-value->bool (car booleans)))
                    (atj-gen-jboolean-array-aux (cdr booleans))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jchar-array ((char-array char-arrayp))
  :returns (expr jexprp)
  :short "Generate Java code to build a Java @('char') array."
  (jexpr-newarray-init (jtype-char)
                       (atj-gen-jchar-array-aux
                        (char-array->components char-array)))
  :prepwork
  ((define atj-gen-jchar-array-aux ((chars char-value-listp))
     :returns (exprs jexpr-listp)
     :parents nil
     (cond ((endp chars) nil)
           (t (cons (atj-gen-jchar (char-value->nat (car chars)))
                    (atj-gen-jchar-array-aux (cdr chars))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jbyte-array ((byte-array byte-arrayp))
  :returns (expr jexprp)
  :short "Generate Java code to build a Java @('byte') array."
  (jexpr-newarray-init (jtype-byte)
                       (atj-gen-jbyte-array-aux
                        (byte-array->components byte-array)))
  :prepwork
  ((define atj-gen-jbyte-array-aux ((bytes byte-value-listp))
     :returns (exprs jexpr-listp)
     :parents nil
     (cond ((endp bytes) nil)
           (t (cons (atj-gen-jbyte (byte-value->int (car bytes)))
                    (atj-gen-jbyte-array-aux (cdr bytes))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jshort-array ((short-array short-arrayp))
  :returns (expr jexprp)
  :short "Generate Java code to build a Java @('short') array."
  (jexpr-newarray-init (jtype-short)
                       (atj-gen-jshort-array-aux
                        (short-array->components short-array)))
  :prepwork
  ((define atj-gen-jshort-array-aux ((shorts short-value-listp))
     :returns (exprs jexpr-listp)
     :parents nil
     (cond ((endp shorts) nil)
           (t (cons (atj-gen-jshort (short-value->int (car shorts)))
                    (atj-gen-jshort-array-aux (cdr shorts))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jint-array ((int-array int-arrayp))
  :returns (expr jexprp)
  :short "Generate Java code to build a Java @('int') array."
  (jexpr-newarray-init (jtype-int)
                       (atj-gen-jint-array-aux
                        (int-array->components int-array)))
  :prepwork
  ((define atj-gen-jint-array-aux ((ints int-value-listp))
     :returns (exprs jexpr-listp)
     :parents nil
     (cond ((endp ints) nil)
           (t (cons (atj-gen-jint (int-value->int (car ints)))
                    (atj-gen-jint-array-aux (cdr ints))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jlong-array ((long-array long-arrayp))
  :returns (expr jexprp)
  :short "Generate Java code to build a Java @('long') array."
  (jexpr-newarray-init (jtype-long)
                       (atj-gen-jlong-array-aux
                        (long-array->components long-array)))
  :prepwork
  ((define atj-gen-jlong-array-aux ((longs long-value-listp))
     :returns (exprs jexpr-listp)
     :parents nil
     (cond ((endp longs) nil)
           (t (cons (atj-gen-jlong (long-value->int (car longs)))
                    (atj-gen-jlong-array-aux (cdr longs))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-paramlist ((names string-listp) (types jtype-listp))
  :guard (= (len names) (len types))
  :returns (params jparam-listp)
  :short "Generate a Java formal parameter list
          from the specified names and Java types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a list of Java parameter names and a list of Java types,
     this function generates a Java formal parameter list
     that associates each type to each name, in order."))
  (cond ((endp names) nil)
        (t (cons (make-jparam :final? nil
                              :type (car types)
                              :name (car names))
                 (atj-gen-paramlist (cdr names) (cdr types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jlocvar-indexed
  ((var-type jtypep "Type of the local variable.")
   (var-base stringp "Base name of the local variable.")
   (var-index natp "Index of the local variable.")
   (var-init? maybe-jexprp "Initializer of the local variable."))
  :returns (mv (locvar-block jblockp)
               (var-name stringp "The name of the local variable.")
               (new-var-index natp "The updated variable index."
                              :hyp (natp var-index)))
  :short "Generate a Java declaration for an indexed local variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name of the local variable to use is obtained by
     adding the next variable index after the base name.
     The index is incremented and returned because it has been used,
     and the next variable with the same name must use the next index.")
   (xdoc::p
    "For convenience of the callers of this function,
     the local variable declaration is returned in a singleton block."))
  (b* ((var-name (str::cat var-base (nat-to-dec-string var-index)))
       (var-index (1+ var-index))
       (locvar-block (jblock-locvar var-type var-name var-init?)))
    (mv locvar-block var-name var-index))
  ///

  (defrule posp-of-atj-gen-jlocvar-indexed-new-var-index
    (implies (posp var-index)
             (posp (mv-nth 2 (atj-gen-jlocvar-indexed
                              var-type var-base var-index var-init))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-char ((char characterp) (deep$ symbolp) (guards$ symbolp))
  :returns (expr jexprp)
  :short "Generate Java code to build an ACL2 character."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding with guards,
     we translate ACL2 characters to Java character literals.
     This is because, in the shallow embedding with guards,
     ACL2 characters are represented as Java characters.")
   (xdoc::p
    "In the deep embedding, or in the shallow embedding without guards,
     we generate an expression of type @('Acl2Character'),
     by calling the factory method on the Java character literal."))
  (if (and (not deep$)
           guards$)
      (jexpr-literal-character char)
    (jexpr-smethod *aij-type-char*
                   "make"
                   (list (jexpr-literal-character char)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-string ((string stringp) (deep$ symbolp) (guards$ symbolp))
  :returns (expr jexprp)
  :short "Generate Java code to build an ACL2 string."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding with guards,
     we translate ACL2 Strings to Java string expression.
     This is because, in the shallow embedding with guards,
     ACL2 strings are represented as Java strings.")
   (xdoc::p
    "In the deep embedding, or in the shallow embedding without guards,
     we generate an expression of type @('Acl2String'),
     by calling the factory method on the Java string expression."))
  (if (and (not deep$)
           guards$)
      (atj-gen-jstring string)
    (jexpr-smethod *aij-type-string*
                   "make"
                   (list (atj-gen-jstring string)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-symbol ((symbol symbolp) (deep$ symbolp) (guards$ symbolp))
  :returns (expr jexprp)
  :short "Generate Java code to build an ACL2 symbol."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding with guards,
     for the symbols @('t') and @('nil')
     we generate the Java literals @('true') and @('false').
     This is because, in the shallow embedding with guards,
     ACL2 booleans are represented as Java booleans.")
   (xdoc::p
    "In all other cases,
     we generate an expression of type @('Acl2Symbol').
     Since AIJ has a number of constants (i.e. static final fields)
     for certain common symbols,
     we just reference the appropriate constant
     if the symbol in question is among those symbols.
     Otherwise, we build it in the general way."))
  (if (and (booleanp symbol)
           (not deep$)
           guards$)
      (if symbol (jexpr-literal-true) (jexpr-literal-false))
    (b* ((pair (assoc-eq symbol *aij-symbol-constants*)))
      (if pair
          (jexpr-name (str::cat "Acl2Symbol." (cdr pair)))
        (jexpr-smethod *aij-type-symbol*
                       "make"
                       (list (atj-gen-jstring
                              (symbol-package-name symbol))
                             (atj-gen-jstring
                              (symbol-name symbol))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-symbols ((symbols symbol-listp)
                         (deep$ symbolp)
                         (guards$ symbolp))
  :returns (exprs jexpr-listp)
  :short "Lift @(tsee atj-gen-symbol) to lists."
  (cond ((endp symbols) nil)
        (t (cons (atj-gen-symbol (car symbols) deep$ guards$)
                 (atj-gen-symbols (cdr symbols) deep$ guards$)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-integer ((integer integerp))
  :returns (expr jexprp)
  :short "Generate Java code to build an ACL2 integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the ACL2 integer is representable as a Java integer,
     we generate a Java integer literal.
     Otherwise, if it is representable as a Java long integer,
     we generate a Java long integer literal.
     Otherwise, we generate a Java big integer
     built out of the string representation of the ACL2 integer.")
   (xdoc::p
    "These are passed to the @('Acl2Integer.make').
     However, if the integer is 0 or 1,
     we simply generate a reference to the respective Java static final fields
     in the @('Acl2Integer') class."))
  (b* ((arg (cond ((sbyte32p integer)
                   (atj-gen-jint integer))
                  ((sbyte64p integer)
                   (atj-gen-jlong integer))
                  (t (atj-gen-jbigint integer)))))
    (jexpr-smethod *aij-type-int*
                   "make"
                   (list arg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-rational ((rational rationalp))
  :returns (expr jexprp)
  :short "Generate Java code to build an ACL2 rational."
  (b* ((numerator (numerator rational))
       (denominator (denominator rational))
       ((mv numerator-arg denominator-arg)
        (cond ((and (sbyte32p numerator)
                    (sbyte32p denominator))
               (mv (atj-gen-jint numerator)
                   (atj-gen-jint denominator)))
              ((and (sbyte64p numerator)
                    (sbyte64p denominator))
               (mv (atj-gen-jlong numerator)
                   (atj-gen-jlong denominator)))
              (t (mv (atj-gen-jbigint numerator)
                     (atj-gen-jbigint denominator))))))
    (jexpr-smethod *aij-type-rational*
                   "make"
                   (list numerator-arg
                         denominator-arg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-number ((number acl2-numberp))
  :returns (expr jexprp)
  :short "Generate Java code to build an ACL2 number."
  (b* ((realpart (realpart number))
       (imagpart (imagpart number))
       ((mv realpart-arg imagpart-arg)
        (cond ((and (sbyte32p realpart)
                    (sbyte32p imagpart))
               (mv (atj-gen-jint realpart)
                   (atj-gen-jint imagpart)))
              ((and (sbyte64p realpart)
                    (sbyte64p imagpart))
               (mv (atj-gen-jlong realpart)
                   (atj-gen-jlong imagpart)))
              ((and (integerp realpart)
                    (integerp imagpart))
               (mv (atj-gen-jbigint realpart)
                   (atj-gen-jbigint imagpart)))
              (t (mv (atj-gen-rational realpart)
                     (atj-gen-rational imagpart))))))
    (jexpr-smethod *aij-type-number*
                   "make"
                   (list realpart-arg
                         imagpart-arg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-gen-value
  :short "Generate Java code to build an ACL2 value."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a @(tsee cons) pair that is also a true list,
     the generated code builds all the elements
     and then calls @('Acl2Value.makeList()') (a variable arity method)
     with the elements;
     the result is cast to @('Acl2ConsPair').
     For a @(tsee cons) pair that is not a true list,
     the generated code
     builds the @(tsee car),
     sets a local variable to it,
     builds the @(tsee cdr),
     sets another local variable to it,
     and then calls @('Acl2ConsValue.make()') with the two local variables.")
   (xdoc::p
    "The @('deep$') and @('guards$') arguments are passed
     from @(tsee atj-gen-value) to
     @(tsee atj-gen-symbol), @(tsee atj-gen-char), and @(tsee atj-gen-string)
     only at the top level;
     this is so that we generate Java boolean, character, and string expressions
     for ACL2 boolean, character, and string values,
     in the shallow embedding with guards.
     But at the non-top levels, these flags are set to @('t') and @('nil'),
     because ACL2 booleans, characters, and strings
     are represented as @('Acl2Symbol'), @('Acl2Character'), and @('Acl2String')
     instances inside other values (@(tsee cons)es).")
   (xdoc::@def "atj-gen-value")
   (xdoc::@def "atj-gen-values")
   (xdoc::@def "atj-gen-list")
   (xdoc::@def "atj-gen-cons"))

  (define atj-gen-value (value
                         (jvar-value-base stringp)
                         (jvar-value-index posp)
                         (deep$ booleanp)
                         (guards$ booleanp))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index)))
    :parents nil
    (cond ((characterp value) (mv nil
                                  (atj-gen-char value deep$ guards$)
                                  jvar-value-index))
          ((stringp value) (mv nil
                               (atj-gen-string value deep$ guards$)
                               jvar-value-index))
          ((symbolp value) (mv nil
                               (atj-gen-symbol value deep$ guards$)
                               jvar-value-index))
          ((integerp value) (mv nil
                                (atj-gen-integer value)
                                jvar-value-index))
          ((rationalp value) (mv nil
                                 (atj-gen-rational value)
                                 jvar-value-index))
          ((acl2-numberp value) (mv nil
                                    (atj-gen-number value)
                                    jvar-value-index))
          ((true-listp value) (atj-gen-list value
                                            jvar-value-base
                                            jvar-value-index))
          ((consp value) (atj-gen-cons value
                                       jvar-value-base
                                       jvar-value-index))
          (t (prog2$ (raise "Internal error: the value ~x0 is a bad atom."
                            value)
                     (mv nil
                         (jexpr-name "this-is-irrelevant")
                         jvar-value-index))))
    ;; 2nd component is larger than 1 and 0
    ;; so that the calls of ATJ-GEN-LIST and ATJ-GEN-CONS decrease:
    :measure (two-nats-measure (acl2-count value) 2))

  (define atj-gen-values ((values true-listp)
                          (jvar-value-base stringp)
                          (jvar-value-index posp))
    :returns (mv (block jblockp)
                 (exprs (and (jexpr-listp exprs)
                             (equal (len exprs) (len values))))
                 (new-jvar-value-index posp :hyp (posp jvar-value-index)))
    (cond ((endp values) (mv nil nil jvar-value-index))
          (t (b* (((mv first-block
                       first-expr
                       jvar-value-index)
                   (atj-gen-value (car values)
                                  jvar-value-base
                                  jvar-value-index
                                  t
                                  nil))
                  ((mv rest-block
                       rest-jexrps
                       jvar-value-index)
                   (atj-gen-values (cdr values)
                                   jvar-value-base
                                   jvar-value-index)))
               (mv (append first-block rest-block)
                   (cons first-expr rest-jexrps)
                   jvar-value-index))))
    :measure (two-nats-measure (acl2-count values) 0))

  (define atj-gen-list ((list true-listp)
                        (jvar-value-base stringp)
                        (jvar-value-index posp))
    :guard (consp list)
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index)))
    (b* (((mv block exprs jvar-value-index) (atj-gen-values list
                                                            jvar-value-base
                                                            jvar-value-index))
         (expr (jexpr-smethod *aij-type-value* "makeList" exprs)))
      (mv block
          (jexpr-cast *aij-type-cons* expr)
          jvar-value-index))
    ;; 2nd component is non-0 so that the call of ATJ-GEN-VALUES decreases:
    :measure (two-nats-measure (acl2-count list) 1))

  (define atj-gen-cons ((conspair consp)
                        (jvar-value-base stringp)
                        (jvar-value-index posp))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index)))
    :parents nil
    (b* (((unless (mbt (consp conspair)))
          (mv nil (jexpr-name "this-is-irrelevant") jvar-value-index))
         ((mv car-block
              car-expr
              jvar-value-index)
          (atj-gen-value (car conspair)
                         jvar-value-base
                         jvar-value-index
                         t
                         nil))
         ((mv car-locvar-block
              car-jvar
              jvar-value-index)
          (atj-gen-jlocvar-indexed *aij-type-value*
                                   jvar-value-base
                                   jvar-value-index
                                   car-expr))
         ((mv cdr-block
              cdr-expr
              jvar-value-index)
          (atj-gen-value (cdr conspair)
                         jvar-value-base
                         jvar-value-index
                         t
                         nil))
         ((mv cdr-locvar-block
              cdr-jvar
              jvar-value-index)
          (atj-gen-jlocvar-indexed *aij-type-value*
                                   jvar-value-base
                                   jvar-value-index
                                   cdr-expr))
         (block (append car-block
                        car-locvar-block
                        cdr-block
                        cdr-locvar-block))
         (expr (jexpr-smethod *aij-type-cons*
                              "make"
                              (list (jexpr-name car-jvar)
                                    (jexpr-name cdr-jvar)))))
      (mv block expr jvar-value-index))
    :measure (two-nats-measure (acl2-count conspair) 0))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-gen-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-gen-value-flat
  :short "Generate flat Java code to build an ACL2 value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee atj-gen-value),
     except that we do not generate local variables
     for the @(tsee car) and @(tsee cdr) sub-expressions of a @(tsee cons).
     We generate a single expression, without blocks;
     in this sense it is ``flat''.")
   (xdoc::p
    "We set the @('deep$') and @('guards$') flags to @('t') and @('nil')
     when we call
     @(tsee atj-gen-symbol), @(tsee atj-gen-char), and @(tsee atj-gen-string),
     so that we generate @('Acl2Symbol')s for the ACL2 booleans,
     @('Acl2Character')s for the ACL2 characters,
     and @('Acl2String')s for the ACL2 strings.
     This is because @(tsee atj-gen-value-flat) is only called
     on @(tsee cons)es at the top level;
     see the documentation of @(tsee atj-gen-value).")
   (xdoc::@def "atj-gen-value-flat")
   (xdoc::@def "atj-gen-values-flat")
   (xdoc::@def "atj-gen-list-flat")
   (xdoc::@def "atj-gen-cons-flat"))

  (define atj-gen-value-flat (value)
    :returns (expr jexprp)
    :parents nil
    (cond ((characterp value) (atj-gen-char value t nil))
          ((stringp value) (atj-gen-string value t nil))
          ((symbolp value) (atj-gen-symbol value t nil))
          ((integerp value) (atj-gen-integer value))
          ((rationalp value) (atj-gen-rational value))
          ((acl2-numberp value) (atj-gen-number value))
          ((true-listp value) (atj-gen-list-flat value))
          ((consp value) (atj-gen-cons-flat value))
          (t (prog2$ (raise "Internal error: the value ~x0 is a bad atom."
                            value)
                     (jexpr-name "this-is-irrelevant"))))
    ;; 2nd component is larger than 1 and 0
    ;; so that the calls of ATJ-GEN-LIST-FLAT and ATJ-GEN-CONS-FLAT decrease:
    :measure (two-nats-measure (acl2-count value) 2))

  (define atj-gen-values-flat ((values true-listp))
    :returns (exprs (and (jexpr-listp exprs)
                         (equal (len exprs) (len values))))
    (cond ((endp values) nil)
          (t (cons (atj-gen-value-flat (car values))
                   (atj-gen-values-flat (cdr values)))))
    :measure (two-nats-measure (acl2-count values) 0))

  (define atj-gen-list-flat ((list true-listp))
    :returns (expr jexprp)
    (jexpr-cast *aij-type-cons*
                (jexpr-smethod *aij-type-value*
                               "makeList"
                               (atj-gen-values-flat list)))
    ;; 2nd component is non-0 so that the call of ATJ-GEN-VALUES-FLAT decreases:
    :measure (two-nats-measure (acl2-count list) 1))

  (define atj-gen-cons-flat ((conspair consp))
    :returns (expr jexprp)
    :parents nil
    (b* (((unless (mbt (consp conspair))) (jexpr-name "this-is-irrelevant"))
         (car-expr (atj-gen-value-flat (car conspair)))
         (cdr-expr (atj-gen-value-flat (cdr conspair))))
      (jexpr-smethod *aij-type-cons*
                     "make"
                     (list car-expr
                           cdr-expr)))
    :measure (two-nats-measure (acl2-count conspair) 0))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-gen-value-flat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-pkg-method-name ((pkg stringp))
  :returns (method-name stringp)
  :short "Name of the Java method that adds an ACL2 package definition."
  :long
  (xdoc::topstring-p
   "We generate a private static method
    for each ACL2 package definition to build.
    This function generates the name of this method,
    which is distinct from all the other methods
    generated for the same class.")
  (str::cat "addPackageDef_"
            (implode (atj-chars-to-jchars-id (explode pkg) nil :dash nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-pkg-name ((pkg stringp))
  :returns (expr jexprp)
  :short "Generate Java code to build an ACL2 package name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since AIJ has a number of constants (i.e. static final fields)
     for a number of common ACL2 package names,
     we just reference the appropriate constant
     if the package name in question is among those.
     Otherwise, we build it in the general way;
     note that ACL2 package names can always be safely generated
     as Java string literals.
     Using the constants when possible makes the generated Java code faster.
     We introduce and use an alist to specify
     the correspondence between ACL2 package symbols
     and AIJ static final fields."))
  (b* ((pair (assoc-equal pkg *atj-gen-pkg-name-alist*)))
    (if pair
        (jexpr-name (cdr pair))
      (jexpr-smethod *aij-type-pkg-name*
                     "make"
                     (list (atj-gen-jstring pkg)))))

  :prepwork
  ((defval *atj-gen-pkg-name-alist*
     '(("KEYWORD"             . "Acl2PackageName.KEYWORD")
       ("COMMON-LISP"         . "Acl2PackageName.LISP")
       ("ACL2"                . "Acl2PackageName.ACL2")
       ("ACL2-OUTPUT-CHANNEL" . "Acl2PackageName.ACL2_OUTPUT")
       ("ACL2-INPUT-CHANNEL"  . "Acl2PackageName.ACL2_INPUT")
       ("ACL2-PC"             . "Acl2PackageName.ACL2_PC")
       ("ACL2-USER"           . "Acl2PackageName.ACL2_USER")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-pkg-method ((pkg stringp) (verbose$ booleanp))
  :returns (method jmethodp)
  :short "Generate a Java method that adds an ACL2 package definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a private static method
     that contains a sequence of statements
     to incrementally construct
     the Java list of symbols imported by the package.
     The sequence starts with a declaration of a local variable
     initialized with an empty Java list
     whose capacity is the length of the import list.
     After all the assignments, we generate a method call
     to add the ACL2 package definition with the calculated import list.")
   (xdoc::p
    "We set the @('deep$') and @('guards$') flag to @('t') and @('nil')
     when we call @(tsee atj-gen-symbol),
     so that we generate @('Acl2Symbol')s for ACL2 booleans."))
  (b* (((run-when verbose$)
        (cw "  ~s0~%" pkg))
       (jvar-imports "imports")
       (method-name (atj-gen-pkg-method-name pkg))
       (imports (pkg-imports pkg))
       (len-expr (jexpr-lit-int-dec-nouscores (len imports)))
       (newlist-expr (jexpr-newclass (jtype-class "ArrayList<>")
                                     (list len-expr)))
       (imports-block (jblock-locvar (jtype-class "List<Acl2Symbol>")
                                     jvar-imports
                                     newlist-expr))
       (imports-block (append imports-block
                              (atj-gen-pkg-method-aux imports
                                                      jvar-imports)))
       (pkg-name-expr (atj-gen-pkg-name pkg))
       (defpkg-block (jblock-smethod *aij-type-pkg*
                                     "define"
                                     (list pkg-name-expr
                                           (jexpr-name jvar-imports))))
       (method-body (append imports-block
                            defpkg-block)))
    (make-jmethod :access (jaccess-private)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-void)
                  :name method-name
                  :params nil
                  :throws nil
                  :body method-body))

  :prepwork
  ((define atj-gen-pkg-method-aux ((imports symbol-listp)
                                   (jvar-imports stringp))
     :returns (block jblockp)
     :parents nil
     (cond ((endp imports) nil)
           (t (b* ((import-expr (atj-gen-symbol (car imports) t nil))
                   (first-block (jblock-method (str::cat jvar-imports ".add")
                                               (list import-expr)))
                   (rest-block (atj-gen-pkg-method-aux (cdr imports)
                                                       jvar-imports)))
                (append first-block rest-block)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-pkg-methods ((pkgs string-listp) (verbose$ booleanp))
  :returns (methods jmethod-listp)
  :short "Generate all the Java methods that add the ACL2 package definitions."
  (if (endp pkgs)
      nil
    (b* ((first-method (atj-gen-pkg-method (car pkgs) verbose$))
         (rest-methods (atj-gen-pkg-methods (cdr pkgs) verbose$)))
      (cons first-method rest-methods))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-pkgs ((pkgs string-listp))
  :returns (block jblockp)
  :short "Generate Java code to build the ACL2 packages."
  :long
  (xdoc::topstring-p
   "This is a sequence of calls to the methods
    generated by @(tsee atj-gen-pkg-methods).
    These calls are part of the code that
    initializes (the Java representation of) the ACL2 environment.")
  (if (endp pkgs)
      nil
    (b* ((method-name (atj-gen-pkg-method-name (car pkgs)))
         (first-block (jblock-method method-name nil))
         (rest-block (atj-gen-pkgs (cdr pkgs))))
      (append first-block rest-block))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-static-initializer ((java-class$ stringp))
  :returns (initializer jcinitializerp)
  :short "Generate the static initializer of the main Java class."
  :long
  (xdoc::topstring
   (xdoc::p
    "This calls the @('build()') method of the environment Java class."))
  (make-jcinitializer
   :static? t
   :code (jblock-smethod (jtype-class (str::cat java-class$ "Environment"))
                         "build"
                         nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-init-method ()
  :returns (method jmethodp)
  :short "Generate the Java public method to initialize the ACL2 environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This method is actually empty,
     but its invocation ensures that the class initializer,
     which builds the ACL2 environment,
     has been executed.")
   (xdoc::p
    "The reason for having an empty initialization method
     and the environment-building code in the static initializer,
     as opposed to having no static initializer
     and the environment-building code in the initialization method,
     is that, in the shallow embedding approach,
     we need the ACL2 environment to be initialized
     before we create certain final static fields that involve ACL2 symbols,
     and that therefore need the ACL2 environment to be built.
     This is unnecessary in the deep embedding approach,
     but we use the same code structure for uniformity and simplicity."))
  (make-jmethod :access (jaccess-public)
                :abstract? nil
                :static? t
                :final? nil
                :synchronized? nil
                :native? nil
                :strictfp? nil
                :result (jresult-void)
                :name "initialize"
                :params nil
                :throws nil
                :body nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-failures-field ()
  :returns (field jfieldp)
  :short "Generate the Java field that keeps track of failures
          in the test Java class."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a private static boolean field that is initially false,
     and gets set if and when any test fails (see below).")
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil')."))
  (make-jfield :access (jaccess-private)
               :static? t
               :final? nil
               :transient? nil
               :volatile? nil
               :type (jtype-boolean)
               :name "failures"
               :init? (jexpr-literal-false)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-method-name ((test-name stringp))
  :returns (method-name stringp)
  :short "Name of the Java method to run one of the specified tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "We generate a private static method for each test
     specified by the @(':tests') input.
     This function generates the name of this method,
     which has the form @('test_...'),
     where @('...') is the name of the test.
     Since ATJ checks that the tests have unique names,
     this scheme ensures that the method names are all distinct.")
   (xdoc::p
    "The argument of this function is the name of the test."))
  (str::cat "test_" test-name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-run-tests ((tests$ atj-test-listp))
  :returns (block jblockp)
  :short "Generate Java code to run the specified tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "This is a sequence of calls to the methods
     generated by @(tsee atj-gen-test-methods).
     These calls are part of the main method of the test Java class."))
  (if (endp tests$)
      nil
    (b* ((method-name
          (atj-gen-test-method-name (atj-test->name (car tests$))))
         (first-block (jblock-method method-name (list (jexpr-name "n"))))
         (rest-block (atj-gen-run-tests (cdr tests$))))
      (append first-block rest-block))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-main-method ((tests$ atj-test-listp)
                                  (java-class$ stringp))
  :returns (method jmethodp)
  :short "Generate the Java main method for the test Java class."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "This method initializes the ACL2 environment
     and then calls each test method.
     It also prints a message saying whether all tests passed or not.")
   (xdoc::p
    "If no argument is passed to this method
     (the argument normally comes from the command line,
     when the generated code is called as a Java application),
     then the test methods are called with 0 as the repetition parameter:
     that is, no time information is printed.
     Otherwise, there must exactly one argument
     that must parse to a positive integer,
     which is passed as the repetition parameter to the test methods.")
   (xdoc::p
    "Note that we generate an expression name for @('args.length'),
     because grammatically this is not a field access expression in Java:
     it cannot be generated from the nonterminal @('field-acces');
     it can be generated from the nonterminal @('expression-name')."))
  (b* ((method-param (make-jparam :final? nil
                                  :type (jtype-array (jtype-class "String"))
                                  :name "args"))
       (method-body
        (append
         (jblock-locvar (jtype-int) "n" (jexpr-literal-0))
         (jblock-if (jexpr-binary (jbinop-eq)
                                  (jexpr-name "args.length")
                                  (jexpr-literal-1))
                    (jblock-asg (jexpr-name "n")
                                (jexpr-smethod (jtype-class "Integer")
                                               "parseInt"
                                               (list
                                                (jexpr-array
                                                 (jexpr-name "args")
                                                 (jexpr-literal-0))))))
         (jblock-if (jexpr-binary (jbinop-gt)
                                  (jexpr-name "args.length")
                                  (jexpr-literal-1))
                    (jblock-throw (jexpr-newclass
                                   (jtype-class "IllegalArgumentException")
                                   (list (jexpr-literal-string
                                          "There must be 0 or 1 arguments.")))))
         (jblock-smethod (jtype-class java-class$) "initialize" nil)
         (atj-gen-run-tests tests$)
         (jblock-ifelse (jexpr-name "failures")
                        (append
                         (jblock-imethod (jexpr-name "System.out")
                                         "println"
                                         (list (atj-gen-jstring
                                                "Some tests failed.")))
                         (jblock-imethod (jexpr-name "System.out")
                                         "println"
                                         nil)
                         (jblock-smethod (jtype-class "System")
                                         "exit"
                                         (list (jexpr-literal-1))))
                        (append
                         (jblock-imethod (jexpr-name "System.out")
                                         "println"
                                         (list (atj-gen-jstring
                                                "All tests passed.")))
                         (jblock-imethod (jexpr-name "System.out")
                                         "println"
                                         nil)
                         (jblock-smethod (jtype-class "System")
                                         "exit"
                                         (list (jexpr-literal-0))))))))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-void)
                  :name "main"
                  :params (list method-param)
                  :throws (list *aij-class-undef-pkg-exc*)
                  :body method-body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-value ((tvalue atj-test-valuep)
                            (jvar-value-base stringp)
                            (jvar-value-index posp)
                            (deep$ booleanp)
                            (guards$ booleanp))
  :returns (mv (block jblockp)
               (expr jexprp)
               (type atj-typep)
               (new-jvar-value-index posp :hyp (posp jvar-value-index)))
  :short "Generate the Java code for a test value."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee atj-gen-value) for @('a') test values;
     this is why this function has the @('jvar-value-...') arguments
     and returns the @('new-jvar-value-index') result.")
   (xdoc::p
    "For @('j') test values, we use
     @(tsee atj-gen-jboolean) and similar functions.")
   (xdoc::p
    "In both cases, we also return the ATJ type of the expression.
     In the shallow embedding, this will determine the Java type
     of the local variable that stores the value."))
  (atj-test-value-case
   tvalue
   :acl2 (b* (((mv block expr jvar-value-index)
               (atj-gen-value tvalue.get
                              jvar-value-base
                              jvar-value-index
                              deep$
                              guards$)))
           (mv block
               expr
               (atj-type-of-value tvalue.get)
               jvar-value-index))
   :jboolean (mv nil
                 (atj-gen-jboolean (boolean-value->bool tvalue.get))
                 (atj-type-jprim (primitive-type-boolean))
                 jvar-value-index)
   :jchar (mv nil
              (atj-gen-jchar (char-value->nat tvalue.get))
              (atj-type-jprim (primitive-type-char))
              jvar-value-index)
   :jbyte (mv nil
              (atj-gen-jbyte (byte-value->int tvalue.get))
              (atj-type-jprim (primitive-type-byte))
              jvar-value-index)
   :jshort (mv nil
               (atj-gen-jshort (short-value->int tvalue.get))
               (atj-type-jprim (primitive-type-short))
               jvar-value-index)
   :jint (mv nil
             (atj-gen-jint (int-value->int tvalue.get))
             (atj-type-jprim (primitive-type-int))
             jvar-value-index)
   :jlong (mv nil
              (atj-gen-jlong (long-value->int tvalue.get))
              (atj-type-jprim (primitive-type-long))
              jvar-value-index)
   :jboolean[] (mv nil
                   (atj-gen-jboolean-array tvalue.get)
                   (atj-type-jprimarr (primitive-type-boolean))
                   jvar-value-index)
   :jchar[] (mv nil
                (atj-gen-jchar-array tvalue.get)
                (atj-type-jprimarr (primitive-type-char))
                jvar-value-index)
   :jbyte[] (mv nil
                (atj-gen-jbyte-array tvalue.get)
                (atj-type-jprimarr (primitive-type-byte))
                jvar-value-index)
   :jshort[] (mv nil
                 (atj-gen-jshort-array tvalue.get)
                 (atj-type-jprimarr (primitive-type-short))
                 jvar-value-index)
   :jint[] (mv nil
               (atj-gen-jint-array tvalue.get)
               (atj-type-jprimarr (primitive-type-int))
               jvar-value-index)
   :jlong[] (mv nil
                (atj-gen-jlong-array tvalue.get)
                (atj-type-jprimarr (primitive-type-long))
                jvar-value-index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-values ((tvalues atj-test-value-listp)
                             (jvar-value-base stringp)
                             (jvar-value-index posp)
                             (deep$ booleanp)
                             (guards$ booleanp))
  :returns (mv (block jblockp)
               (exprs jexpr-listp)
               (types atj-type-listp)
               (new-jvar-value-index posp :hyp (posp jvar-value-index)))
  :short "Lift @(tsee atj-gen-test-value) to lists."
  (b* (((when (endp tvalues)) (mv nil nil nil jvar-value-index))
       ((mv first-block first-expr first-type jvar-value-index)
        (atj-gen-test-value (car tvalues)
                            jvar-value-base
                            jvar-value-index
                            deep$
                            guards$))
       ((mv rest-block rest-exprs rest-types jvar-value-index)
        (atj-gen-test-values (cdr tvalues)
                             jvar-value-base
                             jvar-value-index
                             deep$
                             guards$)))
    (mv (append first-block rest-block)
        (cons first-expr rest-exprs)
        (cons first-type rest-types)
        jvar-value-index))
  ///

  (defret len-of-atj-gen-test-values.exprs
    (equal (len exprs) (len tvalues)))

  (defret len-of-atj-gen-test-values.types
    (equal (len types) (len tvalues)))

  (defret consp-of-atj-gen-test-values.exprs
    (implies (consp tvalues)
             (consp exprs))
    :rule-classes :type-prescription)

  (defret consp-of-atj-gen-test-values.types
    (implies (consp tvalues)
             (consp types))
    :rule-classes :type-prescription))
