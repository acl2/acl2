; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

; Avoid failure for atj-gen-anumber in ACL2(r):
; cert_param: non-acl2r

(include-book "library-extensions")
(include-book "test-structures")
(include-book "pretty-printer")

(include-book "kestrel/std/basic/symbol-package-name-lst" :dir :system)
(include-book "kestrel/utilities/strings/hexchars" :dir :system)
(include-book "kestrel/utilities/system/term-function-recognizers" :dir :system)
(include-book "kestrel/utilities/system/world-queries" :dir :system)

(defrulel natp-of-incremented-index
  (implies (natp x)
           (natp (1+ x))))

(defrulel posp-of-incremented-index
  (implies (posp x)
           (posp (1+ x))))

(local (in-theory (disable natp posp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-code-generation
  :parents (atj-implementation)
  :short "Code generation performed by ATJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate Java abstract syntax,
     which we then pretty-print to files.")
   (xdoc::p
    "We translate ACL2 values, expressions, and lambda expressions
     to Java expressions ``preceded by'' Java blocks.
     By this we mean that the relevant code generation functions
     in general return a Java block and a Java expression,
     such that the block must be executed before the expression.
     That is, the Java block provides the necessary code
     to ``prepare'' the evaluation of the Java expression.
     The Java block may include Java expressions and blocks
     that are recursively generated.")
   (xdoc::p
    "To illustrate this concept,
     consider the generation of a Java expression to build
     the Java representation of an ACL2 @(tsee cons) pair.
     The pair may be a large binary tree,
     so we prefer not to generate a large Java expression.
     Instead, we generate
     a Java block that sets a local variable to the @(tsee car),
     a Java block that sets another local variable to the @(tsee cdr),
     and then a Java expression that builds the pair
     from those two variables.
     The two blocks are concatenated to result in a block and an expression
     for the @(tsee cons) pair in question.
     But the expressions assigned to the two local variables
     may in turn need to be built that way, recursively.
     This recursion ends when an atom value is reached.
     A similar strategy is used to build
     Java representations of ACL2 terms and lambda expressions,
     which have a recursive structure analogously to @(tsee cons) pairs.")
   (xdoc::p
    "As special cases, some of these code generation functions
     may return just Java expressions and no blocks,
     since they would return always empty blocks.")
   (xdoc::p
    "These code generation functions keep track
     of the next local variables to use
     via numeric indices that are threaded through the functions.
     The indices are appended to the base names for the local variables
     in order to guarantee the uniqueness of the local variables.")
   (xdoc::p
    "The @('atj-gen-deep-...') functions are used
     for the deep embedding approach.
     The @('atj-gen-shallow-...') functions are used
     for the shallow embedding approach.
     The other functions are generally used for both approaches."))
  :order-subtopics t
  :default-parent t)

(defsection atj-aij-class-consts
  :short "ACL2 named constants for the AIJ class names."
  (defconst *atj-jclass-char*      "Acl2Character")
  (defconst *atj-jclass-complex*   "Acl2ComplexRational")
  (defconst *atj-jclass-cons*      "Acl2ConsPair")
  (defconst *atj-jclass-def-fn*    "Acl2DefinedFunction")
  (defconst *atj-jclass-eval-exc*  "Acl2EvaluationException")
  (defconst *atj-jclass-fn*        "Acl2Function")
  (defconst *atj-jclass-fn-app*    "Acl2FunctionApplication")
  (defconst *atj-jclass-int*       "Acl2Integer")
  (defconst *atj-jclass-lambda*    "Acl2LambdaExpression")
  (defconst *atj-jclass-named-fn*  "Acl2NamedFunction")
  (defconst *atj-jclass-native-fn* "Acl2NativeFunction")
  (defconst *atj-jclass-number*    "Acl2Number")
  (defconst *atj-jclass-pkg*       "Acl2Package")
  (defconst *atj-jclass-pkg-name*  "Acl2PackageName")
  (defconst *atj-jclass-qconst*    "Acl2QuotedConstant")
  (defconst *atj-jclass-ratio*     "Acl2Ratio")
  (defconst *atj-jclass-rational*  "Acl2Rational")
  (defconst *atj-jclass-string*    "Acl2String")
  (defconst *atj-jclass-symbol*    "Acl2Symbol")
  (defconst *atj-jclass-term*      "Acl2Term")
  (defconst *atj-jclass-value*     "Acl2Value")
  (defconst *atj-jclass-var*       "Acl2Variable"))

(defsection atj-aij-type-consts
  :short "ACL2 named constants for the AIJ (class) types."
  (defconst *atj-jtype-char*      (jtype-class *atj-jclass-char*))
  (defconst *atj-jtype-complex*   (jtype-class *atj-jclass-complex*))
  (defconst *atj-jtype-cons*      (jtype-class *atj-jclass-cons*))
  (defconst *atj-jtype-def-fn*    (jtype-class *atj-jclass-def-fn*))
  (defconst *atj-jtype-eval-exc*  (jtype-class *atj-jclass-eval-exc*))
  (defconst *atj-jtype-fn*        (jtype-class *atj-jclass-fn*))
  (defconst *atj-jtype-fn-app*    (jtype-class *atj-jclass-fn-app*))
  (defconst *atj-jtype-int*       (jtype-class *atj-jclass-int*))
  (defconst *atj-jtype-lambda*    (jtype-class *atj-jclass-lambda*))
  (defconst *atj-jtype-named-fn*  (jtype-class *atj-jclass-named-fn*))
  (defconst *atj-jtype-native-fn* (jtype-class *atj-jclass-native-fn*))
  (defconst *atj-jtype-number*    (jtype-class *atj-jclass-number*))
  (defconst *atj-jtype-pkg*       (jtype-class *atj-jclass-pkg*))
  (defconst *atj-jtype-pkg-name*  (jtype-class *atj-jclass-pkg-name*))
  (defconst *atj-jtype-qconst*    (jtype-class *atj-jclass-qconst*))
  (defconst *atj-jtype-ratio*     (jtype-class *atj-jclass-ratio*))
  (defconst *atj-jtype-rational*  (jtype-class *atj-jclass-rational*))
  (defconst *atj-jtype-string*    (jtype-class *atj-jclass-string*))
  (defconst *atj-jtype-symbol*    (jtype-class *atj-jclass-symbol*))
  (defconst *atj-jtype-term*      (jtype-class *atj-jclass-term*))
  (defconst *atj-jtype-value*     (jtype-class *atj-jclass-value*))
  (defconst *atj-jtype-var*       (jtype-class *atj-jclass-var*)))

(define atj-achars-to-jhexcodes ((achars character-listp))
  :returns (jexprs jexpr-listp)
  :short "Turn a list of ACL2 characters
          into a list of Java hexadecimal literal expressions
          corresponding to the character codes,
          in the same order."
  (cond ((endp achars) nil)
        (t (cons (jexpr-literal
                  (make-jliteral-integer :value (char-code (car achars))
                                         :long? nil
                                         :base (jintbase-hexadecimal)))
                 (atj-achars-to-jhexcodes (cdr achars))))))

(define atj-gen-jstring ((astring stringp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build a Java string from an ACL2 string."
  :long
  (xdoc::topstring
   (xdoc::p
    "Often, an ACL2 string can be turned into a Java string literal
     that is valid when pretty-printed.
     Examples are @('\"abc\"') or @('\"x-y @ 5.A\"').")
   (xdoc::p
    "However, if the ACL2 string includes characters like @('#\Return'),
     turning into a Java string literal
     may result in an invalid one when pretty-printed.
     In this case, a safe way to build the Java string is
     via a Java character array with an initializer
     consisting of the codes of the ACL2 string.")
   (xdoc::p
    "If the ACL2 string consists of only pritable ASCII characters
     (i.e. space and visible ASCII characters),
     we turn it into a Java string literal.
     Otherwise, we turn it into a Java array creation expression."))
  (b* ((achars (explode astring)))
    (if (printable-charlist-p achars)
        (jexpr-literal-string astring)
      (jexpr-newarray-init (jtype-char) (atj-achars-to-jhexcodes achars)))))

(define atj-gen-jparamlist-avalues ((names string-listp))
  :returns (jparams jparam-listp)
  :short "Generate a Java formal parameter list for ACL2 values,
          from the names of the parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a list of Java parameter names,
     this function generates a Java formal parameter list
     that associates the Java type @('Acl2Value') for ACL2 values
     to each name."))
  (cond ((endp names) nil)
        (t (cons (make-jparam :final? nil
                              :type *atj-jtype-value*
                              :name (car names))
                 (atj-gen-jparamlist-avalues (cdr names))))))

(define atj-achar-to-jchars-id ((achar characterp)
                                (startp booleanp)
                                (flip-case-p booleanp))
  :returns (jchars character-listp :hyp (characterp achar))
  :short "Turn an ACL2 character into one or more Java characters
          of an ASCII Java identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "For various purposes,
     we want to turn ACL2 symbols and package names into Java identifiers.
     ACL2 symbols may consist of arbitrary sequences of 8-bit characters,
     while Java identifiers may only contain certain Unicode characters;
     when Unicode is restricted to ASCII,
     Java identifiers are much more restricted than ACL2 symbols.
     They are also more restricted than ACL2 package names,
     although ACL2 package names have restrictions of their own
     compared to Java identifiers, notably the uppercase restriction.")
   (xdoc::p
    "If an ACL2 character (part of an ACL2 symbol or package name) is a letter,
     we keep it unchanged in forming the Java identifier,
     but we flip it from uppercase to lowercase or from lowercase to uppercase
     if the @('flip-case-p') flag is @('t'):
     since ACL2 symbols often have uppercase letters,
     by flipping them to lowercase we generate
     more readable and idiomatic Java identifiers;
     and flipping lowercase letters to uppercase letters avoids conflicts.
     If the ACL2 character is a digit, we keep it unchanged
     only if it is not at the start of the Java identifier:
     this is indicated by the @('startp') flag.
     Otherwise, we turn it into an ``escape'' consisting of
     @('$') followed by two hexadecimal digits for the ASCII code of the digit.
     We use this same mapping for all the ACL2 characters
     that are neither letters nor digits,
     except for dash, which is very common in ACL2 symbols and package names,
     and which we map into an underscore in Java,
     which is allowed in Java identifiers.
     The hexadecimal digits greater than 9 are uppercase.
     Note that @('$') itself, which is valid in Java identifiers,
     is mapped to itself followed by its hex code (not just to itself)
     when it appears in the ACL2 symbol or package name."))
  (cond ((str::up-alpha-p achar) (if flip-case-p
                                     (list (str::downcase-char achar))
                                   (list achar)))
        ((str::down-alpha-p achar) (if flip-case-p
                                       (list (str::upcase-char achar))
                                     (list achar)))
        ((and (digit-char-p achar)
              (not startp)) (list achar))
        ((eql achar #\-) (list #\_))
        (t (b* ((acode (char-code achar))
                ((mv hi-char lo-char) (ubyte8=>hexchars acode)))
             (list #\$ hi-char lo-char)))))

(define atj-achars-to-jchars-id ((achars character-listp)
                                 (startp booleanp)
                                 (flip-case-p booleanp))
  :returns (jchars character-listp :hyp (character-listp achars))
  :short "Lift @(tsee atj-achar-to-jchars-id) to lists."
  :long
  (xdoc::topstring-p
   "This is used on the sequence of characters
    that form an ACL2 symbol or package name;
    see the callers of this function for details.
    The @('startp') flag becomes @('nil') at the first recursive call,
    because after the first character
    we are no longer at the start of the Java identifier.")
  (cond ((endp achars) nil)
        (t (append (atj-achar-to-jchars-id (car achars) startp flip-case-p)
                   (atj-achars-to-jchars-id (cdr achars) nil flip-case-p)))))

(define atj-gen-jlocvar-indexed
  ((var-type jtypep "Type of the local variable.")
   (var-base stringp "Base name of the local variable.")
   (var-index natp "Index of the local variable.")
   (var-init jexprp "Initializer of the local variable."))
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
  (b* ((var-name (str::cat var-base (natstr var-index)))
       (var-index (1+ var-index))
       (locvar-block (jblock-locvar var-type var-name var-init)))
    (mv locvar-block var-name var-index))
  ///

  (defrule posp-of-atj-gen-jlocvar-indexed-new-var-index
    (implies (posp var-index)
             (posp (mv-nth 2 (atj-gen-jlocvar-indexed
                              var-type var-base var-index var-init))))))

(define atj-gen-achar ((achar characterp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 character."
  (jexpr-smethod *atj-jtype-char*
                 "make"
                 (list (jexpr-cast (jtype-char)
                                   (jexpr-literal-integer-decimal
                                    (char-code achar))))))

(define atj-gen-astring ((astring stringp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 string."
  (jexpr-smethod *atj-jtype-string*
                 "make"
                 (list (atj-gen-jstring astring))))

(define atj-gen-asymbol ((asymbol symbolp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 symbol."
  :long
  (xdoc::topstring-p
   "Since AIJ has a number of constants (i.e. static final fields)
    for a number of common symbols,
    we just reference the appropriate constant
    if the symbol in question is among those symbols.
    Otherwise, we build it in the general way.
    Overall, this makes the generated Java code faster.")
  (cond
   ((eq asymbol 't) (jexpr-name "Acl2Symbol.T"))
   ((eq asymbol 'nil) (jexpr-name "Acl2Symbol.NIL"))
   ((eq asymbol 'list) (jexpr-name "Acl2Symbol.LIST"))
   ((eq asymbol 'if) (jexpr-name "Acl2Symbol.IF"))
   ((eq asymbol 'characterp) (jexpr-name "Acl2Symbol.CHARACTERP"))
   ((eq asymbol 'stringp) (jexpr-name "Acl2Symbol.STRINGP"))
   ((eq asymbol 'symbolp) (jexpr-name "Acl2Symbol.SYMBOLP"))
   ((eq asymbol 'integerp) (jexpr-name "Acl2Symbol.INTEGERP"))
   ((eq asymbol 'rationalp) (jexpr-name "Acl2Symbol.RATIONALP"))
   ((eq asymbol 'complex-rationalp) (jexpr-name "Acl2Symbol.COMPLEX_RATIONALP"))
   ((eq asymbol 'acl2-numberp) (jexpr-name "Acl2Symbol.ACL2_NUMBERP"))
   ((eq asymbol 'consp) (jexpr-name "Acl2Symbol.CONSP"))
   ((eq asymbol 'char-code) (jexpr-name "Acl2Symbol.CHAR_CODE"))
   ((eq asymbol 'code-char) (jexpr-name "Acl2Symbol.CODE_CHAR"))
   ((eq asymbol 'coerce) (jexpr-name "Acl2Symbol.COERCE"))
   ((eq asymbol 'intern-in-package-of-symbol)
    (jexpr-name "Acl2Symbol.INTERN_IN_PACKAGE_OF_SYMBOL"))
   ((eq asymbol 'symbol-package-name)
    (jexpr-name "Acl2Symbol.SYMBOL_PACKAGE_NAME"))
   ((eq asymbol 'symbol-name) (jexpr-name "Acl2Symbol.SYMBOL_NAME"))
   ((eq asymbol 'pkg-imports) (jexpr-name "Acl2Symbol.PKG_IMPORTS"))
   ((eq asymbol 'pkg-witness) (jexpr-name "Acl2Symbol.PKG_WITNESS"))
   ((eq asymbol 'unary--) (jexpr-name "Acl2Symbol.UNARY_MINUS"))
   ((eq asymbol 'unary-/) (jexpr-name "Acl2Symbol.UNARY_SLASH"))
   ((eq asymbol 'binary-+) (jexpr-name "Acl2Symbol.BINARY_PLUS"))
   ((eq asymbol 'binary-*) (jexpr-name "Acl2Symbol.BINARY_STAR"))
   ((eq asymbol '<) (jexpr-name "Acl2Symbol.LESS_THAN"))
   ((eq asymbol 'complex) (jexpr-name "Acl2Symbol.COMPLEX"))
   ((eq asymbol 'realpart) (jexpr-name "Acl2Symbol.REALPART"))
   ((eq asymbol 'imagpart) (jexpr-name "Acl2Symbol.IMAGPART"))
   ((eq asymbol 'numerator) (jexpr-name "Acl2Symbol.NUMERATOR"))
   ((eq asymbol 'denominator) (jexpr-name "Acl2Symbol.DENOMINATOR"))
   ((eq asymbol 'cons) (jexpr-name "Acl2Symbol.CONS"))
   ((eq asymbol 'car) (jexpr-name "Acl2Symbol.CAR"))
   ((eq asymbol 'cdr) (jexpr-name "Acl2Symbol.CDR"))
   ((eq asymbol 'equal) (jexpr-name "Acl2Symbol.EQUAL"))
   ((eq asymbol 'bad-atom<=)
    (jexpr-name "Acl2Symbol.BAD_ATOM_LESS_THAN_OR_EQUAL_TO"))
   ((eq asymbol 'or) (jexpr-name "Acl2Symbol.OR"))
   (t (jexpr-smethod *atj-jtype-symbol*
                     "make"
                     (list (atj-gen-jstring
                            (symbol-package-name asymbol))
                           (atj-gen-jstring
                            (symbol-name asymbol)))))))

(define atj-gen-ainteger ((ainteger integerp))
  :returns (jexpr jexprp)
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
  (b* (((when (= ainteger 0)) (jexpr-name "Acl2Integer.ZERO"))
       ((when (= ainteger 1)) (jexpr-name "Acl2Integer.ONE"))
       (arg (cond ((signed-byte-p 32 ainteger)
                   (if (< ainteger 0)
                       (jexpr-unary (junop-uminus)
                                    (jexpr-literal-integer-decimal
                                     (- ainteger)))
                     (jexpr-literal-integer-decimal ainteger)))
                  ((signed-byte-p 64 ainteger)
                   (if (< ainteger 0)
                       (jexpr-unary (junop-uminus)
                                    (jexpr-literal-integer-long-decimal
                                     (- ainteger)))
                     (jexpr-literal-integer-long-decimal ainteger)))
                  (t (b* ((string (if (< ainteger 0)
                                      (str::cat "-" (str::natstr (- ainteger)))
                                    (str::natstr ainteger))))
                       (jexpr-newclass (jtype-class "BigInteger")
                                       (list
                                        (jexpr-literal-string string))))))))
    (jexpr-smethod *atj-jtype-int*
                   "make"
                   (list arg))))

(define atj-gen-arational ((arational rationalp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 rational."
  (jexpr-smethod *atj-jtype-rational*
                 "make"
                 (list (atj-gen-ainteger (numerator arational))
                       (atj-gen-ainteger (denominator arational)))))

(define atj-gen-anumber ((anumber acl2-numberp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 number."
  (jexpr-smethod *atj-jtype-number*
                 "make"
                 (list (atj-gen-arational (realpart anumber))
                       (atj-gen-arational (imagpart anumber)))))

(defines atj-gen-avalue
  :short "Generate Java code to build an ACL2 value."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a @(tsee cons) pair,
     the generated code
     builds the @(tsee car),
     sets a local variable to it,
     builds the @(tsee cdr),
     sets another local variable to it,
     and returns an expression that builds the pair
     from the two local variables.")
   (xdoc::@def "atj-gen-avalue")
   (xdoc::@def "atj-gen-aconspair"))

  (define atj-gen-aconspair ((aconspair consp)
                             (jvar-value-base stringp)
                             (jvar-value-index posp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index)))
    :parents nil
    (b* (((unless (mbt (consp aconspair)))
          (mv nil (jexpr-name "irrelevant") jvar-value-index))
         ((mv car-jblock
              car-jexpr
              jvar-value-index) (atj-gen-avalue (car aconspair)
                                                jvar-value-base
                                                jvar-value-index))
         ((mv car-locvar-jblock
              car-jvar
              jvar-value-index) (atj-gen-jlocvar-indexed *atj-jtype-value*
                                                         jvar-value-base
                                                         jvar-value-index
                                                         car-jexpr))
         ((mv cdr-jblock
              cdr-jexpr
              jvar-value-index) (atj-gen-avalue (cdr aconspair)
                                                jvar-value-base
                                                jvar-value-index))
         ((mv cdr-locvar-jblock
              cdr-jvar
              jvar-value-index) (atj-gen-jlocvar-indexed *atj-jtype-value*
                                                         jvar-value-base
                                                         jvar-value-index
                                                         cdr-jexpr))
         (jblock (append car-jblock
                         car-locvar-jblock
                         cdr-jblock
                         cdr-locvar-jblock))
         (jexpr (jexpr-smethod *atj-jtype-cons*
                               "make"
                               (list (jexpr-name car-jvar)
                                     (jexpr-name cdr-jvar)))))
      (mv jblock jexpr jvar-value-index))
    :measure (two-nats-measure (acl2-count aconspair) 0))

  (define atj-gen-avalue (avalue
                          (jvar-value-base stringp)
                          (jvar-value-index posp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index)))
    :parents nil
    (cond ((characterp avalue) (mv nil
                                   (atj-gen-achar avalue)
                                   jvar-value-index))
          ((stringp avalue) (mv nil
                                (atj-gen-astring avalue)
                                jvar-value-index))
          ((symbolp avalue) (mv nil
                                (atj-gen-asymbol avalue)
                                jvar-value-index))
          ((integerp avalue) (mv nil
                                 (atj-gen-ainteger avalue)
                                 jvar-value-index))
          ((rationalp avalue) (mv nil
                                  (atj-gen-arational avalue)
                                  jvar-value-index))
          ((acl2-numberp avalue) (mv nil
                                     (atj-gen-anumber avalue)
                                     jvar-value-index))
          ((consp avalue) (atj-gen-aconspair avalue
                                             jvar-value-base
                                             jvar-value-index))
          (t (prog2$ (raise "Internal error: the value ~x0 is a bad atom."
                            avalue)
                     (mv nil (jexpr-name "irrelevant") jvar-value-index))))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-ACONSPAIR decreases:
    :measure (two-nats-measure (acl2-count avalue) 1))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-gen-avalue))

(define atj-gen-avalues ((avalues true-listp)
                         (jvar-value-base stringp)
                         (jvar-value-index posp))
  :returns (mv (jblock jblockp)
               (jexprs jexpr-listp)
               (new-jvar-value-index posp :hyp (posp jvar-value-index)))
  :short "Lift @(tsee atj-gen-avalue) to lists."
  (cond ((endp avalues) (mv nil nil jvar-value-index))
        (t (b* (((mv first-jblock
                     first-jexpr
                     jvar-value-index) (atj-gen-avalue (car avalues)
                                                       jvar-value-base
                                                       jvar-value-index))
                ((mv rest-jblock
                     rest-jexrps
                     jvar-value-index) (atj-gen-avalues (cdr avalues)
                                                        jvar-value-base
                                                        jvar-value-index)))
             (mv (append first-jblock rest-jblock)
                 (cons first-jexpr rest-jexrps)
                 jvar-value-index)))))

(define atj-gen-asymbols ((asymbols symbol-listp))
  :returns (jexprs jexpr-listp)
  :short "Lift @(tsee atj-gen-asymbol) to lists."
  (cond ((endp asymbols) nil)
        (t (cons (atj-gen-asymbol (car asymbols))
                 (atj-gen-asymbols (cdr asymbols))))))

(define atj-gen-deep-aqconst
  ((aqconst "(Unquoted) value of the ACL2 quoted constant.")
   (jvar-value-base stringp)
   (jvar-value-index posp))
  :returns (mv (jblock jblockp)
               (jexpr jexprp)
               (new-jvar-value-index posp :hyp (posp jvar-value-index)))
  :short "Generate Java code to build a deeply embedded ACL2 quoted constant."
  (b* (((mv value-jblock
            value-jexpr
            jvar-value-index) (atj-gen-avalue aqconst
                                              jvar-value-base
                                              jvar-value-index))
       (jblock value-jblock)
       (jexpr (jexpr-smethod *atj-jtype-qconst*
                             "make"
                             (list value-jexpr))))
    (mv jblock jexpr jvar-value-index)))

(define atj-gen-deep-avar ((avar symbolp "The ACL2 variable."))
  :returns (jexpr jexprp)
  :short "Generate Java code to build a deeply embedded ACL2 variable."
  (jexpr-smethod *atj-jtype-var*
                 "make"
                 (list (atj-gen-asymbol avar))))

(define atj-gen-deep-aformals ((aformals symbol-listp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build a deeply embedded formals parameter list
          of an ACL2 named function or lambda expression."
  :long
  (xdoc::topstring-p
   "The generated code builds an array of the formals as symbols.")
  (jexpr-newarray-init *atj-jtype-symbol*
                       (atj-gen-asymbols aformals)))

(defines atj-gen-deep-aterms+alambdas
  :short "Generate Java code to build
          deeply embedded ACL2 terms and lambda expressions."

  (define atj-gen-deep-afnapp ((afn pseudo-termfnp)
                               (aargs pseudo-term-listp)
                               (jvar-value-base stringp)
                               (jvar-value-index posp)
                               (jvar-term-base stringp)
                               (jvar-term-index posp)
                               (jvar-lambda-base stringp)
                               (jvar-lambda-index posp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index))
                 (new-jvar-term-index posp :hyp (posp jvar-term-index))
                 (new-jvar-lambda-index posp :hyp (posp jvar-lambda-index)))
    :parents (atj-code-generation atj-gen-deep-aterms+alambdas)
    :short "Generate Java code to build
            a deeply embedded ACL2 function application."
    :long
    (xdoc::topstring
     (xdoc::p
      "The generated code
       builds the named function or lambda expression,
       builds the argument terms,
       puts them into an array,
       builds the application,
       puts it to a local variable,
       and returns the local variable.")
     (xdoc::p
      "Terms of the form @('(if a a b)') are treated as @('(or a b)'),
       i.e. the generated code builds a term of the form @('(or a b)').
       In ACL2, @(tsee or) is a macro:
       an untranslated term @('(or a b)') is translated to @('(if a a b)'),
       which, if executed as such by AIJ, would evaluate @('a') twice.
       (ACL2 relies on the underlying Lisp platform to optimize this situation.)
       AIJ provides support for a ``pseudo-function'' @('or')
       that evaluates its arguments non-strictly;
       see the documentation of AIJ for details.
       Thus, ATJ recognizes (translated) terms of the form @('(if a a b)'),
       which are likely derived from @('(or a b)'),
       and represents them in AIJ via the @('or') pseudo-function."))
    (b* (((mv afn aargs)
          (if (and (eq afn 'if)
                   (= (len aargs) 3)
                   (equal (first aargs) (second aargs)))
              (mv 'or (list (first aargs) (third aargs)))
            (mv afn aargs)))
         ((mv afn-jblock
              afn-jexpr
              jvar-value-index
              jvar-term-index
              jvar-lambda-index)
          (if (symbolp afn)
              (mv nil
                  (jexpr-smethod *atj-jtype-named-fn*
                                 "make"
                                 (list (atj-gen-asymbol afn)))
                  jvar-value-index
                  jvar-term-index
                  jvar-lambda-index)
            (atj-gen-deep-alambda (lambda-formals afn)
                                  (lambda-body afn)
                                  jvar-value-base
                                  jvar-value-index
                                  jvar-term-base
                                  jvar-term-index
                                  jvar-lambda-base
                                  jvar-lambda-index)))
         ((mv aargs-jblock
              aarg-jexprs
              jvar-value-index
              jvar-term-index
              jvar-lambda-index) (atj-gen-deep-aterms aargs
                                                      jvar-value-base
                                                      jvar-value-index
                                                      jvar-term-base
                                                      jvar-term-index
                                                      jvar-lambda-base
                                                      jvar-lambda-index))
         (aargs-jexpr (jexpr-newarray-init *atj-jtype-term* aarg-jexprs))
         (afnapp-jexpr (jexpr-smethod *atj-jtype-fn-app*
                                      "make"
                                      (list afn-jexpr
                                            aargs-jexpr)))
         ((mv afnapp-locvar-jblock
              afnapp-jvar
              jvar-term-index) (atj-gen-jlocvar-indexed *atj-jtype-term*
                                                        jvar-term-base
                                                        jvar-term-index
                                                        afnapp-jexpr)))
      (mv (append afn-jblock
                  aargs-jblock
                  afnapp-locvar-jblock)
          (jexpr-name afnapp-jvar)
          jvar-value-index
          jvar-term-index
          jvar-lambda-index))
    ;; 2nd component is greater then the one of ATJ-GEN-DEEP-ALAMBDA
    ;; so that the call of ATJ-GEN-DEEP-ALAMBDA decreases
    ;; even when AFN is a non-symbol atom (impossible under the guard):
    :measure (two-nats-measure (+ (acl2-count afn) (acl2-count aargs)) 2))

  (define atj-gen-deep-alambda ((aformals symbol-listp)
                                (abody pseudo-termp)
                                (jvar-value-base stringp)
                                (jvar-value-index posp)
                                (jvar-term-base stringp)
                                (jvar-term-index posp)
                                (jvar-lambda-base stringp)
                                (jvar-lambda-index posp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index))
                 (new-jvar-term-index posp :hyp (posp jvar-term-index))
                 (new-jvar-lambda-index posp :hyp (posp jvar-lambda-index)))
    :parents (atj-code-generation atj-gen-deep-aterms+alambdas)
    :short "Generate Java code to build
            a deeply embedded ACL2 lambda expression."
    :long
    (xdoc::topstring-p
     "The generated code
      puts the formals into an array,
      builds the body,
      builds the lambda expression,
      puts it to a local variable,
      and returns the local variable.")
    (b* ((aformals-jexpr (atj-gen-deep-aformals aformals))
         ((mv abody-jblock
              abody-jexpr
              jvar-value-index
              jvar-term-index
              jvar-lambda-index) (atj-gen-deep-aterm abody
                                                     jvar-value-base
                                                     jvar-value-index
                                                     jvar-term-base
                                                     jvar-term-index
                                                     jvar-lambda-base
                                                     jvar-lambda-index))
         (alambda-jexpr (jexpr-smethod *atj-jtype-lambda*
                                       "make"
                                       (list aformals-jexpr
                                             abody-jexpr)))
         ((mv alambda-locvar-jblock
              alambda-jvar
              jvar-lambda-index) (atj-gen-jlocvar-indexed
                                  *atj-jtype-lambda*
                                  jvar-lambda-base
                                  jvar-lambda-index
                                  alambda-jexpr)))
      (mv (append abody-jblock
                  alambda-locvar-jblock)
          (jexpr-name alambda-jvar)
          jvar-value-index
          jvar-term-index
          jvar-lambda-index))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-DEEP-ATERM decreases:
    :measure (two-nats-measure (acl2-count abody) 1))

  (define atj-gen-deep-aterm ((aterm pseudo-termp)
                              (jvar-value-base stringp)
                              (jvar-value-index posp)
                              (jvar-term-base stringp)
                              (jvar-term-index posp)
                              (jvar-lambda-base stringp)
                              (jvar-lambda-index posp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index))
                 (new-jvar-term-index posp :hyp (posp jvar-term-index))
                 (new-jvar-lambda-index posp :hyp (posp jvar-lambda-index)))
    :parents (atj-code-generation atj-gen-deep-aterms+alambdas)
    :short "Generate Java code to build a deeply embedded ACL2 term."
    (cond ((variablep aterm) (mv nil
                                 (atj-gen-deep-avar aterm)
                                 jvar-value-index
                                 jvar-term-index
                                 jvar-lambda-index))
          ((fquotep aterm) (b* (((mv jblock
                                     jexpr
                                     jvar-value-index)
                                 (atj-gen-deep-aqconst (unquote aterm)
                                                       jvar-value-base
                                                       jvar-value-index)))
                             (mv jblock
                                 jexpr
                                 jvar-value-index
                                 jvar-term-index
                                 jvar-lambda-index)))
          (t (atj-gen-deep-afnapp (ffn-symb aterm)
                                  (fargs aterm)
                                  jvar-value-base
                                  jvar-value-index
                                  jvar-term-base
                                  jvar-term-index
                                  jvar-lambda-base
                                  jvar-lambda-index)))
    :measure (two-nats-measure (acl2-count aterm) 0))

  (define atj-gen-deep-aterms ((aterms pseudo-term-listp)
                               (jvar-value-base stringp)
                               (jvar-value-index posp)
                               (jvar-term-base stringp)
                               (jvar-term-index posp)
                               (jvar-lambda-base stringp)
                               (jvar-lambda-index posp))
    :returns (mv (jblock jblockp)
                 (jexprs jexpr-listp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index))
                 (new-jvar-term-index posp :hyp (posp jvar-term-index))
                 (new-jvar-lambda-index posp :hyp (posp jvar-lambda-index)))
    :parents (atj-code-generation atj-gen-deep-aterms+alambdas)
    :short "Lift @(tsee atj-gen-deep-aterm) to lists."
    (if (endp aterms)
        (mv nil
            nil
            jvar-value-index
            jvar-term-index
            jvar-lambda-index)
      (b* (((mv first-jblock
                jexpr
                jvar-value-index
                jvar-term-index
                jvar-lambda-index) (atj-gen-deep-aterm (car aterms)
                                                       jvar-value-base
                                                       jvar-value-index
                                                       jvar-term-base
                                                       jvar-term-index
                                                       jvar-lambda-base
                                                       jvar-lambda-index))
           ((mv rest-jblock
                jexprs
                jvar-value-index
                jvar-term-index
                jvar-lambda-index) (atj-gen-deep-aterms (cdr aterms)
                                                        jvar-value-base
                                                        jvar-value-index
                                                        jvar-term-base
                                                        jvar-term-index
                                                        jvar-lambda-base
                                                        jvar-lambda-index)))
        (mv (append first-jblock
                    rest-jblock)
            (cons jexpr jexprs)
            jvar-value-index
            jvar-term-index
            jvar-lambda-index)))
    :measure (two-nats-measure (acl2-count aterms) 0))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-gen-deep-aterm
    :hints (("Goal" :in-theory (enable pseudo-termfnp acl2::pseudo-lambdap)))))

(defval *atj-disallowed-shallow-jvars*
  :short "Disallowed Java variable names
          for the shallowly embedded ACL2 variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 variable is turned into a Java variable.
     The function @(tsee atj-achars-to-jchars-id) takes care of
     ensuring that only characters valid for Java identifiers are used,
     but this is not sufficient:
     a Java variable name cannot be a keyword,
     a boolean literal, or the null literal.")
   (xdoc::p
    "This constant collects these disallowed sequences of characters,
     which otherwise consist of valid Java identifier characters.
     It also includes the empty sequence,
     because an ACL2 symbol may consist of no characters,
     but a Java identifier cannot be empty."))
  (append *atj-java-keywords*
          *atj-java-boolean-literals*
          (list *atj-java-null-literal*)
          (list ""))
  ///
  (assert-event (string-listp *atj-disallowed-shallow-jvars*))
  (assert-event (no-duplicatesp-equal *atj-disallowed-shallow-jvars*)))

(define atj-gen-shallow-avar ((avar symbolp)
                              (index natp)
                              (curr-apkg stringp)
                              (avars-by-name string-symbols-alistp))
  :returns (jvar-name stringp)
  :short "Generate a shallowly embedded ACL2 variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 variable is turned into a Java variable:
     either a local variable or a method parameter.
     This function computes the name of the Java variable
     from the ACL2 variable.")
   (xdoc::p
    "Each ACL2 function is turned into a Java method,
     whose body is a shallowly embedded representation
     of the ACL2 function body.
     The ACL2 function body may reference the ACL2 function's parameter,
     as well as @(tsee let)-bound variables (via lambda expressions).
     Thus, the same variable symbol may in fact denote different variables
     in different parts of an ACL2 function body.
     Java does not allow different local variables with the same name
     in (nested scopes in) the same method,
     and so we need to map homonymous but different ACL2 variables
     in the same ACL2 function
     to differently named Java variables
     in the same Java method.
     We use numeric indices, one for each variable name,
     which is appended (as explained below) to the Java variable name
     to make it unique within the Java mehtod.")
   (xdoc::p
    "Another need for disambiguation arises because of package prefixes.
     An ACL2 variable is a symbol,
     which consists of a name and also a package name:
     two distinct variables may have the same name
     but different package names.
     However, when we append the package name and the name of the symbol,
     we have unique Java variable names.")
   (xdoc::p
    "Systematically prefixing, in the generated Java variables,
     every symbol name with the package prefix affects readability.
     In ACL2, package prefixes are normally omitted
     for symbols in the current ACL2 package.
     Here we do something similar for the Java variable names,
     where the notion of current package is as follows.
     As mentioned above, each ACL2 function is turned into a Java method:
     this method is inside a Java class whose name is derived from
     the ACL2 package name of the function name:
     thus, the ``current package'' in this context is
     the one of the function name.
     This is the @('curr-apkg') parameter of this code generation function.")
   (xdoc::p
    "Given an ACL2 variable (i.e. symbol)
     with name @('name') and package name @('pname'),
     in general the generated Java variable name is
     @('<pname>$$$<name>$$<index>'),
     where @('<pname>') and @('<name>') are representations of the ACL2 names
     that are valid for Java identifiers,
     and @('<index>') is a decimal representation of the numeric index.")
   (xdoc::p
    "If @('<pname>') is the same as the current package,
     we omit @('<pname>$$$').
     We omit @('<pname>$$$') also when the variable
     is the only one with name @('<name>')
     within the ``current'' ACL2 function:
     since the scope of Java method parameters and local variables
     is limited to the method where they occur,
     no naming conflict may arise in this case.
     The parameter @('avars-by-name') consists of
     all the variables in the current ACL2 function,
     organized by symbol name for easy lookup.
     We retrieve the variables with the same name of the variable,
     we remove the variables from them,
     and we check if the result is empty:
     in this case, this is the only variable with that name.
     (The alist may have duplicate symbols in its values.)")
   (xdoc::p
    "If the index is 0, we omit @('$$<index>'),
     so that if there is just one variable with a certain name,
     since we start with index 0, no index is added to the name.")
   (xdoc::p
    "Thus there are a few combinations possible with these three parts;
     the use of triple and double @('$') characters guarantees
     that there is no confusion with the @('$hh') escapes
     where @('hh') is the hex code of an ACL2 character
     that is not valid for a Java identifier.
     Furthermore, if the resulting variable name is just @('<name>')
     and happens to be a Java keyword or Java literal or empty,
     we add a single @('$') at the end, which again is unambiguous.")
   (xdoc::p
    "This is a relatively simple and uniform scheme to keep names unique,
     but we may improve it to generate more readable names.")
   (xdoc::p
    "We call @(tsee atj-achars-to-jchars-id) to create
     @('<pname') and @('<name>') from @('pname') and @('name').
     If there is a package prefix, the @('startp') flag is @('t')
     only for @('pname'), but not for @('name'),
     because @('<name>') is not the start of the Java identifier.
     Otherwise, @('startp') is @('t') for @('name')
     if there is no package prefix."))
  (b* ((apkg (symbol-package-name avar))
       (omit-pname? (or (equal apkg curr-apkg)
                        (null (remove-eq
                               avar
                               (cdr (assoc-equal (symbol-name avar)
                                                 avars-by-name))))))
       (pname$$$-jchars (if omit-pname?
                            nil
                          (append (atj-achars-to-jchars-id (explode apkg) t t)
                                  (list #\$ #\$ #\$))))
       (name-jchars (atj-achars-to-jchars-id (explode (symbol-name avar))
                                             (endp pname$$$-jchars)
                                             t))
       ($$index-jchars (if (= index 0)
                           nil
                         (append (list #\$ #\$)
                                 (str::natchars index))))
       (jchars (append pname$$$-jchars name-jchars $$index-jchars))
       (jvar (implode jchars))
       (jvar (if (member-equal jvar *atj-disallowed-shallow-jvars*)
                 (str::cat jvar "$")
               jvar)))
    jvar))

(define atj-gen-shallow-avars ((avars symbol-listp)
                               (jvar-indices symbol-nat-alistp)
                               (curr-apkg stringp)
                               (avars-by-name string-symbols-alistp))
  :returns (mv (jvar-names symbol-string-alistp :hyp (symbol-listp avars))
               (new-jvar-indices
                symbol-nat-alistp
                :hyp (and (symbol-listp avars)
                          (symbol-nat-alistp jvar-indices))))
  :verify-guards nil
  :short "Generate a sequence of shallowly embedded ACL2 variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-gen-shallow-avar),
     the shallowly embedded ACL2 variables are made unique via indices.
     There is an independent index for each ACL2 variable,
     so we use an alist from symbols to natural numbers
     to keep track of these indices.
     This alist is threaded through the code generation functions.")
   (xdoc::p
    "In ACL2, a variable is ``introduced''
     as a formal parameter of a function or lambda expression,
     and then referenced in the body of the function or lambda expression.
     The choice and use of the index must be done at this introduction time,
     and not at every reference to the variable after its introduction.
     Thus, in the shallow embedding approach,
     when we encounter the formals of a function or lambda expression,
     we generate the Java variable names for these ACL2 variables,
     using the current indices, and update and return the indices.
     This code generation function does that,
     and returns the generated Java variables as an alist
     from the ACL2 variables (symbols) to the Java variables (strings).")
   (xdoc::p
    "Each ACL2 variable in the list is processed as follows.
     If it has no index in the alist of indices,
     it has index 0,
     and the alist is extended to associate 1 (the next index) to the symbol.
     Otherwise, the index in the alist is used,
     and the alist is updated with the next index."))
  (b* (((when (endp avars)) (mv nil jvar-indices))
       (avar (car avars))
       (avar+index (assoc-eq avar jvar-indices))
       (index (if avar+index (cdr avar+index) 0))
       (jvar-indices (acons avar (1+ index) jvar-indices))
       ((mv jvar-names jvar-indices) (atj-gen-shallow-avars (cdr avars)
                                                            jvar-indices
                                                            curr-apkg
                                                            avars-by-name)))
    (mv (acons avar
               (atj-gen-shallow-avar avar index curr-apkg avars-by-name)
               jvar-names)
        jvar-indices)))

(defval *atj-aij-class-names*
  :short "Names of the Java classes that form AIJ."
  (list *atj-jclass-char*
        *atj-jclass-complex*
        *atj-jclass-cons*
        *atj-jclass-def-fn*
        *atj-jclass-eval-exc*
        *atj-jclass-fn*
        *atj-jclass-fn-app*
        *atj-jclass-int*
        *atj-jclass-lambda*
        *atj-jclass-named-fn*
        *atj-jclass-native-fn*
        *atj-jclass-number*
        *atj-jclass-pkg*
        *atj-jclass-pkg-name*
        *atj-jclass-qconst*
        *atj-jclass-ratio*
        *atj-jclass-rational*
        *atj-jclass-string*
        *atj-jclass-symbol*
        *atj-jclass-term*
        *atj-jclass-value*
        *atj-jclass-var*)
  ///
  (assert-event (string-listp *atj-aij-class-names*))
  (assert-event (no-duplicatesp-equal *atj-aij-class-names*)))

(defval *atj-disallowed-shallow-jclasses*
  :short "Disallowed Java class names
          for the shallowly embedded ACL2 packages."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     a Java class is generated for each ACL2 package
     that includes ACL2 functions for which we generate Java code.
     Each ACL2 function is turned into a Java method in that Java class.")
   (xdoc::p
    "The name of the Java class is obtained from the name of the ACL2 package,
     but since the generated Java code imports some classes
     from other Java packages,
     we need to make sure that the Java class name for an ACL2 package
     does not conflict with any of the imported classes.")
   (xdoc::p
    "The generated Java code imports all the classes
     in the Java package of AIJ, as well as some other Java library classes.
     This constant collects all of these.")
   (xdoc::p
    "We also disallow Java keywords, boolean literals, and null literal,
     which are not valid Java identiers.
     There is no need to exclude the empty string explicitly,
     because ACL2 package names are never empty
     and thus they never result in the empty string."))
  (append *atj-java-keywords*
          *atj-java-boolean-literals*
          (list *atj-java-null-literal*)
          *atj-aij-class-names*
          (list "BigInteger"
                "ArrayList"
                "List"))
  ///
  (assert-event (string-listp *atj-disallowed-shallow-jclasses*))
  (assert-event (no-duplicatesp-equal *atj-disallowed-shallow-jclasses*)))

(define atj-gen-shallow-apkgname ((apkg stringp) (java-class$ stringp))
  :returns (jclass-name stringp)
  :short "Generate a shallowly embedded ACL2 package name."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     a Java class is generated for each ACL2 package
     that includes ACL2 functions that we generate Java code for.
     Each ACL2 function is turned into a Java method in that Java class.")
   (xdoc::p
    "The name of the Java class for the ACL2 package
     is obtained by turning the ACL2 package name
     into a valid Java identifier,
     in the same way as done for shallowly embedded Java variables.
     The resulting Java class name
     must not be a keyword, a boolean or null literal,
     or any of the imported Java classes
     (see @(tsee *atj-disallowed-shallow-jclasses*)).
     We also ensure that is is distinct from the main class generated.
     If the candidate Java class name is one of these,
     we add a @('$') at the end."))
  (b* ((jchars (atj-achars-to-jchars-id (explode apkg) t nil))
       (jstring (implode jchars))
       (jstring (if (or (member-equal jstring *atj-disallowed-shallow-jclasses*)
                        (equal jstring java-class$))
                    (str::cat jstring "$")
                  jstring)))
    jstring))

(defval *atj-disallowed-shallow-jmethods*
  :short "Disallowed Java method names
          for the shallowly embedded ACL2 functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     ACL2 function names are turned into Java method names
     that must be valid identifiers.
     The same character mapping used for ACL2 variables and package names
     is used for ACL2 function names,
     but the result must be a valid Java identifier,
     which means that it must not be
     a Java keyword, boolean or null literal, or empty.")
   (xdoc::p
    "This constant collects these disallowed names."))
  (append *atj-java-keywords*
          *atj-java-boolean-literals*
          (list *atj-java-null-literal*)
          (list ""))
  ///
  (assert-event (string-listp *atj-disallowed-shallow-jmethods*))
  (assert-event (no-duplicatesp-equal *atj-disallowed-shallow-jmethods*)))

(define atj-gen-shallow-afnname ((afn symbolp) (curr-apkg stringp))
  :returns (jmethod-name stringp)
  :short "Generate a shallowly embedded ACL2 function name."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 function is represented as a Java method.
     The Java methods for all the ACL2 functions that are translated to Java
     are partitioned by ACL2 packages:
     there is a Java class for each ACL2 package,
     and the Java method for each ACL2 function
     is in the Java class corresponding to the ACL2 package of the function.")
   (xdoc::p
    "These are all static methods, which can therefore be referenced as
     @('<jclass>.<jmethod>') in Java code,
     not dissmilarly to @('<apkg>::<afn>') in ACL2.
     However, inside @('<jclass>'), it suffices to use @('<jmethod>'),
     which is more readable.
     Thus, somewhat analogously to @(tsee atj-gen-shallow-avar),
     we prepend the Java class name to the Java method name
     if and only if the current ACL2 package (the @('curr-apkg') argument)
     differs from the ACL2 function's package.")
   (xdoc::p
    "The Java class name @('<jclass>') is generated
     via @(tsee atj-gen-shallow-apkgname).
     The method name is generated using the same character mapping
     used for shallowly embedded ACL2 variables and package names.
     We avoid Java keyword, boolean and null literals,
     and the empty string,
     by appending a @('$') at their end if they come up."))
  (b* ((apkg (symbol-package-name afn))
       (jclass.-jchars (if (equal apkg curr-apkg)
                           nil
                         (append (atj-achars-to-jchars-id (explode apkg) t nil)
                                 (list #\.))))
       (jmethod-jchars (atj-achars-to-jchars-id (explode
                                                 (symbol-name afn)) t t))
       (jmethod-jchars (if (member-equal (implode jmethod-jchars)
                                         *atj-disallowed-shallow-jmethods*)
                           (rcons #\$ jmethod-jchars)
                         jmethod-jchars))
       (jchars (append jclass.-jchars jmethod-jchars))
       (jstring (implode jchars)))
    jstring)
  :prepwork
  ((local (include-book "std/typed-lists/character-listp" :dir :system))))

(define atj-gen-shallow-let-bindings ((avars symbol-listp)
                                      (jexprs msg-listp)
                                      (jvar-names symbol-string-alistp))
  :guard (and (= (len jexprs) (len avars))
              (subsetp-eq avars (strip-cars jvar-names)))
  :returns (jblock jblockp)
  :verify-guards nil
  :short "Generate shallowly embedded ACL2 @(tsee let) bindings."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     ACL2 lambda expressions (i.e. @(tsee let)s)
     are handled by introducing Java local variables
     for the formal parameters of the lambda expression
     and assigning to them the Java expressions
     generated from the actual parameters of the lambda expression.
     This function generates these bindings,
     given the ACL2 variables that are the formal arguments
     and the Java expressions to assign to them.")
   (xdoc::p
    "The names for the local variables
     are generated by @(tsee atj-gen-shallow-avars)
     prior to calling this function,
     and thus the names of the Java local variables
     are stored in the @('jvar-names') alist."))
  (b* (((when (endp avars)) nil)
       (avar (car avars))
       (jexpr (car jexprs))
       (jvar (cdr (assoc-eq avar jvar-names)))
       (first-jblock (jblock-locvar *atj-jtype-value* jvar jexpr))
       (rest-jblock (atj-gen-shallow-let-bindings (cdr avars)
                                                  (cdr jexprs)
                                                  jvar-names)))
    (append first-jblock rest-jblock)))

(defines atj-gen-shallow-aterms+alambdas
  :short "Generate shallowly embedded ACL2 terms and lambda expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     the actual arguments of an ACL2 function or lambda expression
     are calculated by the generated Java code,
     and then the (shallowly embedded) ACL2 function or lambda expression
     is called on them.
     However, for the non-strict function @(tsee if)
     and the non-strict ``pseudo-function'' @('or')
     (see the documentation of AIJ for details on the latter),
     the generated Java code follows a different strategy,
     in order to realize the required non-strictness.
     This strategy involves generating Java local variables
     to store results of arguments of non-strict ACL2 functions.
     The base name to use for these variables
     is an argument of these code generation functions."))
  :verify-guards nil

  (define atj-gen-shallow-aifapp ((atest pseudo-termp)
                                  (athen pseudo-termp)
                                  (aelse pseudo-termp)
                                  (jvar-names symbol-string-alistp)
                                  (jvar-indices symbol-nat-alistp)
                                  (jvar-value-base stringp)
                                  (jvar-value-index posp)
                                  (jvar-result-base stringp)
                                  (jvar-result-index posp)
                                  (curr-pkg stringp)
                                  (avars-by-name string-symbols-alistp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Generate a shallowly embedded ACL2 @(tsee if) application."
    :long
    (xdoc::topstring
     (xdoc::p
      "Consider a call @('(if a b c)').
       If the Java code generated for @('a')
       consists of the block @('<a-block>') and expression @('<a-expr>'),
       and similarly for @('b') and @('c'),
       we generate the Java block")
     (xdoc::codeblock
      "<a-blocks>"
      "Acl2Value <result> = null;"
      "if (Acl2Symbol.NIL.equals(<a-expr>)) {"
      "    <c-blocks>"
      "    <result> = <c-expr>;"
      "} else {"
      "    <b-blocks>"
      "    <result> = <b-expr>;"
      "}")
     (xdoc::p
      "and the Java expression @('<result>'),
       where @('<result>') consists of
       the base name in the parameter @('jvar-result-base')
       followed by a numeric index.")
     (xdoc::p
      "In other words, we first compute the test
       and create a local variable to store the final result.
       Based on the test, we execute either branch (for non-strictness),
       storing the result into the variable."))
    (b* (((mv test-jblock
              test-jexpr
              jvar-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm atest
                                                        jvar-names
                                                        jvar-indices
                                                        jvar-value-base
                                                        jvar-value-index
                                                        jvar-result-base
                                                        jvar-result-index
                                                        curr-pkg
                                                        avars-by-name))
         ((mv result-locvar-jblock jvar-result jvar-result-index)
          (atj-gen-jlocvar-indexed *atj-jtype-value*
                                   jvar-result-base
                                   jvar-result-index
                                   (jexpr-literal-null)))
         ((mv else-jblock
              else-jexpr
              jvar-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm aelse
                                                        jvar-names
                                                        jvar-indices
                                                        jvar-value-base
                                                        jvar-value-index
                                                        jvar-result-base
                                                        jvar-result-index
                                                        curr-pkg
                                                        avars-by-name))
         (else-jblock (append else-jblock
                              (jblock-asg-name jvar-result else-jexpr)))
         ((mv then-jblock
              then-jexpr
              jvar-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm athen
                                                        jvar-names
                                                        jvar-indices
                                                        jvar-value-base
                                                        jvar-value-index
                                                        jvar-result-base
                                                        jvar-result-index
                                                        curr-pkg
                                                        avars-by-name))
         (then-jblock (append then-jblock
                              (jblock-asg-name jvar-result then-jexpr)))
         (if-jblock (jblock-ifelse
                     (jexpr-imethod (jexpr-name "Acl2Symbol.NIL")
                                    "equals"
                                    (list test-jexpr))
                     else-jblock
                     then-jblock))
         (jblock (append test-jblock
                         result-locvar-jblock
                         if-jblock))
         (jexpr (jexpr-name jvar-result)))
      (mv jblock
          jexpr
          jvar-indices
          jvar-value-index
          jvar-result-index))
    ;; 2nd component is non-0
    ;; so that each call of ATJ-GEN-SHALLOW-ATERM decreases
    ;; even when the ACL2-COUNTs of the other two addends are 0:
    :measure (two-nats-measure (+ (acl2-count atest)
                                  (acl2-count athen)
                                  (acl2-count aelse))
                               1))

  (define atj-gen-shallow-aorapp ((afirst pseudo-termp)
                                  (asecond pseudo-termp)
                                  (jvar-names symbol-string-alistp)
                                  (jvar-indices symbol-nat-alistp)
                                  (jvar-value-base stringp)
                                  (jvar-value-index posp)
                                  (jvar-result-base stringp)
                                  (jvar-result-index posp)
                                  (curr-pkg stringp)
                                  (avars-by-name string-symbols-alistp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Generate a shallowly embedded ACL2 @('or') application."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is for the @('or') ACL2 ``pseudo-function''
       (see the AIJ documentation for details).
       We treat @('(or a b)') non-strictly like @('(if a a b)'),
       but we avoid calculating @('a') twice.
       Similarly to how we treat @(tsee if),
       we generate the Java block")
     (xdoc::codeblock
      "<a-blocks>"
      "Acl2Value <result> = null;"
      "if (Acl2Symbol.NIL.equals(<a-expr>)) {"
      "    <b-blocks>"
      "    <result> = <b-expr>;"
      "} else {"
      "    <result> = <a-expr>;"
      "}")
     (xdoc::p
      "and the Java expression @('<result>')."))
    (b* (((mv first-jblock
              first-jexpr
              jvar-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm afirst
                                                        jvar-names
                                                        jvar-indices
                                                        jvar-value-base
                                                        jvar-value-index
                                                        jvar-result-base
                                                        jvar-result-index
                                                        curr-pkg
                                                        avars-by-name))
         ((mv result-locvar-jblock jvar-result jvar-result-index)
          (atj-gen-jlocvar-indexed *atj-jtype-value*
                                   jvar-result-base
                                   jvar-result-index
                                   (jexpr-literal-null)))
         ((mv second-jblock
              second-jexpr
              jvar-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm asecond
                                                        jvar-names
                                                        jvar-indices
                                                        jvar-value-base
                                                        jvar-value-index
                                                        jvar-result-base
                                                        jvar-result-index
                                                        curr-pkg
                                                        avars-by-name))
         (second-jblock (append second-jblock
                                (jblock-asg-name jvar-result second-jexpr)))
         (first-jblock-asg (jblock-asg-name jvar-result first-jexpr))
         (if-jblock (jblock-ifelse
                      (jexpr-imethod (jexpr-name "Acl2Symbol.NIL")
                                     "equals"
                                     (list first-jexpr))
                      second-jblock
                      first-jblock-asg))
         (jblock (append first-jblock
                         result-locvar-jblock
                         if-jblock))
         (jexpr (jexpr-name jvar-result)))
      (mv jblock
          jexpr
          jvar-indices
          jvar-value-index
          jvar-result-index))
    ;; 2nd component is non-0
    ;; so that each call of ATJ-GEN-SHALLOW-ATERM decreases
    ;; even when the ACL2-COUNT of the other addend is 0:
    :measure (two-nats-measure (+ (acl2-count afirst)
                                  (acl2-count asecond))
                               1))

  (define atj-gen-shallow-afnapp ((afn pseudo-termfnp)
                                  (aargs pseudo-term-listp)
                                  (jvar-names symbol-string-alistp)
                                  (jvar-indices symbol-nat-alistp)
                                  (jvar-value-base stringp)
                                  (jvar-value-index posp)
                                  (jvar-result-base stringp)
                                  (jvar-result-index posp)
                                  (curr-pkg stringp)
                                  (avars-by-name string-symbols-alistp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Generate a shallowly embedded ACL2 function application."
    :long
    (xdoc::topstring
     (xdoc::topstring
      "Terms of the form @('(if a a b)') are treated as @('(or a b)'),
       via @(tsee atj-gen-shallow-aorapp), non-strictly.
       Other @(tsee if) calls are handled by @(tsee atj-gen-shallow-aifapp).")
     (xdoc::p
      "For calls of other ACL2 named functions, which are strict,
       we generate Java code to compute all the actual arguments,
       and we generate a call of the method that corresponds to
       the ACL2 function.
       We treat the abstract syntax somewhat improperly here,
       by using a generic method call with a possibly qualified method name,
       which should be therefore a static method call;
       this still produces correct Java code,
       but it should be handled more properly
       in a future version of this implementation.")
     (xdoc::p
      "For calls of an ACL2 lambda expression,
       we also compute all the actual arguments
       (lambda expressions are strict too),
       and then use a separate code generation function
       for the lambda expression (applied to the computed arguments)."))
    (b* (((when (and (eq afn 'if)
                     (= (len aargs) 3)))
          (b* ((afirst (first aargs))
               (asecond (second aargs))
               (athird (third aargs)))
            (if (equal afirst asecond)
                (atj-gen-shallow-aorapp afirst
                                        athird
                                        jvar-names
                                        jvar-indices
                                        jvar-value-base
                                        jvar-value-index
                                        jvar-result-base
                                        jvar-result-index
                                        curr-pkg
                                        avars-by-name)
              (atj-gen-shallow-aifapp afirst
                                      asecond
                                      athird
                                      jvar-names
                                      jvar-indices
                                      jvar-value-base
                                      jvar-value-index
                                      jvar-result-base
                                      jvar-result-index
                                      curr-pkg
                                      avars-by-name))))
         ((mv args-jblock
              arg-jexprs
              jvar-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterms aargs
                                                         jvar-names
                                                         jvar-indices
                                                         jvar-value-base
                                                         jvar-value-index
                                                         jvar-result-base
                                                         jvar-result-index
                                                         curr-pkg
                                                         avars-by-name))
         ((when (symbolp afn))
          (mv args-jblock
              (jexpr-method (atj-gen-shallow-afnname afn curr-pkg)
                            arg-jexprs)
              jvar-indices
              jvar-value-index
              jvar-result-index))
         ((mv lambda-jblock
              lambda-jexpr
              jvar-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-alambda (lambda-formals afn)
                                                          (lambda-body afn)
                                                          aargs
                                                          arg-jexprs
                                                          jvar-names
                                                          jvar-indices
                                                          jvar-value-base
                                                          jvar-value-index
                                                          jvar-result-base
                                                          jvar-result-index
                                                          curr-pkg
                                                          avars-by-name))
         (jblock (append args-jblock
                         lambda-jblock))
         (jexpr lambda-jexpr))
      (mv jblock
          jexpr
          jvar-indices
          jvar-value-index
          jvar-result-index))
    ;; 2nd component is greater than the one of ATJ-GEN-SHALLOW-ALAMBDA
    ;; so that the call of ATJ-GEN-SHALLOW-ALAMBDA decreases
    ;; even when AFN is a non-symbol atom (impossible under the guard):
    :measure (two-nats-measure (+ (acl2-count afn)
                                  (acl2-count aargs))
                               2))

  (define atj-gen-shallow-alambda ((aformals symbol-listp)
                                   (abody pseudo-termp)
                                   (aargs pseudo-term-listp)
                                   (jargs jexpr-listp)
                                   (jvar-names symbol-string-alistp)
                                   (jvar-indices symbol-nat-alistp)
                                   (jvar-value-base stringp)
                                   (jvar-value-index posp)
                                   (jvar-result-base stringp)
                                   (jvar-result-index posp)
                                   (curr-pkg stringp)
                                   (avars-by-name string-symbols-alistp))
    :guard (and (= (len aargs) (len aformals))
                (= (len jargs) (len aformals)))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Generate a shallowly embedded ACL2 lambda expression,
            applied to given Java expressions as arguments."
    :long
    (xdoc::topstring
     (xdoc::p
      "Since a lambda expression introduces new ACL2 variables,
       we first generate new Java local variables
       for the ACL2 variables that form the formal parameters,
       producing a new @('jvar-names') alist
       and updating the @('jvar-indices') alist.")
     (xdoc::p
      "ACL2 lambda expressions are always closed,
       which means that often they include formal parameters
       that are replaced by themselves (i.e. by the same symbols)
       when the lambda expression is applied.
       For instance, the untranslated term @('(let ((x 0)) (+ x y))')
       is @('((lambda (x y) (binary-+ x y)) '3 y)') in translated form:
       the lambda expression includes the extra formal parameter @('y')
       (which is not bound by the @(tsee let)),
       applied to @('y') itself,
       making the lambda expression closed.
       To avoid generating an extra Java local variable
       for these additional formal parameters of lambda expressions
       (e.g. to avoid generating a Java local variable
       for the formal parameter @('y') in the example above,
       given that one must already be in scope
       for the @(tsee let) term to make sense),
       we remove for consideration all the formal parameters
       that are replaced by themselves when the lambda expression is applied.
       We do that by looking at
       the actual arguments @('aargs') of the lambda expression;
       this is why @('aargs') is passed to this code generation function.")
     (xdoc::p
      "Since we only generate new Java local variables
       for the lambda expression's formal parameters
       that are not dropped as just explained,
       in general we need to keep the Java local variables
       associated to the dropped formal parameters.
       We do that by simply appending the new @('jvar-names')
       in front of the old one, achieving the desired ``overwriting''.")
     (xdoc::p
      "After generating the needed Java local variables,
       we assign to them the Java expressions for the actual arguments,
       as in @(tsee let) bindings.")
     (xdoc::p
      "Finally, we generate Java code
       for the body of the lambda expression."))
    (b* ((aformals (remove-unneeded-lambda-formals aformals aargs))
         ((mv new-jvar-names
              jvar-indices) (atj-gen-shallow-avars aformals
                                                   jvar-indices
                                                   curr-pkg
                                                   avars-by-name))
         (jvar-names (append new-jvar-names jvar-names))
         (let-jblock (atj-gen-shallow-let-bindings aformals
                                                   jargs
                                                   jvar-names))
         ((mv body-jblock
              body-jexpr
              jvar-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm abody
                                                        jvar-names
                                                        jvar-indices
                                                        jvar-value-base
                                                        jvar-value-index
                                                        jvar-result-base
                                                        jvar-result-index
                                                        curr-pkg
                                                        avars-by-name)))
      (mv (append let-jblock body-jblock)
          body-jexpr
          jvar-indices
          jvar-value-index
          jvar-result-index))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-SHALLOW-ATERM decreases:
    :measure (two-nats-measure (acl2-count abody) 1))

  (define atj-gen-shallow-aterm ((aterm pseudo-termp)
                                 (jvar-names symbol-string-alistp)
                                 (jvar-indices symbol-nat-alistp)
                                 (jvar-value-base stringp)
                                 (jvar-value-index posp)
                                 (jvar-result-base stringp)
                                 (jvar-result-index posp)
                                 (curr-pkg stringp)
                                 (avars-by-name string-symbols-alistp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Generate a shallowly embedded ACL2 term."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the ACL2 term is a variable,
       it must be in the @('jvar') alist,
       so we just look it up there.")
     (xdoc::p
      "If the ACL2 term is a quoted constant,
       we represent it as its value."))
    (cond ((variablep aterm) (mv nil
                                 (jexpr-name (cdr (assoc-eq aterm jvar-names)))
                                 jvar-indices
                                 jvar-value-index
                                 jvar-result-index))
          ((fquotep aterm) (b* (((mv jblock jexpr jvar-value-index)
                                 (atj-gen-avalue (unquote aterm)
                                                 jvar-value-base
                                                 jvar-value-index)))
                             (mv jblock
                                 jexpr
                                 jvar-indices
                                 jvar-value-index
                                 jvar-result-index)))
          (t (atj-gen-shallow-afnapp (ffn-symb aterm)
                                     (fargs aterm)
                                     jvar-names
                                     jvar-indices
                                     jvar-value-base
                                     jvar-value-index
                                     jvar-result-base
                                     jvar-result-index
                                     curr-pkg
                                     avars-by-name)))
    :measure (two-nats-measure (acl2-count aterm) 0))

  (define atj-gen-shallow-aterms ((aterms pseudo-term-listp)
                                  (jvar-names symbol-string-alistp)
                                  (jvar-indices symbol-nat-alistp)
                                  (jvar-value-base stringp)
                                  (jvar-value-index posp)
                                  (jvar-result-base stringp)
                                  (jvar-result-index posp)
                                  (curr-pkg stringp)
                                  (avars-by-name string-symbols-alistp))
    :returns (mv (jblock jblockp)
                 (jexpr jexpr-listp)
                 (new-jvar-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Lift @(tsee atj-gen-shallow-aterm) to lists."
    (if (endp aterms)
        (mv nil nil jvar-indices jvar-value-index jvar-result-index)
      (b* (((mv first-jblock
                first-jexpr
                jvar-indices
                jvar-value-index
                jvar-result-index) (atj-gen-shallow-aterm (car aterms)
                                                          jvar-names
                                                          jvar-indices
                                                          jvar-value-base
                                                          jvar-value-index
                                                          jvar-result-base
                                                          jvar-result-index
                                                          curr-pkg
                                                          avars-by-name))
           ((mv rest-jblock
                rest-jexprs
                jvar-indices
                jvar-value-index
                jvar-result-index) (atj-gen-shallow-aterms (cdr aterms)
                                                           jvar-names
                                                           jvar-indices
                                                           jvar-value-base
                                                           jvar-value-index
                                                           jvar-result-base
                                                           jvar-result-index
                                                           curr-pkg
                                                           avars-by-name)))
        (mv (append first-jblock rest-jblock)
            (cons first-jexpr rest-jexprs)
            jvar-indices
            jvar-value-index
            jvar-result-index)))
    :measure (two-nats-measure (acl2-count aterms) 0)))

(define atj-gen-apkg-jmethod-name ((apkg stringp))
  :returns (jmethod-name stringp)
  :short "Name of the Java method that adds an ACL2 package definition."
  :long
  (xdoc::topstring-p
   "We generate a private static method
    for each ACL2 package definition to build.
    This function generates the name of this method,
    which should be distinct from all the other methods
    generated for the same class.")
  (str::cat "$addPackageDef_"
            (implode (atj-achars-to-jchars-id (explode apkg) nil nil))))

(define atj-gen-apkg-name ((apkg stringp))
  :returns (expr jexprp)
  :short "Generate Java code to build an ACL2 package name."
  :long
  (xdoc::topstring-p
   "Note that package names
    can always be safely generated as Java string literals.")
  (jexpr-smethod *atj-jtype-pkg-name*
                 "make"
                 (list (atj-gen-jstring apkg))))

(define atj-gen-apkg-jmethod ((apkg stringp) (verbose$ booleanp))
  :returns (jmethod jmethodp)
  :short "Generate a Java method that adds an ACL2 package definition."
  :long
  (xdoc::topstring-p
   "This is a private static method
    that contains a sequence of statements
    to incrementally construct
    the Java list of symbols imported by the package.
    The sequence starts with a declaration of a local variable
    initialized with an empty Java list
    whose capacity is the length of the import list.
    After all the assignments, we generate a method call
    to add the ACL2 package definition with the calculated import list.")
  (b* (((run-when verbose$)
        (cw "  ~s0~%" apkg))
       (jvar-aimports "imports")
       (jmethod-name (atj-gen-apkg-jmethod-name apkg))
       (aimports (pkg-imports apkg))
       (len-jexpr (jexpr-literal-integer-decimal (len aimports)))
       (newlist-jexpr (jexpr-newclass (jtype-class "ArrayList<>")
                                      (list len-jexpr)))
       (imports-jblock (jblock-locvar (jtype-class "List<Acl2Symbol>")
                                      jvar-aimports
                                      newlist-jexpr))
       (imports-jblock (append imports-jblock
                               (atj-gen-apkg-jmethod-aux aimports
                                                         jvar-aimports)))
       (apkg-name-jexpr (atj-gen-apkg-name apkg))
       (defpkg-jblock (jblock-smethod *atj-jtype-pkg*
                                      "define"
                                      (list apkg-name-jexpr
                                            (jexpr-name jvar-aimports))))
       (jmethod-body (append imports-jblock
                             defpkg-jblock)))
    (make-jmethod :access (jaccess-private)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-void)
                  :name jmethod-name
                  :params nil
                  :throws nil
                  :body jmethod-body))

  :prepwork
  ((define atj-gen-apkg-jmethod-aux ((imports symbol-listp)
                                     (jvar-aimports stringp))
     :returns (jblock jblockp)
     :parents nil
     (cond ((endp imports) nil)
           (t (b* ((import-jexpr (atj-gen-asymbol (car imports)))
                   (first-jblock (jblock-imethod (jexpr-name jvar-aimports)
                                                 "add"
                                                 (list import-jexpr)))
                   (rest-jblock (atj-gen-apkg-jmethod-aux (cdr imports)
                                                          jvar-aimports)))
                (append first-jblock rest-jblock)))))))

(define atj-gen-apkg-jmethods ((apkgs string-listp) (verbose$ booleanp))
  :returns (jmethods jmethod-listp)
  :short "Generate all the Java methods that add the ACL2 package definitions."
  (if (endp apkgs)
      nil
    (b* ((first-jmethod (atj-gen-apkg-jmethod (car apkgs) verbose$))
         (rest-jmethods (atj-gen-apkg-jmethods (cdr apkgs) verbose$)))
      (cons first-jmethod rest-jmethods))))

(define atj-gen-apkgs ((apkgs string-listp))
  :returns (jblock jblockp)
  :short "Generate Java code to build the ACL2 packages."
  :long
  (xdoc::topstring-p
   "This is a sequence of calls to the methods
    generated by @(tsee atj-gen-apkg-jmethods).
    These calls are part of the code that
    initializes (the Java representation of) the ACL2 environment.")
  (if (endp apkgs)
      nil
    (b* ((jmethod-name (atj-gen-apkg-jmethod-name (car apkgs)))
         (first-jblock (jblock-method jmethod-name nil))
         (rest-jblock (atj-gen-apkgs (cdr apkgs))))
      (append first-jblock rest-jblock))))

(define atj-gen-apkg-witness ()
  :returns (jblock jblockp)
  :short "Generate Java code to set the name of the ACL2 package witness."
  :long
  (xdoc::topstring-p
   "This is a statement that is part of
    initializing (the Java representation of) the ACL2 environment.")
  (jblock-smethod *atj-jtype-pkg*
                  "setWitnessName"
                  (list (atj-gen-jstring *pkg-witness-name*))))

(define atj-gen-deep-afndef-jmethod-name ((afn symbolp))
  :returns (method-name stringp)
  :short "Name of the Java method that builds
          a deeply embedded ACL2 function definition."
  :long
  (xdoc::topstring-p
   "We generate a private static method
    for each deeply embedded ACL2 function definition to build.
    This function generates the name of this method,
    which should be distinct from all the other methods
    generated for the same class.")
  (str::cat
   "$addFunctionDef_"
   (implode (atj-achars-to-jchars-id (explode
                                      (symbol-package-name afn)) nil nil))
   "$$$"
   (implode (atj-achars-to-jchars-id (explode (symbol-name afn)) nil t))))

(define atj-gen-deep-afndef-jmethod ((afn symbolp)
                                     (guards$ booleanp)
                                     (verbose$ booleanp)
                                     state)
  :returns (jmethod jmethodp)
  :verify-guards nil
  :short "Generate a Java method that builds
          a deeply embedded ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a private static method
     that contains a sequence of statements to
     store the function's name into a local variable,
     store an array of the function's formal arguments into a local variable,
     store the function's body into a local variable,
     and use these local variables to add the function's definition.")
   (xdoc::p
    "The indices of the local variables
     to build values, terms, and lambda expressions
     are all reset to 1,
     because each function definition is built in its own method
     (thus, there are no cross-references).")
   (xdoc::p
    "All the calls of @(tsee mbe) are replaced with
     their @(':logic') or @(':exec') parts (based on @(':guards'))
     in the function's body,
     prior to generating code."))
  (b* (((run-when verbose$)
        (cw "  ~s0~%" afn))
       (jmethod-name (atj-gen-deep-afndef-jmethod-name afn))
       (jvar-function "function")
       (jvar-formals "formals")
       (jvar-body "body")
       (aformals (formals afn (w state)))
       (abody (getpropc afn 'unnormalized-body))
       (abody (if guards$
                  (remove-mbe-logic-from-term abody)
                (remove-mbe-exec-from-term abody)))
       (afn-jblock (jblock-locvar *atj-jtype-named-fn*
                                  jvar-function
                                  (jexpr-smethod *atj-jtype-named-fn*
                                                 "make"
                                                 (list (atj-gen-asymbol afn)))))
       (aformals-jblock (jblock-locvar (jtype-array *atj-jtype-symbol*)
                                       jvar-formals
                                       (atj-gen-deep-aformals aformals)))
       ((mv abody-jblock
            abody-jexpr
            & & &) (atj-gen-deep-aterm abody "value" 1 "term" 1 "lambda" 1))
       (abody-jblock (append abody-jblock
                             (jblock-locvar *atj-jtype-term*
                                            jvar-body
                                            abody-jexpr)))
       (def-jblock (jblock-imethod (jexpr-name jvar-function)
                                   "define"
                                   (list (jexpr-name jvar-formals)
                                         (jexpr-name jvar-body))))
       (jmethod-body (append afn-jblock
                             aformals-jblock
                             abody-jblock
                             def-jblock)))
    (make-jmethod :access (jaccess-private)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-void)
                  :name jmethod-name
                  :params nil
                  :throws nil
                  :body jmethod-body)))

(define atj-gen-deep-afndef-jmethods ((afns symbol-listp)
                                      (guards$ booleanp)
                                      (verbose$ booleanp)
                                      state)
  :returns (jmethods jmethod-listp)
  :verify-guards nil
  :short "Generate all the Java methods that build
          the deeply embedded ACL2 function definitions."
  (if (endp afns)
      nil
    (b* ((first-jmethod
          (atj-gen-deep-afndef-jmethod (car afns) guards$ verbose$ state))
         (rest-jmethods
          (atj-gen-deep-afndef-jmethods (cdr afns) guards$ verbose$ state)))
      (cons first-jmethod rest-jmethods))))

(define atj-gen-deep-afndefs ((afns symbol-listp))
  :returns (jblock jblockp)
  :short "Generate Java code to build
          the deeply embedded ACL2 function definitions."
  :long
  (xdoc::topstring-p
   "This is a sequence of calls to the methods
    generated by @(tsee atj-gen-deep-afndef-jmethods).
    These calls are part of the code that
    initializes (the Java representation of) the ACL2 environment.")
  (if (endp afns)
      nil
    (b* ((jmethod-name (atj-gen-deep-afndef-jmethod-name (car afns)))
         (first-jblock (jblock-method jmethod-name nil))
         (rest-jblock (atj-gen-deep-afndefs (cdr afns))))
      (append first-jblock rest-jblock))))

(define atj-gen-shallow-afnprimitive ((afn symbolp) (curr-pkg stringp))
  :guard (and (primitivep afn)
              (equal (symbol-package-name afn) curr-pkg))
  :returns (jmethod jmethodp)
  :short "Generate a shallowly embedded ACL2 primitive function."
  :long
  (xdoc::topstring
   (xdoc::p
    "AIJ's @('Acl2NativeFunction') class provides native Java implementations
     of the ACL2 primitive functions, as public static Java methods.
     Thus, in the shallow embedding approach,
     we could translate each reference to an ACL2 primitive function
     to the names of those public static Java methods.
     However, for greater uniformity,
     we generate Java methods for the ACL2 primitive functions
     whose names are constructed in the same way as
     the Java methods for the non-primitive ACL2 functions,
     and that reside in the Java classes generated for
     the @('\"COMMON-LISP\"') and @('\"ACL2\"') ACL2 packages.
     These Java methods for the ACL2 primitive functions
     simply call the aforementioned public methods."))
  (b* ((jcall-method-name
        (case afn
          (characterp "execCharacterp")
          (stringp "execStringp")
          (symbolp "execSymbolp")
          (integerp "execIntegerp")
          (rationalp "execRationalp")
          (complex-rationalp "execComplexRationalp")
          (acl2-numberp "execAcl2Numberp")
          (consp "execConsp")
          (char-code "execCharCode")
          (code-char "execCodeChar")
          (coerce "execCoerce")
          (intern-in-package-of-symbol "execInternInPackageOfSymbol")
          (symbol-package-name "execSymbolPackageName")
          (symbol-name "execSymbolName")
          (pkg-imports "execPkgImports")
          (pkg-witness "execPkgWitness")
          (unary-- "execUnaryMinus")
          (unary-/ "execUnarySlash")
          (binary-+ "execBinaryPlus")
          (binary-* "execBinaryStar")
          (< "execLessThan")
          (complex "execComplex")
          (realpart "execRealPart")
          (imagpart "execImagPart")
          (numerator "execNumerator")
          (denominator "execDenominator")
          (cons "execCons")
          (car "execCar")
          (cdr "execCdr")
          (equal "execEqual")
          (bad-atom<= "execBadAtomLessThanOrEqualTo")
          (if "execIf")
          (t (impossible))))
       (jcall-arg-names
        (case afn
          (intern-in-package-of-symbol (list "str" "sym"))
          (if (list "x" "y" "z"))
          ((pkg-imports
            pkg-witness) (list "pkg"))
          ((coerce
            binary-+
            binary-*
            <
            complex
            cons
            equal
            bad-atom<=) (list "x" "y"))
          (t (list "x"))))
       (jcall (jexpr-smethod *atj-jtype-native-fn*
                             jcall-method-name
                             (jexpr-name-list jcall-arg-names)))
       (jmethod-name (atj-gen-shallow-afnname afn curr-pkg))
       (jmethod-params (atj-gen-jparamlist-avalues jcall-arg-names))
       (jmethod-body (jblock-return jcall)))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type *atj-jtype-value*)
                  :name jmethod-name
                  :params jmethod-params
                  :throws (list *atj-jclass-eval-exc*)
                  :body jmethod-body))
  :guard-hints (("Goal" :in-theory (enable primitivep))))

(define atj-gen-shallow-afndef ((afn symbolp)
                                (guards$ booleanp)
                                (verbose$ booleanp)
                                (curr-pkg stringp)
                                state)
  :guard (equal (symbol-package-name afn) curr-pkg)
  :returns (jmethod jmethodp)
  :verify-guards nil
  :short "Generate a shallowly embedded ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 function definition is turned into a Java method.
     This is a public static method
     with the same number of parameters as the ACL2 function,
     all of Java type @('Acl2Value'),
     and that returns a value of the same type.")
   (xdoc::p
    "We turn the ACL2 formal parameters
     into Java variables to use as the method parameters,
     starting with no indices for the variables,
     since we are at the top level of the generation of
     the shallowly embedded ACL2 terms and lambda expressions.
     Note that @(tsee atj-gen-shallow-avars) preserves the order,
     so its @(tsee strip-cdrs) consists of the Java parameters
     in the same order as the corresponding ACL2 parameters.")
   (xdoc::p
    "We turn the body of the ACL2 function
     into Java statements and a Java expression,
     which constitute the shallow embedding of the ACL2 function body;
     the indices for the Java local variables
     for constructing values and results are initialized to 1,
     since we are at the top level here.
     We use @('$value') and @('$resullt') as the base names
     for the Java local variables to build values and results,
     so that they do not conflict with each other
     or with the Java local variables generated from the ACL2 variables,
     none of which starts with a @('$') not followed by two hexadecimal digits.
     The body of the Java method consists of those Java statements,
     followed by a @('return') statement with that Java expression.")
   (xdoc::p
    "Prior to shallowly embedding the ACL2 function body,
     all the calls of @(tsee mbe) are replaced with
     their @(':logic') or @(':exec') parts (based on @(':guards'))
     in the function's body."))
  (b* (((run-when verbose$)
        (cw "  ~s0~%" afn))
       (jmethod-name (atj-gen-shallow-afnname afn curr-pkg))
       (aformals (formals afn (w state)))
       (abody (getpropc afn 'unnormalized-body))
       (abody (if guards$
                  (remove-mbe-logic-from-term abody)
                (remove-mbe-exec-from-term abody)))
       (avars (union-eq aformals (all-free/bound-vars abody)))
       (avars-by-name (organize-symbols-by-name avars))
       ((mv jvar-names
            jvar-indices) (atj-gen-shallow-avars
                           aformals nil curr-pkg avars-by-name))
       (jmethod-params (atj-gen-jparamlist-avalues (strip-cdrs jvar-names)))
       ((mv abody-jblock abody-jexpr & & &)
        (atj-gen-shallow-aterm abody
                               jvar-names
                               jvar-indices
                               "$value" 1
                               "$result" 1
                               curr-pkg
                               avars-by-name))
       (jmethod-body (append abody-jblock
                             (jblock-return abody-jexpr))))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type *atj-jtype-value*)
                  :name jmethod-name
                  :params jmethod-params
                  :throws (list *atj-jclass-eval-exc*)
                  :body jmethod-body)))

(define atj-gen-shallow-afn ((afn symbolp)
                             (guards$ booleanp)
                             (verbose$ booleanp)
                             (curr-pkg stringp)
                             state)
  :guard (equal (symbol-package-name afn) curr-pkg)
  :returns (jmethod jmethodp)
  :verify-guards nil
  :short "Generate a shallowly embedded
          ACL2 primitive function or function definition."
  (if (primitivep afn)
      (atj-gen-shallow-afnprimitive afn curr-pkg)
    (atj-gen-shallow-afndef afn guards$ verbose$ curr-pkg state)))

(define atj-gen-shallow-afns ((afns symbol-listp)
                              (guards$ booleanp)
                              (verbose$ booleanp)
                              (curr-pkg stringp)
                              state)
  :guard (equal (symbol-package-name-lst afns)
                (repeat (len afns) curr-pkg))
  :returns (jmethods jmethod-listp)
  :verify-guards nil
  :short "Lift @(tsee atj-gen-shallow-afn) to lists."
  (cond ((endp afns) nil)
        (t (b* ((first-jmethod (atj-gen-shallow-afn (car afns)
                                                    guards$
                                                    verbose$
                                                    curr-pkg
                                                    state))
                (rest-jmethods (atj-gen-shallow-afns (cdr afns)
                                                     guards$
                                                     verbose$
                                                     curr-pkg
                                                     state)))
             (cons first-jmethod rest-jmethods)))))

(define atj-gen-shallow-afns-in-apkg ((afns symbol-listp)
                                      (apkg stringp)
                                      (guards$ booleanp)
                                      (java-class$ stringp)
                                      (verbose$ booleanp)
                                      state)
  :guard (equal (symbol-package-name-lst afns)
                (repeat (len afns) apkg))
  :returns (jclass jclassp)
  :verify-guards nil
  :short "Generate the shallowly embedded ACL2 functions
          in an ACL2 package."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     we generate a Java class for each ACL2 package
     that includes ACL2 functions for which we generate Java code
     (each ACL2 function is turned into a Java method in this class).
     This is a public static Java class,
     nested into the main Java class that ATJ generates."))
  (b* ((jclass-name (atj-gen-shallow-apkgname apkg java-class$))
       (jclass-methods (atj-gen-shallow-afns afns guards$ verbose$ apkg state)))
    (make-jclass :access (jaccess-public)
                 :abstract? nil
                 :static? t
                 :final? nil
                 :strictfp? nil
                 :name jclass-name
                 :superclass? nil
                 :superinterfaces nil
                 :body (jmethods-to-jcmembers jclass-methods))))

(define atj-gen-shallow-afns-by-apkg ((afns-by-apkg string-symbols-alistp)
                                      (guards$ booleanp)
                                      (java-class$ stringp)
                                      (verbose$ booleanp)
                                      state)
  :returns (jclasses jclass-listp)
  :verify-guards nil
  :short "Generate shallowly embedded ACL2 functions, by ACL2 packages."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through each pair in the alist
     from ACL2 package names to ACL2 functions,
     and generate all the Java classes corresponding to the ACL2 packages."))
  (b* ((apkgs (remove-duplicates-equal (strip-cars afns-by-apkg))))
    (atj-gen-shallow-afns-by-apkg-aux
     apkgs afns-by-apkg guards$ java-class$ verbose$ state))

  :prepwork
  ((define atj-gen-shallow-afns-by-apkg-aux
     ((apkgs string-listp)
      (afns-by-apkg string-symbols-alistp)
      (guards$ booleanp)
      (java-class$ stringp)
      (verbose$ booleanp)
      state)
     :returns (jclasses jclass-listp)
     :verify-guards nil
     (cond ((endp apkgs) nil)
           (t (b* ((apkg (car apkgs))
                   (afns (cdr (assoc-equal apkg afns-by-apkg)))
                   (first-jclass (atj-gen-shallow-afns-in-apkg
                                  afns apkg guards$ java-class$ verbose$ state))
                   (rest-jclasses (atj-gen-shallow-afns-by-apkg-aux (cdr apkgs)
                                                                    afns-by-apkg
                                                                    guards$
                                                                    java-class$
                                                                    verbose$
                                                                    state)))
                (cons first-jclass rest-jclasses)))))))

(define atj-gen-init-jmethod ((apkgs string-listp)
                              (afns symbol-listp)
                              (deep$ booleanp))
  :returns (jmethod jmethodp)
  :short "Generate the Java public method to initialize the ACL2 environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a public static method,
     which must be called before calling the method to call ACL2 functions,
     and also before calling the AIJ methods
     to translate between Java and ACL2 values.")
   (xdoc::p
    "If the initialization flag is cleared,
     the initialization is performed and the flag is set.
     Otherwise, an exception is thrown,
     because initialization must occur only once.")
   (xdoc::p
    "If @(':deep') is @('t'), we generate code
     to build the deeply embedded representations of the ACL2 functions.
     Otherwise, we skip this step.
     The representations of the ACL2 packages are needed for
     both deep and shallow embedding.")
   (xdoc::p
    "If @(':deep') is @('t'), we generate code
     to validate the definitions of all the deeply embedded ACL2 functions.
     Otherwise, we skip this step."))
  (b* ((exception-message "The ACL2 environment is already initialized.")
       (exception-message-jexpr (atj-gen-jstring exception-message))
       (throw-jblock (jblock-throw (jexpr-newclass
                                    (jtype-class "IllegalStateException")
                                    (list exception-message-jexpr))))
       (if-jblock (jblock-if (jexpr-name "initialized")
                             throw-jblock))
       (apkgs-jblock (atj-gen-apkgs apkgs))
       (apkg-witness-jblock (atj-gen-apkg-witness))
       (afns-jblock? (if deep$
                         (atj-gen-deep-afndefs afns)
                       nil))
       (validate-jblock (and deep$
                             (jblock-smethod *atj-jtype-named-fn*
                                             "validateAll"
                                             nil)))
       (initialize-jblock (jblock-asg-name "initialized"
                                           (jexpr-literal-true)))
       (jmethod-body (append if-jblock
                             apkgs-jblock
                             apkg-witness-jblock
                             afns-jblock?
                             validate-jblock
                             initialize-jblock)))
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
                  :body jmethod-body)))

(define atj-gen-init-jfield ()
  :returns (jfield jfieldp)
  :short "Generate the Java field for the initialization flag."
  :long
  (xdoc::topstring-p
   "This is a private static field that is initially cleared,
    indicating that the ACL2 environment has not been initialized yet.
    The flag is set when the ACL2 environment is initialized,
    and checked to avoid re-initializing the ACL2 environment again.")
  (make-jfield :access (jaccess-private)
               :static? t
               :final? nil
               :transient? nil
               :volatile? nil
               :type (jtype-boolean)
               :name "initialized"
               :init (jexpr-literal-false)))

(define atj-gen-call-jmethod ()
  :returns (jmethod jmethodp)
  :short "Generate the Java method to call ACL2 functions,
          in the deep embedding approach."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a public static method,
     which provides the means for external Java code to call
     the deeply embedded Java representations of ACL2 functions."))
  (b* ((jmethod-param-function (make-jparam :final? nil
                                            :type *atj-jtype-symbol*
                                            :name "function"))
       (jmethod-param-arguments (make-jparam :final? nil
                                             :type (jtype-array
                                                    *atj-jtype-value*)
                                             :name "arguments"))
       (jmethod-params (list jmethod-param-function
                             jmethod-param-arguments))
       (exception-message "The ACL2 environment is not initialized.")
       (exception-message-jexpr (atj-gen-jstring exception-message))
       (throw-jblock (jblock-throw (jexpr-newclass
                                    (jtype-class "IllegalStateException")
                                    (list exception-message-jexpr))))
       (if-jblock (jblock-if (jexpr-unary (junop-logcompl)
                                          (jexpr-name "initialized"))
                             throw-jblock))
       (function-jexpr (jexpr-smethod *atj-jtype-named-fn*
                                      "make"
                                      (list (jexpr-name "function"))))
       (call-jexpr (jexpr-imethod function-jexpr
                                  "call"
                                  (list (jexpr-name "arguments"))))
       (return-jblock (jblock-return call-jexpr))
       (jmethod-body (append if-jblock
                             return-jblock)))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type *atj-jtype-value*)
                  :name "call"
                  :params jmethod-params
                  :throws (list *atj-jclass-eval-exc*)
                  :body jmethod-body)))

(define atj-gen-jclass ((apkgs string-listp)
                        (afns symbol-listp)
                        (deep$ booleanp)
                        (guards$ booleanp)
                        (java-class$ stringp)
                        (verbose$ booleanp)
                        state)
  :returns (jclass jclassp)
  :verify-guards nil
  :short "Generate the main (i.e. non-test) Java class declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a public class that contains all the generated members.
     [JLS] says that a Java implementation may require
     public classes to be in files with the same names (plus extension).
     The code that we generate satisfies this requirement.")
   (xdoc::p
    "If @(':deep') is @('t'), we generate the Java methods
     to build the deeply embedded ACL2 functions
     and the @('call') method.
     If @(':deep') is @('nil'), we generate the Java classes and methods
     for the shallowly embedded ACL2 functions,
     and no @('call') method.
     In the latter case, we ensure that the ACL2 primitives are included,
     we organize the resulting functions by packages,
     and we proceed to generate the Java nested classes and methods."))
  (b* ((init-jfield (atj-gen-init-jfield))
       ((run-when verbose$)
        (cw "~%Generating Java code for the ACL2 packages:~%"))
       (apkg-jmethods (atj-gen-apkg-jmethods apkgs verbose$))
       ((run-when verbose$)
        (cw "~%Generating Java code for the ACL2 functions:~%"))
       (afn-jmembers
        (if deep$
            (jmethods-to-jcmembers
             (atj-gen-deep-afndef-jmethods afns guards$ verbose$ state))
          (b* ((afns+primitives
                (remove-duplicates-eq
                 (append afns
                         (strip-cars *primitive-formals-and-guards*))))
               (afns-by-apkg (organize-symbols-by-pkg afns+primitives)))
            (jclasses-to-jcmembers
             (atj-gen-shallow-afns-by-apkg afns-by-apkg
                                           guards$
                                           java-class$
                                           verbose$
                                           state)))))
       (init-jmethod (atj-gen-init-jmethod apkgs afns deep$))
       (call-jmethod? (and deep$
                           (list (atj-gen-call-jmethod))))
       (body-jclass (append (list (jcmember-field init-jfield))
                            (jmethods-to-jcmembers apkg-jmethods)
                            afn-jmembers
                            (list (jcmember-method init-jmethod))
                            (jmethods-to-jcmembers call-jmethod?))))
    (make-jclass :access (jaccess-public)
                 :abstract? nil
                 :static? nil
                 :final? nil
                 :strictfp? nil
                 :name java-class$
                 :superclass? nil
                 :superinterfaces nil
                 :body body-jclass)))

(define atj-gen-test-failures-jfield ()
  :returns (jfield jfieldp)
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
               :init (jexpr-literal-false)))

(define atj-gen-test-jmethod-name ((test-name stringp))
  :returns (jmethod-name stringp)
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

(define atj-gen-test-jmethod ((test$ atj-testp)
                              (deep$ booleanp)
                              (java-class$ stringp)
                              (verbose$ booleanp))
  :returns (jmethod jmethodp)
  :short "Generate a Java method to run one of the specified tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "This is a private static method
     that prints the name of the test,
     builds the argument values of the test using AIJ,
     builds the result value of the test using AIJ,
     calls (the Java representation of) the function on them,
     compares the obtained result value with the test's result value,
     and prints a message of success or failure.
     It also sets the failures field to true if the test fails.")
   (xdoc::p
    "This method also measures the time of the Java call,
     by taking the current time just before and just after the call,
     and subtracting them.
     It does that for the number of repetitions
     specified by the integer argument of the method.
     It stores the times of each call in an array,
     and calculates the minimum, maximum, and sum of all the times.
     At the end, it prints all the times,
     along with minimum, maximum, and average
     (where the average is obtained from the sum).
     To prevent unwanted JIT optimizations,
     a boolean flag is used to cumulatively check that
     all the repeated calls succeed
     (in the sense of computing the same result as ACL2);
     since the code is deterministic,
     we expect that either they will all succeed or they will all fail.
     We note that
     the reason for storing the argument values into local variables
     in the shallow embedding approach,
     as opposed to passing the expressions directly to the method call,
     is to accurately measure just the time of each call,
     without the time needed to compute the argument expressions.")
   (xdoc::p
    "As a special case, if the integer parameter of the method is 0,
     times are not collected, and no minimum/maximum/sum is calculated,
     and no time information is printed.
     We use a @('do') loop to ensure that at least one call is made,
     even when the parameter is 0.
     The two values are subtracted, and the time printed.
     The reason for storing the argument values into local variables
     in the shallow embedding approach,
     as opposed to passing the expressions directly to the method call,
     is to accurately measure just the time of the call,
     without the time needed to compute the argument expressions.")
   (xdoc::p
    "The code is slightly different based on whether
     we are using the deep or shallow embedding approach:")
   (xdoc::ul
    (xdoc::li
     "For the deep embedding,
      we build the name of the function to call,
      we put the argument values into an array,
      and we produce the Java result
      via the @('call') method generated by ATJ
      (which uses the AIJ interpreter).")
    (xdoc::li
     "For the shallow embedding,
      we put the argument values into local variables,
      and we just call the Java method that represents the ACL2 function
      on those local variables.
      Since this code is in a class that is different from
      any of the generated Java classes that correspond to ACL2 packages,
      the Java method to call must be always preceded by the class name:
      thus, we use the empty string as the current package name,
      which is guaranteed not to match any existing ACL2 package."))
   (xdoc::p
    "Examining any generated instance of this method
     should make the above documentation,
     and the implementation of this code generation function,
     much clearer."))
  (b* (((atj-test test) test$)
       ((run-when verbose$)
        (cw "  ~s0~%" test.name))
       (jmethod-name (atj-gen-test-jmethod-name test.name))
       ((mv aargs-jblock
            aargs-jexprs
            jvar-value-index) (atj-gen-avalues test.arguments "value" 1))
       ((mv ares-jblock
            ares-jexpr
            &) (atj-gen-avalue test.result "value" jvar-value-index))
       (current-time-jexpr (jexpr-smethod (jtype-class "System")
                                          "currentTimeMillis"
                                          nil))
       ((mv shallow-arg-jblock shallow-arg-jvars)
        (if deep$
            (mv nil nil)
          (atj-gen-test-jmethod-aux aargs-jexprs 1)))
       (n!=0-jexpr (jexpr-binary (jbinop-ne)
                                 (jexpr-name "n")
                                 (jexpr-literal-0)))
       (jmethod-body
        (append
         (jblock-imethod (jexpr-name "System.out")
                         "print"
                         (list (atj-gen-jstring
                                (str::cat "Testing '" test.name "'..."))))
         aargs-jblock ; build test.arguments
         (if deep$
             (jblock-locvar (jtype-array *atj-jtype-value*)
                            "functionArguments"
                            (jexpr-newarray-init *atj-jtype-value*
                                                 aargs-jexprs))
           shallow-arg-jblock) ; assign to argument1, argument2, ...
         ares-jblock ; build test.result
         (jblock-locvar *atj-jtype-value* "resultAcl2" ares-jexpr)
         (and deep$
              (jblock-locvar *atj-jtype-symbol*
                             "functionName"
                             (atj-gen-asymbol test.function)))
         (jblock-locvar (jtype-boolean) "pass" (jexpr-literal-true))
         (jblock-locvar (jtype-array (jtype-long))
                        "times"
                        (jexpr-cond n!=0-jexpr
                                    (jexpr-newarray (jtype-long)
                                                    (jexpr-name "n"))
                                    (jexpr-literal-null)))
         (jblock-locvar (jtype-long) "minTime" (jexpr-literal-0))
         (jblock-locvar (jtype-long) "maxTime" (jexpr-literal-0))
         (jblock-locvar (jtype-long) "sumTime" (jexpr-literal-0))
         (jblock-locvar (jtype-int) "i" (jexpr-literal-0))
         (jblock-do
          ;; body of do loop:
          (append
           (jblock-locvar (jtype-long) "startTime" current-time-jexpr)
           (jblock-locvar *atj-jtype-value*
                          "resultJava"
                          (if deep$
                              (jexpr-smethod (jtype-class java-class$)
                                             "call"
                                             (list
                                              (jexpr-name "functionName")
                                              (jexpr-name "functionArguments")))
                            (jexpr-smethod (jtype-class java-class$)
                                           (atj-gen-shallow-afnname
                                            test.function "")
                                           (jexpr-name-list
                                            shallow-arg-jvars))))
           (jblock-locvar (jtype-long) "endTime" current-time-jexpr)
           (jblock-asg (jexpr-name "pass")
                       (jexpr-binary (jbinop-logand)
                                     (jexpr-name "pass")
                                     (jexpr-imethod (jexpr-name "resultAcl2")
                                                    "equals"
                                                    (list (jexpr-name
                                                           "resultJava")))))
           (jblock-if n!=0-jexpr
                      (append
                       (jblock-locvar (jtype-long)
                                      "time"
                                      (jexpr-binary (jbinop-sub)
                                                    (jexpr-name "endTime")
                                                    (jexpr-name "startTime")))
                       (jblock-asg (jexpr-array (jexpr-name "times")
                                                (jexpr-name "i"))
                                   (jexpr-name "time"))
                       (jblock-asg (jexpr-name "sumTime")
                                   (jexpr-binary (jbinop-add)
                                                 (jexpr-name "sumTime")
                                                 (jexpr-name "time")))
                       (jblock-if (jexpr-binary (jbinop-logor)
                                                (jexpr-binary (jbinop-eq)
                                                              (jexpr-name "i")
                                                              (jexpr-literal-0))
                                                (jexpr-binary (jbinop-lt)
                                                              (jexpr-name
                                                               "time")
                                                              (jexpr-name
                                                               "minTime")))
                                  (jblock-asg (jexpr-name "minTime")
                                              (jexpr-name "time")))
                       (jblock-if (jexpr-binary (jbinop-gt)
                                                (jexpr-name "time")
                                                (jexpr-name "maxTime"))
                                  (jblock-asg (jexpr-name "maxTime")
                                              (jexpr-name "time")))))
           (jblock-expr (jexpr-unary (junop-preinc) (jexpr-name "i"))))
          ;; test of do loop:
          (jexpr-binary (jbinop-lt) (jexpr-name "i") (jexpr-name "n")))
         (jblock-ifelse (jexpr-name "pass")
                        (jblock-imethod (jexpr-name "System.out")
                                        "println"
                                        (list (atj-gen-jstring " PASS")))
                        (append
                         (jblock-imethod (jexpr-name "System.out")
                                         "println"
                                         (list (atj-gen-jstring " FAIL")))
                         (jblock-asg-name "failures"
                                          (jexpr-literal-true))))
         (jblock-if n!=0-jexpr
                    (append
                     (jblock-imethod (jexpr-name "System.out")
                                     "println"
                                     (list (jexpr-literal-string "  Times:")))
                     (jblock-for (jexpr-binary (jbinop-asg)
                                               (jexpr-name "i")
                                               (jexpr-literal-0))
                                 (jexpr-binary (jbinop-lt)
                                               (jexpr-name "i")
                                               (jexpr-name "n"))
                                 (jexpr-unary (junop-preinc)
                                              (jexpr-name "i"))
                                 (jblock-imethod
                                  (jexpr-name "System.out")
                                  "format"
                                  (list (jexpr-literal-string "    %.3f%n")
                                        (jexpr-binary (jbinop-div)
                                                      (jexpr-array
                                                       (jexpr-name "times")
                                                       (jexpr-name "i"))
                                                      (jexpr-literal-floating
                                                        1000)))))
                     (jblock-imethod
                      (jexpr-name "System.out")
                      "format"
                      (list (jexpr-literal-string "  Minimum: %.3f%n")
                            (jexpr-binary (jbinop-div)
                                          (jexpr-name "minTime")
                                          (jexpr-literal-floating 1000))))
                     (jblock-imethod
                      (jexpr-name "System.out")
                      "format"
                      (list (jexpr-literal-string "  Average: %.3f%n")
                            (jexpr-binary (jbinop-div)
                                          (jexpr-binary (jbinop-div)
                                                        (jexpr-name "sumTime")
                                                        (jexpr-literal-floating
                                                         1000))
                                          (jexpr-name "n"))))
                     (jblock-imethod
                      (jexpr-name "System.out")
                      "format"
                      (list (jexpr-literal-string "  Maximum: %.3f%n")
                            (jexpr-binary (jbinop-div)
                                          (jexpr-name "maxTime")
                                          (jexpr-literal-floating 1000))))
                     (jblock-imethod (jexpr-name "System.out")
                                     "println"
                                     nil))))))
    (make-jmethod :access (jaccess-private)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-void)
                  :name jmethod-name
                  :params (list (make-jparam :final? nil
                                             :type (jtype-int)
                                             :name "n"))
                  :throws (list *atj-jclass-eval-exc*)
                  :body jmethod-body))

  :prepwork
  ((define atj-gen-test-jmethod-aux ((aargs-jexprs jexpr-listp)
                                     (index posp))
     :returns (mv (jblock jblockp)
                  (jvars string-listp))
     (cond ((endp aargs-jexprs) (mv nil nil))
           (t (b* ((first-jvar (str::cat "argument" (str::natstr index)))
                   (first-jblock (jblock-locvar *atj-jtype-value*
                                                first-jvar
                                                (car aargs-jexprs)))
                   ((mv rest-jblock rest-jvars)
                    (atj-gen-test-jmethod-aux (cdr aargs-jexprs)
                                              (1+ index))))
                (mv (append first-jblock rest-jblock)
                    (cons first-jvar rest-jvars))))))))

(define atj-gen-test-jmethods ((tests$ atj-test-listp)
                               (deep$ booleanp)
                               (java-class$ stringp)
                               (verbose$ booleanp))
  :returns (jmethods jmethod-listp)
  :short "Generate all the Java methods to run the specified tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are generated only if the @(':tests') input is not @('nil')."))
  (if (endp tests$)
      nil
    (b* ((first-jmethod
          (atj-gen-test-jmethod (car tests$) deep$ java-class$ verbose$))
         (rest-jmethods
          (atj-gen-test-jmethods (cdr tests$) deep$ java-class$ verbose$)))
      (cons first-jmethod rest-jmethods))))

(define atj-gen-run-tests ((tests$ atj-test-listp))
  :returns (jblock jblockp)
  :short "Generate Java code to run the specified tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "This is a sequence of calls to the methods
     generated by @(tsee atj-gen-test-jmethods).
     These calls are part of the main method of the test Java class."))
  (if (endp tests$)
      nil
    (b* ((jmethod-name
          (atj-gen-test-jmethod-name (atj-test->name (car tests$))))
         (first-jblock (jblock-method jmethod-name (list (jexpr-name "n"))))
         (rest-jblock (atj-gen-run-tests (cdr tests$))))
      (append first-jblock rest-jblock))))

(define atj-gen-test-main-jmethod ((tests$ atj-test-listp)
                                   (java-class$ stringp))
  :returns (jmethod jmethodp)
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
     which is passed as the repetition parameter to the test methods."))
  (b* ((jmethod-param (make-jparam :final? nil
                                   :type (jtype-array (jtype-class "String"))
                                   :name "args"))
       (jmethod-body
        (append
         (jblock-locvar (jtype-int) "n" (jexpr-literal-0))
         (jblock-if (jexpr-binary (jbinop-eq)
                                  (jexpr-field (jexpr-name "args") "length")
                                  (jexpr-literal-1))
                    (jblock-asg (jexpr-name "n")
                                (jexpr-smethod (jtype-class "Integer")
                                               "parseInt"
                                               (list
                                                (jexpr-array
                                                 (jexpr-name "args")
                                                 (jexpr-literal-0))))))
         (jblock-if (jexpr-binary (jbinop-gt)
                                  (jexpr-field (jexpr-name "args") "length")
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
                  :params (list jmethod-param)
                  :throws (list *atj-jclass-eval-exc*)
                  :body jmethod-body)))

(define atj-gen-test-jclass ((tests$ atj-test-listp)
                             (deep$ booleanp)
                             (java-class$ stringp)
                             (verbose$ booleanp))
  :returns (jclass jclassp)
  :short "Generate the test Java class declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "This is a public class that contains all the generated methods.
    [JLS] says that a Java implementation may require
    public classes to be in files with the same names (plus extension).
    The code that we generate satisfies this requirement."))
  (b* (((run-when verbose$)
        (cw "~%Generating Java code for the tests:~%"))
       (failures-jfield (atj-gen-test-failures-jfield))
       (test-jmethods (atj-gen-test-jmethods tests$ deep$ java-class$ verbose$))
       (main-jmethod (atj-gen-test-main-jmethod tests$ java-class$))
       (body-jclass (append (list (jcmember-field failures-jfield))
                            (jmethods-to-jcmembers test-jmethods)
                            (list (jcmember-method main-jmethod)))))
    (make-jclass :access (jaccess-public)
                 :abstract? nil
                 :static? nil
                 :final? nil
                 :strictfp? nil
                 :name (str::cat java-class$ "Tests")
                 :superclass? nil
                 :superinterfaces nil
                 :body body-jclass)))

(define atj-gen-jcunit ((deep$ booleanp)
                        (guards$ booleanp)
                        (java-package$ maybe-stringp)
                        (java-class$ maybe-stringp)
                        (apkgs string-listp)
                        (afns symbol-listp)
                        (verbose$ booleanp)
                        state)
  :returns (jcunit jcunitp)
  :verify-guards nil
  :short "Generate the main Java compilation unit."
  (make-jcunit :package? java-package$
               :imports (list (str::cat *atj-aij-jpackage* ".*")
                              "java.math.BigInteger"
                              "java.util.ArrayList"
                              "java.util.List")
               :types (list (atj-gen-jclass apkgs
                                            afns
                                            deep$
                                            guards$
                                            java-class$
                                            verbose$
                                            state))))

(define atj-gen-test-jcunit ((deep$ booleanp)
                             (java-package$ maybe-stringp)
                             (java-class$ stringp)
                             (tests$ atj-test-listp)
                             (verbose$ booleanp))
  :returns (jcunit jcunitp)
  :short "Generate the test Java compilation unit."
  (make-jcunit :package? java-package$
               :imports (list (str::cat *atj-aij-jpackage* ".*")
                              "java.math.BigInteger")
               :types (list (atj-gen-test-jclass
                             tests$ deep$ java-class$ verbose$))))

(define atj-gen-jfile ((deep$ booleanp)
                       (guards$ booleanp)
                       (java-package$ maybe-stringp)
                       (java-class$ maybe-stringp)
                       (output-file$ stringp)
                       (apkgs string-listp)
                       (afns symbol-listp)
                       (verbose$ booleanp)
                       state)
  :returns state
  :mode :program
  :short "Generate the main Java file."
  (print-to-jfile (print-jcunit (atj-gen-jcunit deep$
                                                guards$
                                                java-package$
                                                java-class$
                                                apkgs
                                                afns
                                                verbose$
                                                state))
                  output-file$
                  state))

(define atj-gen-test-jfile ((deep$ booleanp)
                            (java-package$ maybe-stringp)
                            (java-class$ stringp)
                            (output-file-test$ stringp)
                            (tests$ atj-test-listp)
                            (verbose$ booleanp)
                            state)
  :returns state
  :mode :program
  :short "Generate the test Java file."
  (print-to-jfile (print-jcunit (atj-gen-test-jcunit deep$
                                                     java-package$
                                                     java-class$
                                                     tests$
                                                     verbose$))
                  output-file-test$
                  state))

(define atj-gen-everything ((deep$ booleanp)
                            (guards$ booleanp)
                            (java-package$ maybe-stringp)
                            (java-class$ maybe-stringp)
                            (output-file$ stringp)
                            (output-file-test$ maybe-stringp)
                            (tests$ atj-test-listp)
                            (apkgs string-listp)
                            (afns symbol-listp)
                            (verbose$ booleanp)
                            state)
  :returns (mv erp val state)
  :mode :program
  :short "Generate the main Java file, and optionally the Java test file."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the soft and hard right margins to very large values
     to avoid line breaks in virtually all cases.
     Setting these margins to ``infinity'' is not supported.")
   (xdoc::p
    "We always generate the main Java file.
     We generate the test Java file only if @(':tests') is not @('nil')."))
  (state-global-let*
   ((fmt-soft-right-margin 100000 set-fmt-soft-right-margin)
    (fmt-hard-right-margin 100000 set-fmt-hard-right-margin))
   (b* ((state (atj-gen-jfile deep$
                              guards$
                              java-package$
                              java-class$
                              output-file$
                              apkgs
                              afns
                              verbose$
                              state))
        (state (if tests$
                   (atj-gen-test-jfile deep$
                                       java-package$
                                       java-class$
                                       output-file-test$
                                       tests$
                                       verbose$
                                       state)
                 state)))
     (value nil))))
