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
    "We generate directly Java abstract syntax,
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
     recursively produced.")
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
        (jexpr-literal (jliteral-string astring))
      (jexpr-newarray (jtype-char) (atj-achars-to-jhexcodes achars)))))

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
                              :type (jtype-class "Acl2Value")
                              :name (car names))
                 (atj-gen-jparamlist-avalues (cdr names))))))

(define atj-achar-to-jchars-id ((achar characterp) (startp booleanp))
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
     we keep it unchanged in forming the Java identifier.
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
  (cond ((or (str::down-alpha-p achar)
             (str::up-alpha-p achar)) (list achar))
        ((and (digit-char-p achar)
              (not startp)) (list achar))
        ((eql achar #\-) (list #\_))
        (t (b* ((acode (char-code achar))
                ((mv hi-char lo-char) (ubyte8=>hexchars acode)))
             (list #\$ hi-char lo-char)))))

(define atj-achars-to-jchars-id ((achars character-listp) (startp booleanp))
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
        (t (append (atj-achar-to-jchars-id (car achars) startp)
                   (atj-achars-to-jchars-id (cdr achars) nil)))))

(define atj-gen-jlocvar-indexed
  ((var-type jtypep "Type of the local variable.")
   (var-base stringp "Base name of the local variable.")
   (var-index natp "Index of the local variable.")
   (var-init jexprp "Initializer of the local variable."))
  :returns (mv (locvar jlocvarp)
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
     and the next variable with the same name must use the next index."))
  (b* ((var-name (str::cat var-base (natstr var-index)))
       (var-index (1+ var-index))
       (locvar (make-jlocvar :final? nil
                             :type var-type
                             :name var-name
                             :init var-init)))
    (mv locvar var-name var-index))
  ///

  (defrule posp-of-atj-gen-jlocvar-indexed-new-var-index
    (implies (posp var-index)
             (posp (mv-nth 2 (atj-gen-jlocvar-indexed
                              var-type var-base var-index var-init))))))

(defval *atj-jvar-value*
  :short "Base name of the Java local variables used to build
          Java representations of ACL2 values."
  :long
  (xdoc::topstring-p
   "We start the name with a @('$') to avoid possible conflicts with
    the Java variables generated for the shallow embedding approach.")
  "$value"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-value*)))

(define atj-gen-achar ((achar characterp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 character."
  (b* ((literal (make-jliteral-integer :value (char-code achar)
                                       :long? nil
                                       :base (jintbase-decimal)))
       (expr (jexpr-cast (jtype-char) (jexpr-literal literal))))
    (jexpr-smethod (jtype-class "Acl2Character")
                   "make"
                   (list expr))))

(define atj-gen-astring ((astring stringp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 string."
  (jexpr-smethod (jtype-class "Acl2String")
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
   (t (jexpr-smethod (jtype-class "Acl2Symbol")
                     "make"
                     (list (atj-gen-jstring
                            (symbol-package-name asymbol))
                           (atj-gen-jstring
                            (symbol-name asymbol)))))))

(define atj-gen-ainteger ((ainteger integerp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 integer."
  :long
  (xdoc::topstring-p
   "If the ACL2 integer is representable as a Java integer,
    we generate a Java integer literal.
    Otherwise, if it is representable as a Java long integer,
    we generate a Java long integer literal.
    Otherwise, we generate a Java big integer
    built out of the string representation of the ACL2 integer.")
  (b* ((arg (cond ((signed-byte-p 32 ainteger)
                   (if (< ainteger 0)
                       (jexpr-unary (junop-uminus)
                                    (jexpr-literal
                                     (make-jliteral-integer
                                      :value (- ainteger)
                                      :long? nil
                                      :base (jintbase-decimal))))
                     (jexpr-literal (make-jliteral-integer
                                     :value ainteger
                                     :long? nil
                                     :base (jintbase-decimal)))))
                  ((signed-byte-p 64 ainteger)
                   (if (< ainteger 0)
                       (jexpr-unary (junop-uminus)
                                    (jexpr-literal
                                     (make-jliteral-integer
                                      :value (- ainteger)
                                      :long? t
                                      :base (jintbase-decimal))))
                     (jexpr-literal (make-jliteral-integer
                                     :value ainteger
                                     :long? t
                                     :base (jintbase-decimal)))))
                  (t (b* ((string (if (< ainteger 0)
                                      (str::cat "-" (str::natstr (- ainteger)))
                                    (str::natstr ainteger)))
                          (stringlit (jliteral-string string))
                          (stringexpr (jexpr-literal stringlit)))
                       (jexpr-newclass (jtype-class "BigInteger")
                                       (list stringexpr)))))))
    (jexpr-smethod (jtype-class "Acl2Integer")
                   "make"
                   (list arg))))

(define atj-gen-arational ((arational rationalp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 rational."
  (jexpr-smethod (jtype-class "Acl2Rational")
                 "make"
                 (list (atj-gen-ainteger (numerator arational))
                       (atj-gen-ainteger (denominator arational)))))

(define atj-gen-anumber ((anumber acl2-numberp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 number."
  (jexpr-smethod (jtype-class "Acl2Number")
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
     from the two local variables."))

  (define atj-gen-aconspair ((aconspair consp) (jvar-value-index posp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index)))
    :parents nil
    (b* (((unless (mbt (consp aconspair)))
          (mv nil (jexpr-name "irrelevant") jvar-value-index))
         ((mv car-jblock
              car-jexpr
              jvar-value-index) (atj-gen-avalue (car aconspair)
                                                jvar-value-index))
         ((mv car-jlocvardecl
              car-jvar
              jvar-value-index) (atj-gen-jlocvar-indexed (jtype-class
                                                          "Acl2Value")
                                                         *atj-jvar-value*
                                                         jvar-value-index
                                                         car-jexpr))
         ((mv cdr-jblock
              cdr-jexpr
              jvar-value-index) (atj-gen-avalue (cdr aconspair)
                                                jvar-value-index))
         ((mv cdr-jlocvardecl
              cdr-jvar
              jvar-value-index) (atj-gen-jlocvar-indexed (jtype-class
                                                          "Acl2Value")
                                                         *atj-jvar-value*
                                                         jvar-value-index
                                                         cdr-jexpr))
         (jblock (append car-jblock
                         (list (jstatem-locvar car-jlocvardecl))
                         cdr-jblock
                         (list (jstatem-locvar cdr-jlocvardecl))))
         (jexpr (jexpr-smethod (jtype-class "Acl2ConsPair")
                               "make"
                               (list (jexpr-name car-jvar)
                                     (jexpr-name cdr-jvar)))))
      (mv jblock jexpr jvar-value-index))
    :measure (two-nats-measure (acl2-count aconspair) 0))

  (define atj-gen-avalue (avalue (jvar-value-index posp))
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
                                             jvar-value-index))
          (t (prog2$ (raise "Internal error: the value ~x0 is a bad atom."
                            avalue)
                     (mv nil (jexpr-name "irrelevant") jvar-value-index))))
    :measure (two-nats-measure (acl2-count avalue) 1))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-gen-avalue))

(define atj-gen-asymbols ((asymbols symbol-listp))
  :returns (jexprs jexpr-listp)
  :short "Lift @(tsee atj-gen-asymbol) to lists."
  (cond ((endp asymbols) nil)
        (t (cons (atj-gen-asymbol (car asymbols))
                 (atj-gen-asymbols (cdr asymbols))))))

(defval *atj-jvar-term*
  :short "Base name of the Java local variables used to build
          deeply embedded Java representations of ACL2 terms."
  "term"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-term*)))

(defval *atj-jvar-lambda*
  :short "Base name of the Java local variables used to build
          deeply embedded Java representations of ACL2 lambda expressions."
  "lambda"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-lambda*)))

(define atj-gen-deep-aqconst
  ((aqconst "(Unquoted) value of the ACL2 quoted constant.")
   (jvar-value-index posp))
  :returns (mv (jblock jblockp)
               (jexpr jexprp)
               (new-jvar-value-index posp :hyp (posp jvar-value-index)))
  :short "Generate Java code to build a deeply embedded ACL2 quoted constant."
  (b* (((mv value-jblock
            value-jexpr
            jvar-value-index) (atj-gen-avalue aqconst
                                              jvar-value-index))
       (jblock value-jblock)
       (jexpr (jexpr-smethod (jtype-class "Acl2QuotedConstant")
                             "make"
                             (list value-jexpr))))
    (mv jblock jexpr jvar-value-index)))

(define atj-gen-deep-avar ((avar symbolp "The ACL2 variable."))
  :returns (jexpr jexprp)
  :short "Generate Java code to build a deeply embedded ACL2 variable."
  (jexpr-smethod (jtype-class "Acl2Variable")
                 "make"
                 (list (atj-gen-asymbol avar))))

(define atj-gen-deep-aformals ((aformals symbol-listp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build a deeply embedded formals parameter list
          of an ACL2 named function or lambda expression."
  :long
  (xdoc::topstring-p
   "The generated code builds an array of the formals as symbols.")
  (jexpr-newarray (jtype-class "Acl2Symbol")
                  (atj-gen-asymbols aformals)))
(defines atj-gen-deep-aterms+alambdas
  :short "Generate Java code to build
          deeply embedded ACL2 terms and lambda expressions."

  (define atj-gen-deep-afnapp ((afn pseudo-termfnp)
                               (aargs pseudo-term-listp)
                               (jvar-value-index posp)
                               (jvar-term-index posp)
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
                  (jexpr-smethod (jtype-class "Acl2NamedFunction")
                                 "make"
                                 (list (atj-gen-asymbol afn)))
                  jvar-value-index
                  jvar-term-index
                  jvar-lambda-index)
            (atj-gen-deep-alambda (lambda-formals afn)
                                  (lambda-body afn)
                                  jvar-value-index
                                  jvar-term-index
                                  jvar-lambda-index)))
         ((mv aargs-jblock
              aarg-jexprs
              jvar-value-index
              jvar-term-index
              jvar-lambda-index) (atj-gen-deep-aterms aargs
                                                      jvar-value-index
                                                      jvar-term-index
                                                      jvar-lambda-index))
         (aargs-jexpr (jexpr-newarray (jtype-class "Acl2Term") aarg-jexprs))
         (afnapp-jexpr (jexpr-smethod (jtype-class "Acl2FunctionApplication")
                                      "make"
                                      (list afn-jexpr
                                            aargs-jexpr)))
         ((mv afnapp-jlocvar
              afnapp-jvar
              jvar-term-index) (atj-gen-jlocvar-indexed (jtype-class "Acl2Term")
                                                        *atj-jvar-term*
                                                        jvar-term-index
                                                        afnapp-jexpr)))
      (mv (append afn-jblock
                  aargs-jblock
                  (list (jstatem-locvar afnapp-jlocvar)))
          (jexpr-name afnapp-jvar)
          jvar-value-index
          jvar-term-index
          jvar-lambda-index))
    :measure (two-nats-measure (+ (acl2-count afn) (acl2-count aargs)) 2))

  (define atj-gen-deep-alambda ((aformals symbol-listp)
                                (abody pseudo-termp)
                                (jvar-value-index posp)
                                (jvar-term-index posp)
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
                                                     jvar-value-index
                                                     jvar-term-index
                                                     jvar-lambda-index))
         (alambda-jexpr (jexpr-smethod (jtype-class "Acl2LambdaExpression")
                                       "make"
                                       (list aformals-jexpr
                                             abody-jexpr)))
         ((mv alambda-jlocvar
              alambda-jvar
              jvar-lambda-index) (atj-gen-jlocvar-indexed
                                  (jtype-class "Acl2LambdaExpression")
                                  *atj-jvar-lambda*
                                  jvar-lambda-index
                                  alambda-jexpr)))
      (mv (append abody-jblock
                  (list (jstatem-locvar alambda-jlocvar)))
          (jexpr-name alambda-jvar)
          jvar-value-index
          jvar-term-index
          jvar-lambda-index))
    :measure (two-nats-measure (acl2-count abody) 1))

  (define atj-gen-deep-aterm ((aterm pseudo-termp)
                              (jvar-value-index posp)
                              (jvar-term-index posp)
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
                                                       jvar-value-index)))
                             (mv jblock
                                 jexpr
                                 jvar-value-index
                                 jvar-term-index
                                 jvar-lambda-index)))
          (t (atj-gen-deep-afnapp (ffn-symb aterm)
                                  (fargs aterm)
                                  jvar-value-index
                                  jvar-term-index
                                  jvar-lambda-index)))
    :measure (two-nats-measure (acl2-count aterm) 0))

  (define atj-gen-deep-aterms ((aterms pseudo-term-listp)
                               (jvar-value-index posp)
                               (jvar-term-index posp)
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
                                                       jvar-value-index
                                                       jvar-term-index
                                                       jvar-lambda-index))
           ((mv rest-jblock
                jexprs
                jvar-value-index
                jvar-term-index
                jvar-lambda-index) (atj-gen-deep-aterms (cdr aterms)
                                                        jvar-value-index
                                                        jvar-term-index
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

(define atj-gen-shallow-avar ((avar symbolp) (index natp) (curr-apkg stringp))
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
     whose body is a shallowly embedded represented of the ACL2 function body.
     The ACL2 function body may reference the ACL2 function's parameter,
     as well as @(tsee let)-bound variables (via lambda expressions).
     Thus, the same variable name may in fact denote different variables
     in different parts of an ACL2 function body.
     Java does not allow different local variables with the same
     (in nested scopes in) the same method,
     and so we need to map equally named ACL2 variables
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
     We do something similar for the Java variable names,
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
     and @('<index>') is a decimal representation of the numeric index.
     If @('pname') is the same as the current package, we omit @('<pname>$$$').
     If the index is 0, we omit @('$$<index>'),
     so that if there is just one variable with a certain name,
     since we start with index 0, no index is added to the name.
     Thus there are a few combinations possible with these three parts;
     the use of triple and double @('$') characters guaranteee
     that there is no confusion with the @('$hh') escapes
     where @('hh') is the hex code of an ACL2 character
     that is not valid for a Java identifier.
     Furthermore, if the resulting variable name if just @('<name>')
     and happens to be a Java keyword or Java literal or empty,
     we add a single @('$') at the end, which again is unambiguous.")
   (xdoc::p
    "This is a simple scheme to keep names unique,
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
       (pname$$$-jchars (if (equal apkg curr-apkg)
                            nil
                          (append (atj-achars-to-jchars-id (explode apkg) t)
                                  (list #\$ #\$ #\$))))
       (name-jchars (atj-achars-to-jchars-id (explode (symbol-name avar))
                                             (endp pname$$$-jchars)))
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
                               (jvar-var-indices symbol-nat-alistp)
                               (curr-apkg stringp))
  :returns (mv (jvars symbol-string-alistp :hyp (symbol-listp avars))
               (new-jvar-var-indices "A @(tsee symbol-nat-alistp)."))
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
  (b* (((when (endp avars)) (mv nil jvar-var-indices))
       (avar (car avars))
       (avar+index (assoc-eq avar jvar-var-indices))
       (index (if avar+index (cdr avar+index) 0))
       (jvar-var-indices (acons avar (1+ index) jvar-var-indices))
       ((mv jvars jvar-var-indices) (atj-gen-shallow-avars (cdr avars)
                                                           jvar-var-indices
                                                           curr-apkg)))
    (mv (acons avar (atj-gen-shallow-avar avar index curr-apkg) jvars)
        jvar-var-indices)))

(defval *atj-aij-class-names*
  :short "Names of the Java classes that form AIJ."
  (list "Acl2Character"
        "Acl2ComplexRational"
        "Acl2ConsPair"
        "Acl2DefinedFunction"
        "Acl2Environment"
        "Acl2EvaluationException"
        "Acl2Function"
        "Acl2FunctionApplication"
        "Acl2Integer"
        "Acl2LambdaExpression"
        "Acl2NamedFunction"
        "Acl2NativeFunction"
        "Acl2Number"
        "Acl2PackageName"
        "Acl2QuotedConstant"
        "Acl2Ratio"
        "Acl2Rational"
        "Acl2String"
        "Acl2Symbol"
        "Acl2Term"
        "Acl2Value"
        "Acl2Variable")
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
  (b* ((jchars (atj-achars-to-jchars-id (explode apkg) t))
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
                         (append (atj-achars-to-jchars-id (explode apkg) t)
                                 (list #\.))))
       (jmethod-jchars (atj-achars-to-jchars-id (explode (symbol-name afn)) t))
       (jmethod-jchars (if (member-equal jmethod-jchars
                                         *atj-disallowed-shallow-jmethods*)
                           (rcons #\$ jmethod-jchars)
                         jmethod-jchars))
       (jchars (append jclass.-jchars jmethod-jchars))
       (jstring (implode jchars)))
    jstring))

(define atj-gen-shallow-let-bindings ((avars symbol-listp)
                                      (jexprs msg-listp)
                                      (jvars symbol-string-alistp))
  :guard (and (= (len jexprs) (len avars))
              (subsetp-eq avars (strip-cars jvars)))
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
     are stored in the @('jvars') alist."))
  (b* (((when (endp avars)) nil)
       (avar (car avars))
       (jexpr (car jexprs))
       (jvar (cdr (assoc-eq avar jvars)))
       (first-jlocvar (make-jlocvar :final? nil
                                    :type (jtype-class"Acl2Value")
                                    :name jvar
                                    :init jexpr))
       (first-jstatem (jstatem-locvar first-jlocvar))
       (rest-jblock (atj-gen-shallow-let-bindings (cdr avars)
                                                  (cdr jexprs)
                                                  jvars)))
    (cons first-jstatem rest-jblock)))

(defval *atj-jvar-result*
  :short "Base name of the Java local variables used to store
          the results of arguments of non-strict ACL2 functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Normally, in the shallow embedding approach,
     the actual arguments of an ACL2 function or lambda expression
     are calculated by the generated Java code,
     and then the (shallowly embedded) ACL2 function or lambda expression
     is called on them.
     For the non-strict function @(tsee if)
     and the non-strict ``pseudo-function'' @('or')
     (see the documentation of AIJ for details on the latter),
     the generated Java code follows a different strategy,
     in order to realize the required non-strictness.")
   (xdoc::p
    "This strategy involves generating Java local variables
     to store results of arguments of non-strict ACL2 functions.
     This constant is the base name to use for these Java local variables;
     indices are appended to them as neede, as with other recursive structures
     (note that non-strict ACL2 functions may be in fact nested).
     The fact that it starts with a @('$')
     and that the two subsequent characters @('r') and @('e')
     are not hexadecimal digits,
     means that this name (possibly with an index after it)
     will be always distinct from the names of the variables
     generated by @(tsee atj-gen-shallow-avar)."))
  "$result"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-result*)))

(defines atj-gen-shallow-aterms+alambdas
  :short "Generate shallowly embedded ACL2 terms and lambda expressions."

  (define atj-gen-shallow-aifapp ((atest pseudo-termp)
                                  (athen pseudo-termp)
                                  (aelse pseudo-termp)
                                  (jvars symbol-string-alistp)
                                  (jvar-var-indices symbol-nat-alistp)
                                  (jvar-value-index posp)
                                  (jvar-result-index posp)
                                  (curr-pkg stringp))
    :returns (mv (jblock "A @(tsee jblockp).")
                 (jexpr "A @(tsee jexprp).")
                 (new-jvar-var-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :mode :program
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
       @(tsee *atj-jvar-result*) followed by a numeric index.")
     (xdoc::p
      "In other words, we first compute the test
       and create a local variable to store the final result.
       Based on the test, we execute either branch (for non-strictness),
       storing the result into the variable."))
    (b* (((mv test-jblock
              test-jexpr
              jvar-var-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm atest
                                                        jvars
                                                        jvar-var-indices
                                                        jvar-value-index
                                                        jvar-result-index
                                                        curr-pkg))
         ((mv result-jlocvar jvar-result jvar-result-index)
          (atj-gen-jlocvar-indexed (jtype-class "Acl2Value")
                                   *atj-jvar-result*
                                   jvar-result-index
                                   (jexpr-literal (jliteral-null))))
         ((mv else-jblock
              else-jexpr
              jvar-var-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm aelse
                                                        jvars
                                                        jvar-var-indices
                                                        jvar-value-index
                                                        jvar-result-index
                                                        curr-pkg))
         (else-jstatem (jstatem-expr (jexpr-binary (jbinop-asg)
                                                   (jexpr-name jvar-result)
                                                   else-jexpr)))
         ((mv then-jblock
              then-jexpr
              jvar-var-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm athen
                                                        jvars
                                                        jvar-var-indices
                                                        jvar-value-index
                                                        jvar-result-index
                                                        curr-pkg))
         (then-jstatem (jstatem-expr (jexpr-binary (jbinop-asg)
                                                   (jexpr-name jvar-result)
                                                   then-jexpr)))
         (if-jstatem (jstatem-ifelse
                      (jexpr-imethod (jexpr-name "Acl2Symbol.NIL")
                                     "equals"
                                     (list test-jexpr))
                      (append else-jblock
                              (list else-jstatem))
                      (append then-jblock
                              (list then-jstatem))))
         (jblock (append test-jblock
                         (list (jstatem-locvar result-jlocvar))
                         (list if-jstatem)))
         (jexpr (jexpr-name jvar-result)))
      (mv jblock
          jexpr
          jvar-var-indices
          jvar-value-index
          jvar-result-index)))

  (define atj-gen-shallow-aorapp ((afirst pseudo-termp)
                                  (asecond pseudo-termp)
                                  (jvars symbol-string-alistp)
                                  (jvar-var-indices symbol-nat-alistp)
                                  (jvar-value-index posp)
                                  (jvar-result-index posp)
                                  (curr-pkg stringp))
    :returns (mv (jblock "A @(tsee jblockp).")
                 (jexpr "A @(tsee jexprp).")
                 (new-jvar-var-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :mode :program
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
              jvar-var-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm afirst
                                                        jvars
                                                        jvar-var-indices
                                                        jvar-value-index
                                                        jvar-result-index
                                                        curr-pkg))
         ((mv result-jlocvar jvar-result jvar-result-index)
          (atj-gen-jlocvar-indexed (jtype-class "Acl2Value")
                                   *atj-jvar-result*
                                   jvar-result-index
                                   (jexpr-literal (jliteral-null))))
         ((mv second-jblock
              second-jexpr
              jvar-var-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm asecond
                                                        jvars
                                                        jvar-var-indices
                                                        jvar-value-index
                                                        jvar-result-index
                                                        curr-pkg))
         (second-jstatem (jstatem-expr (jexpr-binary (jbinop-asg)
                                                     (jexpr-name jvar-result)
                                                     second-jexpr)))
         (first-jstatem (jstatem-expr (jexpr-binary (jbinop-asg)
                                                    (jexpr-name jvar-result)
                                                    first-jexpr)))
         (if-jstatem (jstatem-ifelse
                      (jexpr-imethod (jexpr-name "Acl2Symbol.NIL")
                                     "equals"
                                     (list first-jexpr))
                      (append second-jblock
                              (list second-jstatem))
                      (list first-jstatem)))
         (jblock (append first-jblock
                         (list (jstatem-locvar result-jlocvar))
                         (list if-jstatem)))
         (jexpr (jexpr-name jvar-result)))
      (mv jblock
          jexpr
          jvar-var-indices
          jvar-value-index
          jvar-result-index)))

  (define atj-gen-shallow-afnapp ((afn pseudo-termfnp)
                                  (aargs pseudo-term-listp)
                                  (jvars symbol-string-alistp)
                                  (jvar-var-indices symbol-nat-alistp)
                                  (jvar-value-index posp)
                                  (jvar-result-index posp)
                                  (curr-pkg stringp))
    :returns (mv (jblock "A @(tsee jblockp).")
                 (jexpr "A @(tsee jexprp).")
                 (new-jvar-var-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :mode :program
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
    (b* (((when (eq afn 'if))
          (b* ((afirst (first aargs))
               (asecond (second aargs))
               (athird (third aargs)))
            (if (equal afirst asecond)
                (atj-gen-shallow-aorapp afirst
                                        athird
                                        jvars
                                        jvar-var-indices
                                        jvar-value-index
                                        jvar-result-index
                                        curr-pkg)
              (atj-gen-shallow-aifapp afirst
                                      asecond
                                      athird
                                      jvars
                                      jvar-var-indices
                                      jvar-value-index
                                      jvar-result-index
                                      curr-pkg))))
         ((mv args-jblock
              arg-jexprs
              jvar-var-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterms aargs
                                                         jvars
                                                         jvar-var-indices
                                                         jvar-value-index
                                                         jvar-result-index
                                                         curr-pkg))
         ((when (symbolp afn))
          (mv args-jblock
              (jexpr-method (atj-gen-shallow-afnname afn curr-pkg)
                            arg-jexprs)
              jvar-var-indices
              jvar-value-index
              jvar-result-index))
         ((mv lambda-jblock
              lambda-jexpr
              jvar-var-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-alambda (lambda-formals afn)
                                                          (lambda-body afn)
                                                          arg-jexprs
                                                          jvar-var-indices
                                                          jvar-value-index
                                                          jvar-result-index
                                                          curr-pkg))
         (jblock (append args-jblock
                         lambda-jblock))
         (jexpr lambda-jexpr))
      (mv jblock
          jexpr
          jvar-var-indices
          jvar-value-index
          jvar-result-index)))

  (define atj-gen-shallow-alambda ((aformals symbol-listp)
                                   (abody pseudo-termp)
                                   (jargs jexpr-listp)
                                   (jvar-var-indices symbol-nat-alistp)
                                   (jvar-value-index posp)
                                   (jvar-result-index posp)
                                   (curr-pkg stringp))
    :guard (= (len jargs) (len aformals))
    :returns (mv (jblock "A @(tsee jblockp).")
                 (jexpr "A @(tsee jexprp).")
                 (new-jvar-var-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :mode :program
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Generate a shallowly embedded ACL2 lambda expression,
            applied to given Java expressions as arguments."
    :long
    (xdoc::topstring
     (xdoc::p
      "Since a lambda expression introduces new ACL2 variables,
       we first generate new Java local variables
       for the ACL2 variables that form the formal parameters,
       producing a new @('jvars') alist
       and updating the @('jvar-var-indices') alist.")
     (xdoc::p
      "Then we assign to these Java local variables
       the Java expressions for the actual arguments,
       as in @(tsee let) bindings.")
     (xdoc::p
      "Finally, we generate Java code
       for the body of the lambda expression."))
    (b* (((mv jvars jvar-var-indices) (atj-gen-shallow-avars aformals
                                                             jvar-var-indices
                                                             curr-pkg))
         (let-jblock (atj-gen-shallow-let-bindings aformals
                                                   jargs
                                                   jvars))
         ((mv body-jblock
              body-jexpr
              jvar-var-indices
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm abody
                                                        jvars
                                                        jvar-var-indices
                                                        jvar-value-index
                                                        jvar-result-index
                                                        curr-pkg)))
      (mv (append let-jblock body-jblock)
          body-jexpr
          jvar-var-indices
          jvar-value-index
          jvar-result-index)))

  (define atj-gen-shallow-aterm ((aterm pseudo-termp)
                                 (jvars symbol-string-alistp)
                                 (jvar-var-indices symbol-nat-alistp)
                                 (jvar-value-index posp)
                                 (jvar-result-index posp)
                                 (curr-pkg stringp))
    :returns (mv (jblock "A @(tsee jblockp).")
                 (jexpr "A @(tsee jexprp).")
                 (new-jvar-var-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :mode :program
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
       we represent it as its value.
       Note that the Java variables with base name @(tsee *atj-jvar-value*),
       used to construct ACL2 values,
       never conflicts with the Java variables
       with base name @(tsee *atj-jvar-result*)
       or with the shallowly embedded ACL2 variables."))
    (cond ((variablep aterm) (mv nil
                                 (jexpr-name (cdr (assoc-eq aterm jvars)))
                                 jvar-var-indices
                                 jvar-value-index
                                 jvar-result-index))
          ((fquotep aterm) (b* (((mv jblock jexpr jvar-value-index)
                                 (atj-gen-avalue (unquote aterm)
                                                 jvar-value-index)))
                             (mv jblock
                                 jexpr
                                 jvar-var-indices
                                 jvar-value-index
                                 jvar-result-index)))
          (t (atj-gen-shallow-afnapp (ffn-symb aterm)
                                     (fargs aterm)
                                     jvars
                                     jvar-var-indices
                                     jvar-value-index
                                     jvar-result-index
                                     curr-pkg))))

  (define atj-gen-shallow-aterms ((aterms pseudo-term-listp)
                                  (jvars symbol-string-alistp)
                                  (jvar-var-indices symbol-nat-alistp)
                                  (jvar-value-index posp)
                                  (jvar-result-index posp)
                                  (curr-pkg stringp))
    :returns (mv (jblock "A @(tsee jblockp).")
                 (jexprs "A @(tsee jexpr-listp).")
                 (new-jvar-var-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :mode :program
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Lift @(tsee atj-gen-shallow-aterm) to lists."
    (if (endp aterms)
        (mv nil nil jvar-var-indices jvar-value-index jvar-result-index)
      (b* (((mv first-jblock
                first-jexpr
                jvar-var-indices
                jvar-value-index
                jvar-result-index) (atj-gen-shallow-aterm (car aterms)
                                                          jvars
                                                          jvar-var-indices
                                                          jvar-value-index
                                                          jvar-result-index
                                                          curr-pkg))
           ((mv rest-jblock
                rest-jexprs
                jvar-var-indices
                jvar-value-index
                jvar-result-index) (atj-gen-shallow-aterms (cdr aterms)
                                                           jvars
                                                           jvar-var-indices
                                                           jvar-value-index
                                                           jvar-result-index
                                                           curr-pkg)))
        (mv (append first-jblock rest-jblock)
            (cons first-jexpr rest-jexprs)
            jvar-var-indices
            jvar-value-index
            jvar-result-index)))))

(define atj-gen-apkg-jmethod-name ((apkg stringp))
  :returns (jmethod-name stringp)
  :short "Name of the Java method
          that adds an ACL2 package definition to the environment."
  :long
  (xdoc::topstring-p
   "We generate a private static method for each ACL2 package definition
    to add to the Java representation of the ACL2 environment.
    This function generates the name of this method,
    which should be distinct from all the other methods
    generated for the same class.")
  (str::cat "$addPackageDef_"
            (implode (atj-achars-to-jchars-id (explode apkg) nil))))

(define atj-gen-apkg-name ((apkg stringp))
  :returns (expr jexprp)
  :short "Generate Java code to build an ACL2 package name."
  :long
  (xdoc::topstring-p
   "Note that package names
    can always be safely generated as Java string literals.")
  (jexpr-smethod (jtype-class "Acl2PackageName")
                 "make"
                 (list (atj-gen-jstring apkg))))

(defval *atj-jvar-aimports*
  :short "Name of the Java local variable used to build
          the import lists of ACL2 packages."
  "imports"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-aimports*)))

(define atj-gen-apkg-jmethod ((apkg stringp) (verbose$ booleanp))
  :returns (jmethod jmethodp)
  :short "Generate a Java method
          that adds an ACL2 package definition to the environment."
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
    to add the package to the environment with the calculated import list.")
  (b* (((run-when verbose$)
        (cw "  ~s0~%" apkg))
       (jmethod-name (atj-gen-apkg-jmethod-name apkg))
       (aimports (pkg-imports apkg))
       (len-jliteral (make-jliteral-integer :value (len aimports)
                                            :long? nil
                                            :base (jintbase-decimal)))
       (newlist-jexpr (jexpr-newclass (jtype-class "ArrayList<>")
                                      (list (jexpr-literal len-jliteral))))
       (imports-jlocvar (make-jlocvar :final? nil
                                      :type (jtype-class "List<Acl2Symbol>")
                                      :name *atj-jvar-aimports*
                                      :init newlist-jexpr))
       (imports-jblock (atj-gen-apkg-jmethod-aux aimports))
       (apkg-name-jexpr (atj-gen-apkg-name apkg))
       (defpkg-jstatem (jstatem-expr
                        (jexpr-smethod (jtype-class "Acl2Environment")
                                       "addPackageDef"
                                       (list apkg-name-jexpr
                                             (jexpr-name
                                              *atj-jvar-aimports*)))))
       (jmethod-body (append (list (jstatem-locvar imports-jlocvar))
                             imports-jblock
                             (list defpkg-jstatem))))
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
  ((define atj-gen-apkg-jmethod-aux ((imports symbol-listp))
     :returns (jblock jblockp)
     :parents nil
     (cond ((endp imports) nil)
           (t (b* ((import-jexpr (atj-gen-asymbol (car imports)))
                   (first-jstatem
                    (jstatem-expr
                     (jexpr-imethod (jexpr-name *atj-jvar-aimports*)
                                    "add"
                                    (list import-jexpr))))
                   (rest-jblock (atj-gen-apkg-jmethod-aux (cdr imports))))
                (cons first-jstatem rest-jblock)))))))

(define atj-gen-apkg-jmethods ((apkgs string-listp) (verbose$ booleanp))
  :returns (jmethods jmethod-listp)
  :short "Generate all the Java methods
          that add the ACL2 package definitions to the environment."
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
         (first-jstatem (jstatem-expr (jexpr-method jmethod-name nil)))
         (rest-jblock (atj-gen-apkgs (cdr apkgs))))
      (cons first-jstatem rest-jblock))))

(define atj-gen-apkg-witness ()
  :returns (jstatem jstatemp)
  :short "Generate Java code to set the name of the ACL2 package witness."
  :long
  (xdoc::topstring-p
   "This is a statement that is part of
    initializing (the Java representation of) the ACL2 environment.")
  (jstatem-expr (jexpr-smethod (jtype-class "Acl2Environment")
                               "setPackageWitnessName"
                               (list (atj-gen-jstring *pkg-witness-name*)))))

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
   (implode (atj-achars-to-jchars-id (explode (symbol-package-name afn)) nil))
   "$$$"
   (implode (atj-achars-to-jchars-id (explode (symbol-name afn)) nil))))

(defval *atj-jvar-formals*
  :short "Name of the Java local variable used to store
          the formal arguments of a deeply embedded ACL2 function definition."
  "formals"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-formals*)))

(defval *atj-jvar-body*
  :short "Name of the Java local variable used to store
          the body of a deeply embedded ACL2 function definition."
  "body"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-body*)))

(defval *atj-jvar-function*
  :short "Name of the Java local variable used to store
          a deeply embedded ACL2 function."
  "function"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-function*)))

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
       (aformals (formals afn (w state)))
       (abody (getpropc afn 'unnormalized-body))
       (abody (if guards$
                  (remove-mbe-logic-from-term abody)
                (remove-mbe-exec-from-term abody)))
       (afn-jexpr (atj-gen-asymbol afn))
       (aformals-jexpr (atj-gen-deep-aformals aformals))
       ((mv abody-jblock abody-jexpr & & &) (atj-gen-deep-aterm abody 1 1 1))
       (afn-jlocvar (make-jlocvar :final? nil
                                  :type (jtype-class "Acl2NamedFunction")
                                  :name *atj-jvar-function*
                                  :init (jexpr-smethod
                                         (jtype-class "Acl2NamedFunction")
                                         "make"
                                         (list afn-jexpr))))
       (aformals-jlocvar (make-jlocvar :final? nil
                                       :type (jtype-array
                                              (jtype-class "Acl2Symbol"))
                                       :name *atj-jvar-formals*
                                       :init aformals-jexpr))
       (abody-jlocvar (make-jlocvar :final? nil
                                    :type (jtype-class "Acl2Term")
                                    :name *atj-jvar-body*
                                    :init abody-jexpr))
       (def-jstatem (jstatem-expr
                     (jexpr-imethod (jexpr-name *atj-jvar-function*)
                                    "define"
                                    (list (jexpr-name *atj-jvar-formals*)
                                          (jexpr-name *atj-jvar-body*)))))
       (jmethod-body (append abody-jblock
                             (list (jstatem-locvar afn-jlocvar)
                                   (jstatem-locvar aformals-jlocvar)
                                   (jstatem-locvar abody-jlocvar)
                                   def-jstatem))))
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
         (first-jstatem (jstatem-expr (jexpr-method jmethod-name nil)))
         (rest-jblock (atj-gen-deep-afndefs (cdr afns))))
      (cons first-jstatem rest-jblock))))

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
       (jcall (jexpr-smethod (jtype-class "Acl2NativeFunction")
                             jcall-method-name
                             (jexpr-name-list jcall-arg-names)))
       (jmethod-name (atj-gen-shallow-afnname afn curr-pkg))
       (jmethod-params (atj-gen-jparamlist-avalues jcall-arg-names))
       (jmethod-body (list (jstatem-return jcall))))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type (jtype-class "Acl2Value"))
                  :name jmethod-name
                  :params jmethod-params
                  :throws (list "Acl2EvaluationException")
                  :body jmethod-body))
  :guard-hints (("Goal" :in-theory (enable primitivep))))

(define atj-gen-shallow-afndef ((afn symbolp)
                                (guards$ booleanp)
                                (verbose$ booleanp)
                                (curr-pkg stringp)
                                state)
  :guard (equal (symbol-package-name afn) curr-pkg)
  :returns (jmethod "A @(tsee jmethodp).")
  :mode :program
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
     with base names @(tsee *atj-jvar-value*) and @(tsee *atj-jvar-result*)
     are initialized to 1, since we are at the top level here.
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
       ((mv jvars
            jvar-var-indices) (atj-gen-shallow-avars aformals nil curr-pkg))
       (jmethod-params (atj-gen-jparamlist-avalues (strip-cdrs jvars)))
       (abody (getpropc afn 'unnormalized-body))
       (abody (if guards$
                  (remove-mbe-logic-from-term abody)
                (remove-mbe-exec-from-term abody)))
       ((mv abody-jblock abody-jexpr & & &)
        (atj-gen-shallow-aterm abody jvars jvar-var-indices 1 1 curr-pkg))
       (jmethod-body (append abody-jblock
                             (list (jstatem-return abody-jexpr)))))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type (jtype-class "Acl2Value"))
                  :name jmethod-name
                  :params jmethod-params
                  :throws (list "Acl2EvaluationException")
                  :body jmethod-body)))

(define atj-gen-shallow-afn ((afn symbolp)
                             (guards$ booleanp)
                             (verbose$ booleanp)
                             (curr-pkg stringp)
                             state)
  :guard (equal (symbol-package-name afn) curr-pkg)
  :returns (jmethod "A @(tsee jmethodp).")
  :mode :program
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
  :returns (jmethods "A @(tsee jmethod-listp).")
  :mode :program
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
  :returns (jclass "A @(tsee jclassp).")
  :mode :program
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
  :returns (jclasses "A @(tsee jclass-listp).")
  :mode :program
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
     :returns jclasses ; JCLASS-LISTP
     :mode :program
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
       (throw-jstatem (jstatem-throw (jexpr-newclass
                                      (jtype-class "IllegalStateException")
                                      (list exception-message-jexpr))))
       (if-jstatem (jstatem-if (jexpr-name "initialized")
                               (list throw-jstatem)))
       (apkgs-jblock (atj-gen-apkgs apkgs))
       (apkg-witness-jstatem (atj-gen-apkg-witness))
       (afns-jblock? (if deep$
                         (atj-gen-deep-afndefs afns)
                       nil))
       (validate-jblock? (and deep$
                              (list
                               (jstatem-expr
                                (jexpr-smethod (jtype-class
                                                "Acl2NamedFunction")
                                               "validateAll"
                                               nil)))))
       (initialize-jstatem (jstatem-expr
                            (jexpr-binary (jbinop-asg)
                                          (jexpr-name "initialized")
                                          (jexpr-literal
                                           (jliteral-boolean t)))))
       (jmethod-body (append (list if-jstatem)
                             apkgs-jblock
                             (list apkg-witness-jstatem)
                             afns-jblock?
                             validate-jblock?
                             (list initialize-jstatem))))
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
               :init (jliteral-boolean nil)))

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
                                            :type (jtype-class "Acl2Symbol")
                                            :name "function"))
       (jmethod-param-arguments (make-jparam :final? nil
                                             :type (jtype-array
                                                    (jtype-class "Acl2Value"))
                                             :name "arguments"))
       (jmethod-params (list jmethod-param-function
                             jmethod-param-arguments))
       (exception-message "The ACL2 environment is not initialized.")
       (exception-message-jexpr (atj-gen-jstring exception-message))
       (throw-jstatem (jstatem-throw (jexpr-newclass
                                      (jtype-class "IllegalStateException")
                                      (list exception-message-jexpr))))
       (if-jstatem (jstatem-if (jexpr-unary (junop-logcompl)
                                            (jexpr-name "initialized"))
                               (list throw-jstatem)))
       (function-jexpr (jexpr-smethod (jtype-class "Acl2NamedFunction")
                                      "make"
                                      (list (jexpr-name "function"))))
       (call-jexpr (jexpr-imethod function-jexpr
                                  "call"
                                  (list (jexpr-name "arguments"))))
       (return-jstatem (jstatem-return call-jexpr))
       (jmethod-body (list if-jstatem return-jstatem)))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type (jtype-class "Acl2Value"))
                  :name "call"
                  :params jmethod-params
                  :throws (list "Acl2EvaluationException")
                  :body jmethod-body)))

(define atj-gen-jclass ((apkgs string-listp)
                        (afns symbol-listp)
                        (deep$ booleanp)
                        (guards$ booleanp)
                        (java-class$ stringp)
                        (verbose$ booleanp)
                        state)
  :returns (jclass "A @(tsee jclassp).")
  :mode :program
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
               (afns-by-apkg (organize-fns-by-pkg afns+primitives)))
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

(defval *atj-jvar-fnname*
  :short "Name of the Java local variable used to store
          the function name of an ACL2 function call."
  "name"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-fnname*)))

(defval *atj-jvar-fnargs*
  :short "Name of the Java local variables used to store
          the array of argument values of an ACL2 function call."
  "arguments"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-fnargs*)))

(defval *atj-jvar-aresult*
  :short "Name of the Java local variables used to store
          the result of a test calculated in ACL2 (by ATJ)."
  "resultAcl2"
  ///
  (assert-event
   (atj-string-ascii-java-identifier-p *atj-jvar-aresult*)))

(defval *atj-jvar-jresult*
  :short "Name of the Java local variables used to store
          the result of a test calculated in Java (by AIJ)."
  "resultJava"
  ///
  (assert-event
   (atj-string-ascii-java-identifier-p *atj-jvar-jresult*)))

(define atj-gen-test-jmethod ((test$ atj-testp)
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
     and prints a message of success or failure.")
   (xdoc::p
    "We use an auxiliary recursive function to build the argument values.
     We initialize the local variable index for values to 1."))
  (b* (((atj-test test) test$)
       ((run-when verbose$)
        (cw "  ~s0~%" test.name))
       (jmethod-name (atj-gen-test-jmethod-name test.name))
       (message (str::cat "Testing '" test.name "'..."))
       (print-jstatem (jstatem-expr
                       (jexpr-imethod (jexpr-name "System.out")
                                      "print"
                                      (list (atj-gen-jstring message)))))
       (afnname-jexpr (atj-gen-asymbol test.function))
       (function-jlocvar (make-jlocvar :final? nil
                                       :type (jtype-class "Acl2Symbol")
                                       :name *atj-jvar-fnname*
                                       :init afnname-jexpr))
       ((mv aargs-jblock
            aargs-jexprs
            jvar-value-index) (atj-gen-test-jmethod-aux test.arguments 1))
       (aargs-jexpr (jexpr-newarray (jtype-class "Acl2Value") aargs-jexprs))
       (arguments-jlocvar (make-jlocvar :final? nil
                                        :type (jtype-array
                                               (jtype-class "Acl2Value"))
                                        :name *atj-jvar-fnargs*
                                        :init aargs-jexpr))
       ((mv ares-jblock
            ares-jexpr
            &) (atj-gen-avalue test.result jvar-value-index))
       (ares-jlocvar (make-jlocvar :final? nil
                                   :type (jtype-class "Acl2Value")
                                   :name *atj-jvar-aresult*
                                   :init ares-jexpr))
       (jres-jexpr (jexpr-smethod (jtype-class java-class$)
                                  "call"
                                  (list (jexpr-name *atj-jvar-fnname*)
                                        (jexpr-name *atj-jvar-fnargs*))))
       (jres-jlocvar (make-jlocvar :final? nil
                                   :type (jtype-class "Acl2Value")
                                   :name *atj-jvar-jresult*
                                   :init jres-jexpr))
       (print-pass-jstatem (jstatem-expr
                            (jexpr-imethod (jexpr-name "System.out")
                                           "println"
                                           (list (atj-gen-jstring "PASS")))))
       (print-fail-jstatem (jstatem-expr
                            (jexpr-imethod (jexpr-name "System.out")
                                           "println"
                                           (list (atj-gen-jstring "FAIL")))))
       (if-jstatem (jstatem-ifelse
                    (jexpr-imethod (jexpr-name *atj-jvar-aresult*)
                                   "equals"
                                   (list (jexpr-name *atj-jvar-jresult*)))
                    (list print-pass-jstatem)
                    (list print-fail-jstatem)))
       (jmethod-body (append (list print-jstatem)
                             (list (jstatem-locvar function-jlocvar))
                             aargs-jblock
                             (list (jstatem-locvar arguments-jlocvar))
                             ares-jblock
                             (list (jstatem-locvar ares-jlocvar))
                             (list (jstatem-locvar jres-jlocvar))
                             (list if-jstatem))))
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
                  :throws (list "Acl2EvaluationException")
                  :body jmethod-body))

  :prepwork
  ((define atj-gen-test-jmethod-aux ((aargs true-listp) (jvar-value-index posp))
     :returns (mv (jblock jblockp)
                  (jexprs jexpr-listp)
                  (new-jvar-value-index posp :hyp (posp jvar-value-index)))
     :parents nil
     (b* (((when (endp aargs)) (mv nil nil jvar-value-index))
          (aarg (car aargs))
          ((mv first-jblock
               first-jexpr
               jvar-value-index) (atj-gen-avalue aarg jvar-value-index))
          ((mv rest-jblock
               rest-jexprs
               jvar-value-index) (atj-gen-test-jmethod-aux (cdr aargs)
                                                           jvar-value-index)))
       (mv (append first-jblock rest-jblock)
           (cons first-jexpr rest-jexprs)
           jvar-value-index)))))

(define atj-gen-test-jmethods ((tests$ atj-test-listp)
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
          (atj-gen-test-jmethod (car tests$) java-class$ verbose$))
         (rest-jmethods
          (atj-gen-test-jmethods (cdr tests$) java-class$ verbose$)))
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
         (first-jstatem (jstatem-expr (jexpr-method jmethod-name nil)))
         (rest-jblock (atj-gen-run-tests (cdr tests$))))
      (cons first-jstatem rest-jblock))))

(define atj-gen-test-main-jmethod ((tests$ atj-test-listp)
                                   (java-class$ stringp))
  :returns (jmethod jmethodp)
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "This method initializes the ACL2 environment
     and then calls each test method."))
  (b* ((jmethod-param (make-jparam :final? nil
                                   :type (jtype-array (jtype-class "String"))
                                   :name "args"))
       (init-jstatem (jstatem-expr (jexpr-smethod (jtype-class java-class$)
                                                  "initialize"
                                                  nil)))
       (tests-jblock (atj-gen-run-tests tests$))
       (jmethod-body (cons init-jstatem
                           tests-jblock)))
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
                  :throws (list "Acl2EvaluationException")
                  :body jmethod-body)))

(define atj-gen-test-jclass ((tests$ atj-test-listp)
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
       (test-jmethods (atj-gen-test-jmethods tests$ java-class$ verbose$))
       (main-jmethod (atj-gen-test-main-jmethod tests$ java-class$)))
    (make-jclass :access (jaccess-public)
                 :abstract? nil
                 :static? nil
                 :final? nil
                 :strictfp? nil
                 :name (str::cat java-class$ "Tests")
                 :superclass? nil
                 :superinterfaces nil
                 :body (append (jmethods-to-jcmembers test-jmethods)
                               (list (jcmember-method main-jmethod))))))

(define atj-gen-jcunit ((deep$ booleanp)
                        (guards$ booleanp)
                        (java-package$ maybe-stringp)
                        (java-class$ maybe-stringp)
                        (apkgs string-listp)
                        (afns symbol-listp)
                        (verbose$ booleanp)
                        state)
  :returns (jcunit "A @(tsee jcunitp).")
  :mode :program
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

(define atj-gen-test-jcunit ((java-package$ maybe-stringp)
                             (java-class$ stringp)
                             (tests$ atj-test-listp)
                             (verbose$ booleanp))
  :returns (jcunit jcunitp)
  :short "Generate the test Java compilation unit."
  (make-jcunit :package? java-package$
               :imports (list (str::cat *atj-aij-jpackage* ".*")
                              "java.math.BigInteger")
               :types (list (atj-gen-test-jclass tests$ java-class$ verbose$))))

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

(define atj-gen-test-jfile ((java-package$ maybe-stringp)
                            (java-class$ stringp)
                            (output-file-test$ stringp)
                            (tests$ atj-test-listp)
                            (verbose$ booleanp)
                            state)
  :returns state
  :mode :program
  :short "Generate the test Java file."
  (print-to-jfile (print-jcunit (atj-gen-test-jcunit java-package$
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
                   (atj-gen-test-jfile java-package$
                                       java-class$
                                       output-file-test$
                                       tests$
                                       verbose$
                                       state)
                 state)))
     (value nil))))
