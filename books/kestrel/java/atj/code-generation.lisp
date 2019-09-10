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

(include-book "aij-notions")
(include-book "types")
(include-book "test-structures")
(include-book "pretty-printer")

(include-book "kestrel/std/basic/symbol-package-name-lst" :dir :system)
(include-book "kestrel/std/system/remove-mbe" :dir :system)
(include-book "kestrel/std/typed-alists/symbol-symbol-alistp" :dir :system)
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
    "We translate ACL2 values, terms, and lambda expressions
     to Java expressions ``preceded by'' Java blocks.
     By this we mean that the relevant code generation functions
     generally return a Java block and a Java expression,
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  (b* ((achars (explode astring)))
    (if (printable-charlist-p achars)
        (jexpr-literal-string astring)
      (jexpr-newclass (jtype-class "String")
                      (list
                       (jexpr-newarray-init (jtype-char)
                                            (atj-achars-to-jhexcodes
                                             achars)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jparamlist ((names string-listp) (jtypes jtype-listp))
  :guard (= (len names) (len jtypes))
  :returns (jparams jparam-listp)
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
                              :type (car jtypes)
                              :name (car names))
                 (atj-gen-jparamlist (cdr names) (cdr jtypes))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-achar ((achar characterp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 character."
  (jexpr-smethod *atj-jtype-char*
                 "make"
                 (list (jexpr-literal-character achar))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-astring ((astring stringp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 string."
  (jexpr-smethod *atj-jtype-string*
                 "make"
                 (list (atj-gen-jstring astring))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
    Overall, this makes the generated Java code faster.
    We introduce and use an alist to specify
    the correspondence between ACL2 symbols and AIJ static final fields.")
  (b* ((pair (assoc-eq asymbol *atj-gen-asymbol-alist*)))
    (if pair
        (jexpr-name (cdr pair))
      (jexpr-smethod *atj-jtype-symbol*
                     "make"
                     (list (atj-gen-jstring
                            (symbol-package-name asymbol))
                           (atj-gen-jstring
                            (symbol-name asymbol))))))

  :prepwork
  ((defval *atj-gen-asymbol-alist*
     '((t . "Acl2Symbol.T")
       (nil . "Acl2Symbol.NIL")
       (list . "Acl2Symbol.LIST")
       (if . "Acl2Symbol.IF")
       (characterp . "Acl2Symbol.CHARACTERP")
       (stringp . "Acl2Symbol.STRINGP")
       (symbolp . "Acl2Symbol.SYMBOLP")
       (integerp . "Acl2Symbol.INTEGERP")
       (rationalp . "Acl2Symbol.RATIONALP")
       (complex-rationalp . "Acl2Symbol.COMPLEX_RATIONALP")
       (acl2-numberp . "Acl2Symbol.ACL2_NUMBERP")
       (consp . "Acl2Symbol.CONSP")
       (char-code . "Acl2Symbol.CHAR_CODE")
       (code-char . "Acl2Symbol.CODE_CHAR")
       (coerce . "Acl2Symbol.COERCE")
       (intern-in-package-of-symbol . "Acl2Symbol.INTERN_IN_PACKAGE_OF_SYMBOL")
       (symbol-package-name . "Acl2Symbol.SYMBOL_PACKAGE_NAME")
       (symbol-name . "Acl2Symbol.SYMBOL_NAME")
       (pkg-imports . "Acl2Symbol.PKG_IMPORTS")
       (pkg-witness . "Acl2Symbol.PKG_WITNESS")
       (unary-- . "Acl2Symbol.UNARY_MINUS")
       (unary-/ . "Acl2Symbol.UNARY_SLASH")
       (binary-+ . "Acl2Symbol.BINARY_PLUS")
       (binary-* . "Acl2Symbol.BINARY_STAR")
       (< . "Acl2Symbol.LESS_THAN")
       (complex . "Acl2Symbol.COMPLEX")
       (realpart . "Acl2Symbol.REALPART")
       (imagpart . "Acl2Symbol.IMAGPART")
       (numerator . "Acl2Symbol.NUMERATOR")
       (denominator . "Acl2Symbol.DENOMINATOR")
       (cons . "Acl2Symbol.CONS")
       (car . "Acl2Symbol.CAR")
       (cdr . "Acl2Symbol.CDR")
       (equal . "Acl2Symbol.EQUAL")
       (bad-atom<= . "Acl2Symbol.BAD_ATOM_LESS_THAN_OR_EQUAL_TO")
       (or . "Acl2Symbol.OR"))
     ///
     (assert-event (symbol-string-alistp *atj-gen-asymbol-alist*)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-arational ((arational rationalp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 rational."
  (jexpr-smethod *atj-jtype-rational*
                 "make"
                 (list (atj-gen-ainteger (numerator arational))
                       (atj-gen-ainteger (denominator arational)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-anumber ((anumber acl2-numberp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 number."
  (jexpr-smethod *atj-jtype-number*
                 "make"
                 (list (atj-gen-arational (realpart anumber))
                       (atj-gen-arational (imagpart anumber)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-asymbols ((asymbols symbol-listp))
  :returns (jexprs jexpr-listp)
  :short "Lift @(tsee atj-gen-asymbol) to lists."
  (cond ((endp asymbols) nil)
        (t (cons (atj-gen-asymbol (car asymbols))
                 (atj-gen-asymbols (cdr asymbols))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-avar ((avar symbolp "The ACL2 variable."))
  :returns (jexpr jexprp)
  :short "Generate Java code to build a deeply embedded ACL2 variable."
  (jexpr-smethod *atj-jtype-var*
                 "make"
                 (list (atj-gen-asymbol avar))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-aformals ((aformals symbol-listp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build a deeply embedded formals parameter list
          of an ACL2 named function or lambda expression."
  :long
  (xdoc::topstring-p
   "The generated code builds an array of the formals as symbols.")
  (jexpr-newarray-init *atj-jtype-symbol*
                       (atj-gen-asymbols aformals)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-disallowed-jvar-names*
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
  (assert-event (string-listp *atj-disallowed-jvar-names*))
  (assert-event (no-duplicatesp-equal *atj-disallowed-jvar-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-avar ((avar symbolp)
                         (index natp)
                         (curr-apkg stringp)
                         (avars-by-name string-symbollist-alistp))
  :guard (not (equal curr-apkg ""))
  :returns (new-avar symbolp)
  :short "Rename an ACL2 variable to its Java name."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 variable is turned into a Java variable:
     either a local variable or a method parameter.
     This function renames an ACL2 variable
     so that its name (without the package prefix)
     can be directly used as the name of the Java variable.")
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
     we remove the variable being processed from them,
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
     if there is no package prefix.")
   (xdoc::p
    "We put the renamed variable in the current package (i.e. @('curr-apkg')).
     The choice of package is irrelevant, because the variables in a function
     are renamed in a way that their names are all distinct
     regardless of package prefixes.
     However, using the current package makes things uniform."))
  (b* ((apkg (symbol-package-name avar))
       (name (symbol-name avar))
       (omit-pname? (or (equal apkg curr-apkg)
                        (null (remove-eq
                               avar
                               (cdr (assoc-equal name avars-by-name))))))
       (pname$$$-jchars (if omit-pname?
                            nil
                          (append (atj-achars-to-jchars-id (explode apkg) t t)
                                  (list #\$ #\$ #\$))))
       (name-jchars (atj-achars-to-jchars-id (explode name)
                                             (endp pname$$$-jchars)
                                             t))
       ($$index-jchars (if (= index 0)
                           nil
                         (append (list #\$ #\$)
                                 (str::natchars index))))
       (jchars (append pname$$$-jchars name-jchars $$index-jchars))
       (new-name (implode jchars))
       (new-name (if (member-equal new-name *atj-disallowed-jvar-names*)
                     (str::cat new-name "$")
                   new-name)))
    (intern$ new-name curr-apkg)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-avars ((avars symbol-listp)
                          (indices symbol-nat-alistp)
                          (curr-apkg stringp)
                          (avars-by-name string-symbollist-alistp))
  :guard (not (equal curr-apkg ""))
  :returns (mv (renaming symbol-symbol-alistp :hyp (symbol-listp avars))
               (new-indices
                symbol-nat-alistp
                :hyp (and (symbol-listp avars)
                          (symbol-nat-alistp indices))))
  :short "Rename a sequence of ACL2 variables to their Java names."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-rename-avar),
     the shallowly embedded ACL2 variables are made unique via indices.
     There is an independent index for each ACL2 variable,
     so we use an alist from symbols to natural numbers
     to keep track of these indices.
     This alist is threaded through the functions
     that rename all the variables in ACL2 terms.")
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
     This function does that,
     and returns the renamed ACL2 variables as an alist
     from the old ACL2 variables to the new ACL2 variables,
     i.e. the renaming map.")
   (xdoc::p
    "Each ACL2 variable in the input list is processed as follows.
     If it has no index in the alist of indices,
     it has index 0,
     and the alist is extended to associate 1 (the next index) to the symbol.
     Otherwise, the index in the alist is used,
     and the alist is updated with the next index."))
  (b* (((when (endp avars)) (mv nil indices))
       (avar (car avars))
       (avar+index (assoc-eq avar indices))
       (index (if (consp avar+index) (cdr avar+index) 0))
       (indices (acons avar (1+ index) indices))
       ((mv renaming indices) (atj-rename-avars (cdr avars)
                                                indices
                                                curr-apkg
                                                avars-by-name)))
    (mv (acons avar
               (atj-rename-avar avar index curr-apkg avars-by-name)
               renaming)
        indices))
  :verify-guards :after-returns
  :prepwork
  ((defrulel verify-guards-lemma
     (implies (natp x)
              (acl2-numberp x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-aformals ((aformals symbol-listp)
                             (renaming symbol-symbol-alistp))
  :returns (new-aformals symbol-listp :hyp :guard)
  :short "Rename the formal parameters of
          a defined function or lambda expression
          according to a supplied renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used after calling @(tsee atj-rename-avars),
     which introduces the new names for the formal parameters.
     This function just looks up the names in the renaming alist
     and replaces them, returning a list of renamed parameters.")
   (xdoc::p
    "The reason for having this separate function,
     instead of having @(tsee atj-rename-avar)
     also return the new list of variables,
     is motivated by the way lambda expression are treated:
     see @(tsee atj-rename-aterm).
     As explained there, the formal parameters of a lambda expression
     that are the same as the correspoding actual parameters
     are excluded from the call of @(tsee atj-rename-avars),
     so that the old variable names can be re-used.
     Thus, we must use the combined renaming
     not only on the body of the lambda expression,
     but also on its formal parameters:
     this function does that for the formal parameters.
     For uniformity, this function is also used when processing
     a function definition, in order to rename the formal parameters
     in a way that is consistent with the renamings in the body."))
  (cond ((endp aformals) nil)
        (t (cons (cdr (assoc-eq (car aformals) renaming))
                 (atj-rename-aformals (cdr aformals) renaming))))
  ///

  (defrule len-of-atj-rename-aformals
    (equal (len (atj-rename-aformals aformals renaming))
           (len aformals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-rename-aterm
  :short "Rename all the ACL2 variables in an ACL2 term to their Java names."
  :long
  (xdoc::topstring
   (xdoc::p
    "At the top level,
     this function is called on the body of a defined ACL2 function
     prior to translating its body into Java.
     This makes the translation to Java,
     because each ACL2 variable can be turned
     into a Java variable with same name.
     In other words, we factor the overall translation from ACL2 to Java
     by performing the renaming of variables from ACL2 to ACL2 first,
     and then turning the resulting ACL2 into Java.")
   (xdoc::p
    "The alist from variables to indices
     is threaded through this function and its mutually recursive companion.
     On the other hand, the renaming alist is just passed down.")
   (xdoc::p
    "If the term is a variable, it is looked up in the renaming alist,
     and replaced with the renamed variable.
     Recall that new variable names are generated
     via @(tsee atj-rename-avar) and @(tsee atj-rename-avars),
     when variables are introduced,
     i.e. from formal parameters of defined functions and lambda expressions.
     When instead a variable occurrence is encountered in a term,
     it refers to the variable introduced in its surrounding scope,
     and thus the occurrence must be just replaced with the renamed variable.")
   (xdoc::p
    "If the term is a quoted constant, it is left unchanged.")
   (xdoc::p
    "If the term is a function application,
     its actual arguments are recursively processed,
     renaming all their variables.
     If the function is a named one, it is left unchanged.
     If instead it is a lambda expression,
     we introduce new variables renamings from its formal parameters,
     and then recursively process the body of the lambda expression.
     As an optimization,
     we exclude the formal parameters
     that are the same as their corresponding actual parameters
     (which happens often in ACL2: see @(tsee remove-unneeded-lambda-formals)),
     because for those we do not need to generate new Java variables,
     but can instead reference the existing variables.
     We append the newly generated renaming to the existing one,
     achieving the desired ``shadowing'' of the old mappings."))

  (define atj-rename-aterm ((aterm pseudo-termp)
                            (renaming symbol-symbol-alistp)
                            (indices symbol-nat-alistp)
                            (curr-apkg stringp)
                            (avars-by-name string-symbollist-alistp))
    :guard (not (equal curr-apkg ""))
    :returns (mv (new-aterm pseudo-termp
                            :hyp (and (pseudo-termp aterm)
                                      (symbol-symbol-alistp renaming)))
                 (new-indices symbol-nat-alistp
                              :hyp (and (pseudo-termp aterm)
                                        (symbol-nat-alistp indices))))
    (cond ((variablep aterm) (mv (cdr (assoc-eq aterm renaming)) indices))
          ((fquotep aterm) (mv aterm indices))
          (t (b* ((afn (ffn-symb aterm))
                  (aargs (fargs aterm))
                  ((mv new-aargs
                       indices) (atj-rename-aterms aargs
                                                   renaming
                                                   indices
                                                   curr-apkg
                                                   avars-by-name))
                  ((when (symbolp afn)) (mv (fcons-term afn new-aargs)
                                            indices))
                  (aformals (lambda-formals afn))
                  (abody (lambda-body afn))
                  (trimmed-aformals (remove-unneeded-lambda-formals
                                     aformals aargs))
                  ((mv new-renaming
                       indices) (atj-rename-avars trimmed-aformals
                                                  indices
                                                  curr-apkg
                                                  avars-by-name))
                  (renaming (append new-renaming renaming))
                  (new-aformals (atj-rename-aformals aformals renaming))
                  ((mv new-abody
                       indices) (atj-rename-aterm abody
                                                  renaming
                                                  indices
                                                  curr-apkg
                                                  avars-by-name)))
               (mv (fcons-term (make-lambda new-aformals new-abody)
                               new-aargs)
                   indices)))))

  (define atj-rename-aterms ((aterms pseudo-term-listp)
                             (renaming symbol-symbol-alistp)
                             (indices symbol-nat-alistp)
                             (curr-apkg stringp)
                             (avars-by-name string-symbollist-alistp))
    :guard (not (equal curr-apkg ""))
    :returns (mv (new-aterms (and (pseudo-term-listp new-aterms)
                                  (equal (len new-aterms) (len aterms)))
                             :hyp (and (pseudo-term-listp aterms)
                                       (symbol-symbol-alistp renaming)))
                 (new-indices symbol-nat-alistp
                              :hyp (and (pseudo-term-listp aterms)
                                        (symbol-nat-alistp indices))))
    (cond ((endp aterms) (mv nil indices))
          (t (b* (((mv new-aterm
                       indices) (atj-rename-aterm (car aterms)
                                                  renaming
                                                  indices
                                                  curr-apkg
                                                  avars-by-name))
                  ((mv new-aterms
                       indices) (atj-rename-aterms (cdr aterms)
                                                   renaming
                                                   indices
                                                   curr-apkg
                                                   avars-by-name)))
               (mv (cons new-aterm new-aterms)
                   indices)))))

  :prepwork

  ((defrulel consp-of-assoc-equal
     (implies (alistp x)
              (iff (consp (assoc-equal k x))
                   (assoc-equal k x))))

   (defrulel alistp-when-symbol-symbol-alistp
     (implies (symbol-symbol-alistp x)
              (alistp x)))

   (defrulel pseudo-termp-when-symbolp
     (implies (symbolp x)
              (pseudo-termp x)))

   (defrulel true-listp-when-alistp
     (implies (alistp x)
              (true-listp x))))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-rename-aterm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-aformals+abody ((aformals symbol-listp)
                                   (abody pseudo-termp)
                                   (curr-apkg stringp))
  :guard (not (equal curr-apkg ""))
  :returns (mv (new-aformals symbol-listp :hyp (symbol-listp aformals))
               (new-abody pseudo-termp :hyp (and (pseudo-termp abody)
                                                 (symbol-listp aformals))))
  :verify-guards nil
  :short "Rename all the ACL2 variables to their Java names,
          in the formal parameters and body of an ACL2 function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Starting with the empty alist of indices,
     we introduce renamed variables for the formal parameters.
     We use the renaming as the starting one to process the body."))
  (b* ((avars (union-eq aformals (all-free/bound-vars abody)))
       (avars-by-name (organize-symbols-by-name avars))
       ((mv renaming
            indices) (atj-rename-avars aformals nil curr-apkg avars-by-name))
       (new-aformals (atj-rename-aformals aformals renaming))
       ((mv new-abody &) (atj-rename-aterm
                          abody renaming indices curr-apkg avars-by-name)))
    (mv new-aformals new-abody)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-disallowed-jclass-names*
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
  (assert-event (string-listp *atj-disallowed-jclass-names*))
  (assert-event (no-duplicatesp-equal *atj-disallowed-jclass-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
     (see @(tsee *atj-disallowed-jclass-names*)).
     We also ensure that is is distinct from the main class generated.
     If the candidate Java class name is one of these,
     we add a @('$') at the end."))
  (b* ((jchars (atj-achars-to-jchars-id (explode apkg) t nil))
       (jstring (implode jchars))
       (jstring (if (or (member-equal jstring *atj-disallowed-jclass-names*)
                        (equal jstring java-class$))
                    (str::cat jstring "$")
                  jstring)))
    jstring))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-disallowed-jmethod-names*
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
  (assert-event (string-listp *atj-disallowed-jmethod-names*))
  (assert-event (no-duplicatesp-equal *atj-disallowed-jmethod-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-afnname ((afn symbolp) (curr-apkg stringp))
  :guard (not (equal curr-apkg ""))
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
     Thus, somewhat analogously to @(tsee atj-rename-avar),
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
                                         *atj-disallowed-jmethod-names*)
                           (rcons #\$ jmethod-jchars)
                         jmethod-jchars))
       (jchars (append jclass.-jchars jmethod-jchars))
       (jstring (implode jchars)))
    jstring)
  :prepwork
  ((local (include-book "std/typed-lists/character-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-let-bindings ((avars symbol-listp)
                                      (jexprs jexpr-listp)
                                      (types atj-type-listp))
  :guard (and (= (len jexprs) (len avars))
              (= (len types) (len avars)))
  :returns (jblock jblockp)
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
    "This function is called after renaming all the ACL2 variables
     so that their names are valid Java variable names.
     Thus, we directly use the names of the ACL2 variables.")
   (xdoc::p
    "The types of the local variables are passed as argument
     to this code generation function.
     See @(tsee atj-gen-shallow-alambda)."))
  (b* (((when (endp avars)) nil)
       (avar (car avars))
       (jexpr (car jexprs))
       (type (car types))
       (jvar (symbol-name avar))
       (first-jblock (jblock-locvar (atj-type-to-jtype type) jvar jexpr))
       (rest-jblock (atj-gen-shallow-let-bindings (cdr avars)
                                                  (cdr jexprs)
                                                  (cdr types))))
    (append first-jblock rest-jblock)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-adapt-jexpr-to-type ((jexpr jexprp)
                                 (src-type atj-typep)
                                 (dst-type atj-typep))
  :returns (new-jexpr jexprp :hyp (jexprp jexpr))
  :short "Adapt the source type of a Java expression
          to a destination type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when generating
     shallowly embedded ACL2 calls of named functions.
     As explained " (xdoc::seetopic "atj-types" "here") ",
     when the type of an actual argument of a function call
     is wider than the type of the formal argument,
     a cast is inserted in the generated Java code.")
   (xdoc::p
    "This code generation function does that.
     The input Java expression is the one generated for the actual argument,
     whose type is @('src-type') (for `source type').
     The input @('dst-type') (for `destination type')
     is the type of the corresponding formal argument.
     If the destination type is the same as or wider than the source type,
     the Java expression is returned unchanged.
     Otherwise, the expression is wrapped with
     a cast to the narrower destination type."))
  (if (atj-type-subeqp src-type dst-type)
      jexpr
    (jexpr-cast (atj-type-to-jtype dst-type) jexpr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-adapt-jexprs-to-types ((jexprs jexpr-listp)
                                   (src-types atj-type-listp)
                                   (dst-types atj-type-listp))
  :guard (and (= (len jexprs) (len src-types))
              (= (len jexprs) (len dst-types)))
  :returns (new-jexprs jexpr-listp :hyp (jexpr-listp jexprs))
  :short "Lift @(tsee atj-adapt-jexpr-to-type) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for all the arguments of a function call."))
  (cond ((endp jexprs) nil)
        (t (cons (atj-adapt-jexpr-to-type (car jexprs)
                                          (car src-types)
                                          (car dst-types))
                 (atj-adapt-jexprs-to-types (cdr jexprs)
                                            (cdr src-types)
                                            (cdr dst-types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-trim-alambda ((aformals symbol-listp)
                          (aargs pseudo-term-listp)
                          (jargs jexpr-listp)
                          (types atj-type-listp))
  :guard (and (= (len aformals) (len aargs))
              (= (len aargs) (len jargs))
              (= (len jargs) (len types)))
  :returns (mv (trimmed-aformals symbol-listp :hyp :guard)
               (trimmed-jargs jexpr-listp :hyp :guard)
               (trimmed-types atj-type-listp :hyp :guard))
  :short "Remove unneeded arguments from an ACL2 lambda expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "ACL2 lambda expressions are always closed,
     which means that often they include formal parameters
     that are replaced by themselves (i.e. by the same symbols)
     when the lambda expression is applied.
     For instance, the untranslated term @('(let ((x 0)) (+ x y))')
     is @('((lambda (x y) (binary-+ x y)) '3 y)') in translated form:
     the lambda expression includes the extra formal parameter @('y')
     which is not bound by the @(tsee let),
     applied to @('y') itself,
     making the lambda expression closed.")
   (xdoc::p
    "When generating shallowly embedded lambda expressions,
     to avoid generating Java local variables
     for formal parameters such as @('y') in the above example,
     we remove such parameters for consideration.
     This function does that.
     It removes not only the formal parameters from @('aformals')
     that are the same as the corresponding actual parameters @('aargs'),
     but it also removes the corresponding elements from @('jargs')
     (i.e. the Java expressions generated from @('aargs'))
     and from @('types') (i.e. the ATJ types of the actual arguments.
     These all come from @(tsee atj-gen-shallow-alambda):
     looking at that function and how it calls this function
     should make the purpose of this function clearer."))
  (cond ((endp aformals) (mv nil nil nil))
        (t (if (eq (car aformals) (car aargs))
               (atj-trim-alambda (cdr aformals)
                                 (cdr aargs)
                                 (cdr jargs)
                                 (cdr types))
             (b* (((mv rest-aformals
                       rest-jargs
                       rest-types) (atj-trim-alambda (cdr aformals)
                                                     (cdr aargs)
                                                     (cdr jargs)
                                                     (cdr types))))
               (mv (cons (car aformals) rest-aformals)
                   (cons (car jargs) rest-jargs)
                   (cons (car types) rest-types)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
     is an argument of these code generation functions.")
   (xdoc::p
    "As ACL2 terms are traversed and translated into Java,
     types are calculated for the ACL2 terms and used to determine
     the types to use for the generated Java local variables
     and any necessary Java type cast to be generated.
     See the discussion " (xdoc::seetopic "atj-types" "here") ".
     These types are returned as results by these code generation functions.
     If the @(':guards') input is @('nil'),
     all these types are always equal to the type of all ACL2 values,
     i.e. it is as if there were no types."))
  :verify-guards nil

  (define atj-gen-shallow-aifapp ((atest pseudo-termp)
                                  (athen pseudo-termp)
                                  (aelse pseudo-termp)
                                  (jvar-types symbol-atjtype-alistp)
                                  (jvar-value-base stringp)
                                  (jvar-value-index posp)
                                  (jvar-result-base stringp)
                                  (jvar-result-index posp)
                                  (curr-apkg stringp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :guard (not (equal curr-apkg ""))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (type "An @(tsee atj-typep).")
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
      "<type> <result> = null;"
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
       storing the result into the variable.")
     (xdoc::p
      "The type @('<type>') of the result variable is
       the least upper bound of the types of @('b') and @('c').
       This is also the type of this @(tsee if) term.
       The type of @('a') is ignored."))
    (b* (((mv test-jblock
              test-jexpr
              & ; test-type
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm atest
                                                        jvar-types
                                                        jvar-value-base
                                                        jvar-value-index
                                                        jvar-result-base
                                                        jvar-result-index
                                                        curr-apkg
                                                        guards$
                                                        wrld))
         ((mv else-jblock
              else-jexpr
              else-type
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm aelse
                                                        jvar-types
                                                        jvar-value-base
                                                        jvar-value-index
                                                        jvar-result-base
                                                        jvar-result-index
                                                        curr-apkg
                                                        guards$
                                                        wrld))
         ((mv then-jblock
              then-jexpr
              then-type
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm athen
                                                        jvar-types
                                                        jvar-value-base
                                                        jvar-value-index
                                                        jvar-result-base
                                                        jvar-result-index
                                                        curr-apkg
                                                        guards$
                                                        wrld))
         (type (atj-type-join else-type then-type))
         (jtype (atj-type-to-jtype type))
         ((mv result-locvar-jblock jvar-result jvar-result-index)
          (atj-gen-jlocvar-indexed jtype
                                   jvar-result-base
                                   jvar-result-index
                                   (jexpr-literal-null)))
         (if-jblock (jblock-ifelse
                     (jexpr-imethod (jexpr-name "Acl2Symbol.NIL")
                                    "equals"
                                    (list test-jexpr))
                     (append else-jblock
                             (jblock-asg-name jvar-result else-jexpr))
                     (append then-jblock
                             (jblock-asg-name jvar-result then-jexpr))))
         (jblock (append test-jblock
                         result-locvar-jblock
                         if-jblock))
         (jexpr (jexpr-name jvar-result)))
      (mv jblock
          jexpr
          type
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
                                  (jvar-types symbol-atjtype-alistp)
                                  (jvar-value-base stringp)
                                  (jvar-value-index posp)
                                  (jvar-result-base stringp)
                                  (jvar-result-index posp)
                                  (curr-apkg stringp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :guard (not (equal curr-apkg ""))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (type "An @(tsee atj-typep).")
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
      "<type> <result> = null;"
      "if (Acl2Symbol.NIL.equals(<a-expr>)) {"
      "    <b-blocks>"
      "    <result> = <b-expr>;"
      "} else {"
      "    <result> = <a-expr>;"
      "}")
     (xdoc::p
      "and the Java expression @('<result>').")
     (xdoc::p
      "The type @('<type>') of the result variable is
       the least upper bound of the types of @('a') and @('b').
       This is also the type of this @(tsee or) term."))
    (b* (((mv first-jblock
              first-jexpr
              first-type
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm afirst
                                                        jvar-types
                                                        jvar-value-base
                                                        jvar-value-index
                                                        jvar-result-base
                                                        jvar-result-index
                                                        curr-apkg
                                                        guards$
                                                        wrld))
         ((mv second-jblock
              second-jexpr
              second-type
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm asecond
                                                        jvar-types
                                                        jvar-value-base
                                                        jvar-value-index
                                                        jvar-result-base
                                                        jvar-result-index
                                                        curr-apkg
                                                        guards$
                                                        wrld))
         (type (atj-type-join first-type second-type))
         (jtype (atj-type-to-jtype type))
         ((mv result-locvar-jblock jvar-result jvar-result-index)
          (atj-gen-jlocvar-indexed jtype
                                   jvar-result-base
                                   jvar-result-index
                                   (jexpr-literal-null)))
         (if-jblock (jblock-ifelse
                      (jexpr-imethod (jexpr-name "Acl2Symbol.NIL")
                                     "equals"
                                     (list first-jexpr))
                      (append second-jblock
                              (jblock-asg-name jvar-result second-jexpr))
                      (jblock-asg-name jvar-result first-jexpr)))
         (jblock (append first-jblock
                         result-locvar-jblock
                         if-jblock))
         (jexpr (jexpr-name jvar-result)))
      (mv jblock
          jexpr
          type
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
                                  (jvar-types symbol-atjtype-alistp)
                                  (jvar-value-base stringp)
                                  (jvar-value-index posp)
                                  (jvar-result-base stringp)
                                  (jvar-result-index posp)
                                  (curr-apkg stringp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :guard (not (equal curr-apkg ""))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (type "An @(tsee atj-typep).")
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
       (We treat the Java abstract syntax somewhat improperly here,
       by using a generic method call with a possibly qualified method name,
       which should be therefore a static method call;
       this still produces correct Java code,
       but it should be handled more properly
       in a future version of this implementation.)
       If the type of an actual argument
       is wider than the type of a formal argument,
       we generate a cast (see @(tsee atj-adapt-jexpr-to-type));
       the types of the actual arguments are recursively calculated,
       while the types of the formal arguments are retrieved from
       the @(tsee def-atj-function-type) table.
       The type of the function call is the output type of the function,
       which is retrieved from the @(tsee def-atj-function-type) table.")
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
                                        jvar-types
                                        jvar-value-base
                                        jvar-value-index
                                        jvar-result-base
                                        jvar-result-index
                                        curr-apkg
                                        guards$
                                        wrld)
              (atj-gen-shallow-aifapp afirst
                                      asecond
                                      athird
                                      jvar-types
                                      jvar-value-base
                                      jvar-value-index
                                      jvar-result-base
                                      jvar-result-index
                                      curr-apkg
                                      guards$
                                      wrld))))
         ((mv args-jblock
              arg-jexprs
              arg-types
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterms aargs
                                                         jvar-types
                                                         jvar-value-base
                                                         jvar-value-index
                                                         jvar-result-base
                                                         jvar-result-index
                                                         curr-apkg
                                                         guards$
                                                         wrld))
         ((when (symbolp afn))
          (b* (((mv type arg-jexprs)
                (if guards$
                    (b* ((afn-type (atj-get-function-type afn wrld))
                         (arg-jexprs (atj-adapt-jexprs-to-types
                                      arg-jexprs
                                      arg-types
                                      (atj-function-type->inputs afn-type)))
                         (type (atj-function-type->output afn-type)))
                      (mv type arg-jexprs))
                  (mv :value arg-jexprs))))
            (mv args-jblock
                (jexpr-method (atj-gen-shallow-afnname afn curr-apkg)
                              arg-jexprs)
                type
                jvar-value-index
                jvar-result-index)))
         ((mv lambda-jblock
              lambda-jexpr
              lambda-type
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-alambda (lambda-formals afn)
                                                          (lambda-body afn)
                                                          aargs
                                                          arg-jexprs
                                                          arg-types
                                                          jvar-types
                                                          jvar-value-base
                                                          jvar-value-index
                                                          jvar-result-base
                                                          jvar-result-index
                                                          curr-apkg
                                                          guards$
                                                          wrld)))
      (mv (append args-jblock
                  lambda-jblock)
          lambda-jexpr
          lambda-type
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
                                   (types atj-type-listp)
                                   (jvar-types symbol-atjtype-alistp)
                                   (jvar-value-base stringp)
                                   (jvar-value-index posp)
                                   (jvar-result-base stringp)
                                   (jvar-result-index posp)
                                   (curr-apkg stringp)
                                   (guards$ booleanp)
                                   (wrld plist-worldp))
    :guard (and (= (len aargs) (len aformals))
                (= (len jargs) (len aformals))
                (= (len types) (len aformals))
                (not (equal curr-apkg "")))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (type "An @(tsee atj-typep).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Generate a shallowly embedded ACL2 lambda expression,
            applied to given Java expressions as arguments."
    :long
    (xdoc::topstring
     (xdoc::p
      "We remove the formal parameters
       (and the corresponding arguments and types)
       that are the same as the actual arguments
       (see @(tsee atj-trim-alambda)).
       We update the type alist with associations
       for the (remaining) variables introduced by the lambda expression:
       the types of these variables
       are the types of the expressions assigned to them;
       by appending the new associations in front of the existing alist,
       we obtain the desired ``overwriting''.
       We generate @(tsee let) bindings for these variables.
       Finally, we generate Java code for the body of the lambda expression."))
    (b* (((mv aformals jargs types)
          (atj-trim-alambda aformals aargs jargs types))
         (jvar-types (append (pairlis$ aformals types) jvar-types))
         (let-jblock (atj-gen-shallow-let-bindings aformals
                                                   jargs
                                                   types))
         ((mv body-jblock
              body-jexpr
              body-type
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-aterm abody
                                                        jvar-types
                                                        jvar-value-base
                                                        jvar-value-index
                                                        jvar-result-base
                                                        jvar-result-index
                                                        curr-apkg
                                                        guards$
                                                        wrld)))
      (mv (append let-jblock body-jblock)
          body-jexpr
          body-type
          jvar-value-index
          jvar-result-index))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-SHALLOW-ATERM decreases:
    :measure (two-nats-measure (acl2-count abody) 1))

  (define atj-gen-shallow-aterm ((aterm pseudo-termp)
                                 (jvar-types symbol-atjtype-alistp)
                                 (jvar-value-base stringp)
                                 (jvar-value-index posp)
                                 (jvar-result-base stringp)
                                 (jvar-result-index posp)
                                 (curr-apkg stringp)
                                 (guards$ booleanp)
                                 (wrld plist-worldp))
    :guard (not (equal curr-apkg ""))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (type "An @(tsee atj-typep).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Generate a shallowly embedded ACL2 term."
    :long
    (xdoc::topstring
     (xdoc::p
      "Prior to calling this function, we rename all the ACL2 variables
       so that they have the right names as Java variables.
       Thus, if the ACL2 term is a variable,
       we generate a Java variable with the same name.
       Its type is in the type alist.")
     (xdoc::p
      "If the ACL2 term is a quoted constant,
       we represent it as its value.
       Its type is determined by the value."))
    (cond ((variablep aterm) (mv nil
                                 (jexpr-name (symbol-name aterm))
                                 (cdr (assoc-eq aterm jvar-types))
                                 jvar-value-index
                                 jvar-result-index))
          ((fquotep aterm) (b* (((mv jblock jexpr jvar-value-index)
                                 (atj-gen-avalue (unquote aterm)
                                                 jvar-value-base
                                                 jvar-value-index)))
                             (mv jblock
                                 jexpr
                                 (atj-type-of-value (unquote aterm))
                                 jvar-value-index
                                 jvar-result-index)))
          (t (atj-gen-shallow-afnapp (ffn-symb aterm)
                                     (fargs aterm)
                                     jvar-types
                                     jvar-value-base
                                     jvar-value-index
                                     jvar-result-base
                                     jvar-result-index
                                     curr-apkg
                                     guards$
                                     wrld)))
    :measure (two-nats-measure (acl2-count aterm) 0))

  (define atj-gen-shallow-aterms ((aterms pseudo-term-listp)
                                  (jvar-types symbol-atjtype-alistp)
                                  (jvar-value-base stringp)
                                  (jvar-value-index posp)
                                  (jvar-result-base stringp)
                                  (jvar-result-index posp)
                                  (curr-apkg stringp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :guard (not (equal curr-apkg ""))
    :returns (mv (jblock jblockp)
                 (jexpr jexpr-listp)
                 (types "An @(tsee atj-type-listp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Lift @(tsee atj-gen-shallow-aterm) to lists."
    (if (endp aterms)
        (mv nil nil nil jvar-value-index jvar-result-index)
      (b* (((mv first-jblock
                first-jexpr
                first-type
                jvar-value-index
                jvar-result-index) (atj-gen-shallow-aterm (car aterms)
                                                          jvar-types
                                                          jvar-value-base
                                                          jvar-value-index
                                                          jvar-result-base
                                                          jvar-result-index
                                                          curr-apkg
                                                          guards$
                                                          wrld))
           ((mv rest-jblock
                rest-jexprs
                rest-types
                jvar-value-index
                jvar-result-index) (atj-gen-shallow-aterms (cdr aterms)
                                                           jvar-types
                                                           jvar-value-base
                                                           jvar-value-index
                                                           jvar-result-base
                                                           jvar-result-index
                                                           curr-apkg
                                                           guards$
                                                           wrld)))
        (mv (append first-jblock rest-jblock)
            (cons first-jexpr rest-jexprs)
            (cons first-type rest-types)
            jvar-value-index
            jvar-result-index)))
    :measure (two-nats-measure (acl2-count aterms) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-apkg-name ((apkg stringp))
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
  (b* ((pair (assoc-equal apkg *atj-gen-apkg-name-alist*)))
    (if pair
        (jexpr-name (cdr pair))
      (jexpr-smethod *atj-jtype-pkg-name*
                     "make"
                     (list (atj-gen-jstring apkg)))))

  :prepwork
  ((defval *atj-gen-apkg-name-alist*
     '(("KEYWORD"             . "Acl2PackageName.KEYWORD")
       ("COMMON-LISP"         . "Acl2PackageName.LISP")
       ("ACL2"                . "Acl2PackageName.ACL2")
       ("ACL2-OUTPUT-CHANNEL" . "Acl2PackageName.ACL2_OUTPUT")
       ("ACL2-INPUT-CHANNEL"  . "Acl2PackageName.ACL2_INPUT")
       ("ACL2-PC"             . "Acl2PackageName.ACL2_PC")
       ("ACL2-USER"           . "Acl2PackageName.ACL2_USER")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-apkg-jmethods ((apkgs string-listp) (verbose$ booleanp))
  :returns (jmethods jmethod-listp)
  :short "Generate all the Java methods that add the ACL2 package definitions."
  (if (endp apkgs)
      nil
    (b* ((first-jmethod (atj-gen-apkg-jmethod (car apkgs) verbose$))
         (rest-jmethods (atj-gen-apkg-jmethods (cdr apkgs) verbose$)))
      (cons first-jmethod rest-jmethods))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-afnnative ((afn symbolp)
                                   (guards$ booleanp)
                                   (curr-apkg stringp)
                                   (wrld plist-worldp))
  :guard (and (atj-aij-nativep afn)
              (equal (symbol-package-name afn) curr-apkg)
              (not (equal curr-apkg "")))
  :verify-guards nil
  :returns (jmethod jmethodp)
  :short "Generate a shallowly embedded ACL2 function
          that is natively implemented in AIJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "AIJ's @('Acl2NativeFunction') class provides native Java implementations
     of certain ACL2 functions, as public static Java methods.
     Thus, in the shallow embedding approach,
     we could translate references to these ACL2 functions
     to the names of those public static Java methods.
     However, for greater uniformity and readability,
     we generate wrapper Java methods
     for these natively implemented ACL2 functions.
     The names of these methods are constructed in the same way as
     the Java methods for the non-natively implemented ACL2 functions.
     These methods reside in the Java classes generated for
     the ACL2 packages of the ACL2 functions.")
   (xdoc::p
    "For each of these natively implemented ACL2 functions,
     @('Acl2NativeFunction') has a corresponding Java method
     that takes @('Acl2Value') objects as arguments.
     For some of these functions,
     @('Acl2NativeFunction') also has a variant Java method implementation
     that takes argument objects of narrower types,
     based on the guards of the functions:
     these Java methods have @('UnderGuard') in their names.
     For each of the latter functions,
     the generated wrapper Java methods
     call one or the other variant implementation
     based on the ATJ input and output types
     retrieved from the @(tsee def-atj-function-type) table.
     If the @(':guards') input is @('nil'),
     the table is not consulted,
     and @(':value') is the type of every input and output.
     If instead the @(':guards') is @('t'),
     then the narrower types are used
     only if the file @('types-for-natives.lisp') is included
     prior to calling ATJ;
     otherwise, @(':value') is the type of every input and output."))
  (b* ((jmethod-name (atj-gen-shallow-afnname afn curr-apkg))
       (jmethod-param-names
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
       ((mv afn-in-types
            afn-out-type) (if guards$
                              (b* ((afn-type (atj-get-function-type afn wrld)))
                                (mv (atj-function-type->inputs afn-type)
                                    (atj-function-type->output afn-type)))
                            (mv (repeat (len jmethod-param-names) :value)
                                :value)))
       (jmethod-params (atj-gen-jparamlist jmethod-param-names
                                           (atj-types-to-jtypes afn-in-types)))
       (jcall-method-name
        (case afn
          (characterp "execCharacterp")
          (stringp "execStringp")
          (symbolp "execSymbolp")
          (integerp "execIntegerp")
          (rationalp "execRationalp")
          (complex-rationalp "execComplexRationalp")
          (acl2-numberp "execAcl2Numberp")
          (consp "execConsp")
          (char-code (if (equal afn-in-types '(:character))
                         "execCharCodeUnderGuard"
                       "execCharCode"))
          (code-char (if (equal afn-in-types '(:integer))
                         "execCodeCharUnderGuard"
                       "execCodeChar"))
          (coerce (if (equal afn-in-types '(:value :symbol))
                      "execCoerceUnderGuard"
                    "execCoerce"))
          (intern-in-package-of-symbol
           (if (equal afn-in-types '(:string :symbol))
               "execInternInPackageOfSymbolUnderGuard"
             "execInternInPackageOfSymbol"))
          (symbol-package-name (if (equal afn-in-types '(:symbol))
                                   "execSymbolPackageNameUnderGuard"
                                 "execSymbolPackageName"))
          (symbol-name (if (equal afn-in-types '(:symbol))
                           "execSymbolNameUnderGuard"
                         "execSymbolName"))
          (pkg-imports (if (equal afn-in-types '(:string))
                           "execPkgImportsUnderGuard"
                         "execPkgImports"))
          (pkg-witness (if (equal afn-in-types '(:string))
                           "execPkgWitnessUnderGuard"
                         "execPkgWitness"))
          (unary-- (if (equal afn-in-types '(:number))
                       "execUnaryMinusUnderGuard"
                     "execUnaryMinus"))
          (unary-/ (if (equal afn-in-types '(:number))
                       "execUnarySlashUnderGuard"
                     "execUnarySlash"))
          (binary-+ (if (equal afn-in-types '(:number :number))
                        "execBinaryPlusUnderGuard"
                      "execBinaryPlus"))
          (binary-* (if (equal afn-in-types '(:number :number))
                        "execBinaryStarUnderGuard"
                      "execBinaryStar"))
          (< (if (equal afn-in-types '(:rational :rational))
                 "execLessThanUnderGuard"
               "execLessThan"))
          (complex (if (equal afn-in-types '(:rational :rational))
                       "execComplexUnderGuard"
                     "execComplex"))
          (realpart (if (equal afn-in-types '(:number))
                        "execRealPartUnderGuard"
                      "execRealPart"))
          (imagpart (if (equal afn-in-types '(:number))
                        "execImagPartUnderGuard"
                      "execImagPart"))
          (numerator (if (equal afn-in-types '(:rational))
                         "execNumeratorUnderGuard"
                       "execNumerator"))
          (denominator (if (equal afn-in-types '(:rational))
                           "execDenominatorUnderGuard"
                         "execDenominator"))
          (cons "execCons")
          (car "execCar")
          (cdr "execCdr")
          (equal "execEqual")
          (bad-atom<= "execBadAtomLessThanOrEqualTo")
          (if "execIf")
          (t (impossible))))
       (jcall-arg-jexprs (jexpr-name-list jmethod-param-names))
       (jcall (jexpr-smethod *atj-jtype-native-fn*
                             jcall-method-name
                             jcall-arg-jexprs))
       (jmethod-body (jblock-return jcall)))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type (atj-type-to-jtype afn-out-type))
                  :name jmethod-name
                  :params jmethod-params
                  :throws (list *atj-jclass-eval-exc*)
                  :body jmethod-body))
  :guard-hints (("Goal" :in-theory (enable atj-aij-nativep primitivep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-afndef ((afn symbolp)
                                (guards$ booleanp)
                                (verbose$ booleanp)
                                (curr-apkg stringp)
                                state)
  :guard (and (equal (symbol-package-name afn) curr-apkg)
              (not (equal curr-apkg "")))
  :returns (jmethod jmethodp)
  :verify-guards nil
  :short "Generate a shallowly embedded ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 function definition is turned into a Java method.
     This is a public static method
     with the same number of parameters as the ACL2 function.")
   (xdoc::p
    "If the @(':guards') input is @('nil'),
     all the method's parameters and the method's result
     have type @('Acl2Value').
     If instead @(':guards') is @('t'),
     the parameter and result types are determined from
     the ACL2 function's input and output types,
     retrieved from the @(tsee def-atj-function-type) table.
     If the type of the body of the ACL2 function is wider than
     the output type of the function,
     a cast is inserted in the @('return') statement.")
   (xdoc::p
    "Prior to shallowly embedding the ACL2 function body,
     all the calls of @(tsee mbe) are replaced with
     their @(':logic') or @(':exec') parts (based on @(':guards'))
     in the function's body.")
   (xdoc::p
    "After that, we rename all the ACL2 variables
     in the formal parameters and body of the ACL2 function
     so that their names are valid Java variable names.
     This simplifies the subsequent translation to Java,
     which can just use the names of the ACL2 variables
     as names for the corresponding Java variables.")
   (xdoc::p
    "Finally, we turn the body of the ACL2 function
     into Java statements and a Java expression,
     which constitute the shallow embedding of the ACL2 function body;
     the indices for the Java local variables
     for constructing values and results are initialized to 1,
     since we are at the top level here.
     We use @('$value') and @('$result') as the base names
     for the Java local variables to build values and results,
     so that they do not conflict with each other
     or with the Java local variables generated from the ACL2 variables,
     none of which starts with a @('$') not followed by two hexadecimal digits.
     The body of the Java method consists of those Java statements,
     followed by a @('return') statement with that Java expression."))
  (b* ((wrld (w state))
       ((run-when verbose$)
        (cw "  ~s0~%" afn))
       (jmethod-name (atj-gen-shallow-afnname afn curr-apkg))
       (aformals (formals afn wrld))
       (abody (getpropc afn 'unnormalized-body))
       (abody (if guards$
                  (remove-mbe-logic-from-term abody)
                (remove-mbe-exec-from-term abody)))
       ((mv aformals abody) (atj-rename-aformals+abody aformals abody curr-apkg))
       ((mv afn-in-types
            afn-out-type) (if guards$
                              (b* ((afn-type (atj-get-function-type afn wrld)))
                                (mv (atj-function-type->inputs afn-type)
                                    (atj-function-type->output afn-type)))
                            (mv (repeat (len aformals) :value)
                                :value)))
       (jvar-types (pairlis$ aformals afn-in-types))
       (jmethod-params (atj-gen-jparamlist (symbol-name-lst aformals)
                                           (atj-types-to-jtypes afn-in-types)))
       ((mv abody-jblock abody-jexpr abody-type & &)
        (atj-gen-shallow-aterm abody
                               jvar-types
                               "$value" 1
                               "$result" 1
                               curr-apkg
                               guards$
                               wrld))
       (abody-jexpr (atj-adapt-jexpr-to-type
                     abody-jexpr abody-type afn-out-type))
       (jmethod-body (append abody-jblock
                             (jblock-return abody-jexpr))))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type (atj-type-to-jtype afn-out-type))
                  :name jmethod-name
                  :params jmethod-params
                  :throws (list *atj-jclass-eval-exc*)
                  :body jmethod-body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-afn ((afn symbolp)
                             (guards$ booleanp)
                             (verbose$ booleanp)
                             (curr-apkg stringp)
                             state)
  :guard (and (equal (symbol-package-name afn) curr-apkg)
              (not (equal curr-apkg "")))
  :returns (jmethod jmethodp)
  :verify-guards nil
  :short "Generate a shallowly embedded
          ACL2 function natively implemented in AIJ
          or ACL2 function definition."
  (if (atj-aij-nativep afn)
      (atj-gen-shallow-afnnative afn guards$ curr-apkg (w state))
    (atj-gen-shallow-afndef afn guards$ verbose$ curr-apkg state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-afns ((afns symbol-listp)
                              (guards$ booleanp)
                              (verbose$ booleanp)
                              (curr-apkg stringp)
                              state)
  :guard (and (equal (symbol-package-name-lst afns)
                     (repeat (len afns) curr-apkg))
              (not (equal curr-apkg "")))
  :returns (jmethods jmethod-listp)
  :verify-guards nil
  :short "Lift @(tsee atj-gen-shallow-afn) to lists."
  (cond ((endp afns) nil)
        (t (b* ((first-jmethod (atj-gen-shallow-afn (car afns)
                                                    guards$
                                                    verbose$
                                                    curr-apkg
                                                    state))
                (rest-jmethods (atj-gen-shallow-afns (cdr afns)
                                                     guards$
                                                     verbose$
                                                     curr-apkg
                                                     state)))
             (cons first-jmethod rest-jmethods)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-afns-by-apkg ((afns-by-apkg string-symbollist-alistp)
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
      (afns-by-apkg string-symbollist-alistp)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
     In the latter case, we ensure that
     the ACL2 functions natively implemented in AIJ are included
     (currently the ACL2 primitive functions),
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
          (b* ((afns+natives
                (remove-duplicates-eq
                 (append afns
                         (strip-cars *primitive-formals-and-guards*))))
               (afns-by-apkg (organize-symbols-by-pkg afns+natives)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-jmethod ((test$ atj-testp)
                              (deep$ booleanp)
                              (java-class$ stringp)
                              (verbose$ booleanp)
                              (wrld plist-worldp))
  :returns (jmethod jmethodp)
  :verify-guards nil
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
       (fn-type (atj-get-function-type test.function wrld))
       (in-types (atj-function-type->inputs fn-type))
       ((mv shallow-arg-jblock shallow-arg-jvars)
        (if deep$
            (mv nil nil)
          (atj-gen-test-jmethod-aux aargs-jexprs in-types 1)))
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
                                     (types atj-type-listp)
                                     (index posp))
     :guard (= (len aargs-jexprs) (len types))
     :returns (mv (jblock jblockp)
                  (jvars string-listp))
     (cond ((endp aargs-jexprs) (mv nil nil))
           (t (b* ((first-jvar (str::cat "argument" (str::natstr index)))
                   (first-type (car types))
                   (first-jtype (atj-type-to-jtype first-type))
                   (first-jexpr (jexpr-cast (atj-type-to-jtype first-type)
                                            (car aargs-jexprs)))
                   (first-jblock (jblock-locvar first-jtype
                                                first-jvar
                                                first-jexpr))
                   ((mv rest-jblock rest-jvars)
                    (atj-gen-test-jmethod-aux (cdr aargs-jexprs)
                                              (cdr types)
                                              (1+ index))))
                (mv (append first-jblock rest-jblock)
                    (cons first-jvar rest-jvars))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-jmethods ((tests$ atj-test-listp)
                               (deep$ booleanp)
                               (java-class$ stringp)
                               (verbose$ booleanp)
                               (wrld plist-worldp))
  :returns (jmethods jmethod-listp)
  :verify-guards nil
  :short "Generate all the Java methods to run the specified tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are generated only if the @(':tests') input is not @('nil')."))
  (if (endp tests$)
      nil
    (b* ((first-jmethod
          (atj-gen-test-jmethod (car tests$) deep$ java-class$ verbose$ wrld))
         (rest-jmethods
          (atj-gen-test-jmethods (cdr tests$) deep$ java-class$ verbose$ wrld)))
      (cons first-jmethod rest-jmethods))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-jclass ((tests$ atj-test-listp)
                             (deep$ booleanp)
                             (java-class$ stringp)
                             (verbose$ booleanp)
                             (wrld plist-worldp))
  :returns (jclass jclassp)
  :verify-guards nil
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
       (test-jmethods (atj-gen-test-jmethods
                       tests$ deep$ java-class$ verbose$ wrld))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-jcunit ((deep$ booleanp)
                             (java-package$ maybe-stringp)
                             (java-class$ stringp)
                             (tests$ atj-test-listp)
                             (verbose$ booleanp)
                             (wrld plist-worldp))
  :returns (jcunit jcunitp)
  :verify-guards nil
  :short "Generate the test Java compilation unit."
  (make-jcunit :package? java-package$
               :imports (list (str::cat *atj-aij-jpackage* ".*")
                              "java.math.BigInteger")
               :types (list (atj-gen-test-jclass
                             tests$ deep$ java-class$ verbose$ wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
                                                     verbose$
                                                     (w state)))
                  output-file-test$
                  state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
