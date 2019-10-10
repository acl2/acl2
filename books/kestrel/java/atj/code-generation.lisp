; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

; Avoid failure for atj-gen-number in ACL2(r):
; cert_param: non-acl2r

(include-book "aij-notions")
(include-book "types")
(include-book "test-structures")
(include-book "pretty-printer")
(include-book "pre-translation")
(include-book "post-translation")
(include-book "primitives")
(include-book "name-translation")

(include-book "kestrel/std/basic/organize-symbols-by-pkg" :dir :system)
(include-book "kestrel/std/basic/symbol-package-name-lst" :dir :system)
(include-book "kestrel/std/system/pseudo-termfnp" :dir :system)
(include-book "kestrel/std/system/ubody" :dir :system)
(include-book "kestrel/std/typed-alists/symbol-string-alistp" :dir :system)

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
     The other functions are generally used for both approaches.")
   (xdoc::p
    "The code generation process consists of "
    (xdoc::seetopic "atj-pre-translation" "a pre-translation from ACL2 to ACL2")
    ", followed by a translation from ACL2 to Java,
     followed by "
    (xdoc::seetopic "atj-post-translation"
                    "a post-translation from Java to Java")
    ". The pre-translation turns the ACL2 code into a form
     that is closer to the target Java code,
     thus making the translation simpler.
     The correctness of the pre-translation can be formally proved within ACL2,
     without involving (the semantics of) Java.
     The post-translation makes some improvements directly on the Java code."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-chars-to-jhexcodes ((chars character-listp))
  :returns (jexprs jexpr-listp)
  :short "Turn a list of ACL2 characters
          into a list of Java hexadecimal literal expressions
          corresponding to the character codes,
          in the same order."
  (cond ((endp chars) nil)
        (t (cons (jexpr-literal
                  (make-jliteral-integer :value (char-code (car chars))
                                         :long? nil
                                         :base (jintbase-hexadecimal)))
                 (atj-chars-to-jhexcodes (cdr chars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jstring ((string stringp))
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
  (b* ((chars (explode string)))
    (if (printable-charlist-p chars)
        (jexpr-literal-string string)
      (jexpr-newclass (jtype-class "String")
                      (list
                       (jexpr-newarray-init (jtype-char)
                                            (atj-chars-to-jhexcodes
                                             chars)))))))

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

(define atj-gen-char ((char characterp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 character."
  (jexpr-smethod *atj-jtype-char*
                 "make"
                 (list (jexpr-literal-character char))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-string ((string stringp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 string."
  (jexpr-smethod *atj-jtype-string*
                 "make"
                 (list (atj-gen-jstring string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-symbol ((symbol symbolp))
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
  (b* ((pair (assoc-eq symbol *atj-gen-symbol-alist*)))
    (if pair
        (jexpr-name (cdr pair))
      (jexpr-smethod *atj-jtype-symbol*
                     "make"
                     (list (atj-gen-jstring
                            (symbol-package-name symbol))
                           (atj-gen-jstring
                            (symbol-name symbol))))))

  :prepwork
  ((defval *atj-gen-symbol-alist*
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
     (assert-event (symbol-string-alistp *atj-gen-symbol-alist*)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-integer ((integer integerp))
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
  (b* (((when (= integer 0)) (jexpr-name "Acl2Integer.ZERO"))
       ((when (= integer 1)) (jexpr-name "Acl2Integer.ONE"))
       (arg (cond ((signed-byte-p 32 integer)
                   (if (< integer 0)
                       (jexpr-unary (junop-uminus)
                                    (jexpr-literal-integer-decimal
                                     (- integer)))
                     (jexpr-literal-integer-decimal integer)))
                  ((signed-byte-p 64 integer)
                   (if (< integer 0)
                       (jexpr-unary (junop-uminus)
                                    (jexpr-literal-integer-long-decimal
                                     (- integer)))
                     (jexpr-literal-integer-long-decimal integer)))
                  (t (b* ((string (if (< integer 0)
                                      (str::cat "-" (str::natstr (- integer)))
                                    (str::natstr integer))))
                       (jexpr-newclass (jtype-class "BigInteger")
                                       (list
                                        (jexpr-literal-string string))))))))
    (jexpr-smethod *atj-jtype-int*
                   "make"
                   (list arg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-rational ((rational rationalp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 rational."
  (jexpr-smethod *atj-jtype-rational*
                 "make"
                 (list (atj-gen-integer (numerator rational))
                       (atj-gen-integer (denominator rational)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-number ((number acl2-numberp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build an ACL2 number."
  (jexpr-smethod *atj-jtype-number*
                 "make"
                 (list (atj-gen-rational (realpart number))
                       (atj-gen-rational (imagpart number)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-gen-value
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
   (xdoc::@def "atj-gen-value")
   (xdoc::@def "atj-gen-conspair"))

  (define atj-gen-conspair ((conspair consp)
                            (jvar-value-base stringp)
                            (jvar-value-index posp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index)))
    :parents nil
    (b* (((unless (mbt (consp conspair)))
          (mv nil (jexpr-name "irrelevant") jvar-value-index))
         ((mv car-jblock
              car-jexpr
              jvar-value-index) (atj-gen-value (car conspair)
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
              jvar-value-index) (atj-gen-value (cdr conspair)
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
    :measure (two-nats-measure (acl2-count conspair) 0))

  (define atj-gen-value (value
                         (jvar-value-base stringp)
                         (jvar-value-index posp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index)))
    :parents nil
    (cond ((characterp value) (mv nil
                                  (atj-gen-char value)
                                  jvar-value-index))
          ((stringp value) (mv nil
                               (atj-gen-string value)
                               jvar-value-index))
          ((symbolp value) (mv nil
                               (atj-gen-symbol value)
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
          ((consp value) (atj-gen-conspair value
                                           jvar-value-base
                                           jvar-value-index))
          (t (prog2$ (raise "Internal error: the value ~x0 is a bad atom."
                            value)
                     (mv nil (jexpr-name "irrelevant") jvar-value-index))))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-CONSPAIR decreases:
    :measure (two-nats-measure (acl2-count value) 1))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-gen-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-values ((values true-listp)
                        (jvar-value-base stringp)
                        (jvar-value-index posp))
  :returns (mv (jblock jblockp)
               (jexprs jexpr-listp)
               (new-jvar-value-index posp :hyp (posp jvar-value-index)))
  :short "Lift @(tsee atj-gen-value) to lists."
  (cond ((endp values) (mv nil nil jvar-value-index))
        (t (b* (((mv first-jblock
                     first-jexpr
                     jvar-value-index) (atj-gen-value (car values)
                                                      jvar-value-base
                                                      jvar-value-index))
                ((mv rest-jblock
                     rest-jexrps
                     jvar-value-index) (atj-gen-values (cdr values)
                                                       jvar-value-base
                                                       jvar-value-index)))
             (mv (append first-jblock rest-jblock)
                 (cons first-jexpr rest-jexrps)
                 jvar-value-index)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-symbols ((symbols symbol-listp))
  :returns (jexprs jexpr-listp)
  :short "Lift @(tsee atj-gen-symbol) to lists."
  (cond ((endp symbols) nil)
        (t (cons (atj-gen-symbol (car symbols))
                 (atj-gen-symbols (cdr symbols))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-qconst
  ((qconst "(Unquoted) value of the ACL2 quoted constant.")
   (jvar-value-base stringp)
   (jvar-value-index posp))
  :returns (mv (jblock jblockp)
               (jexpr jexprp)
               (new-jvar-value-index posp :hyp (posp jvar-value-index)))
  :short "Generate Java code to build a deeply embedded ACL2 quoted constant."
  (b* (((mv value-jblock
            value-jexpr
            jvar-value-index) (atj-gen-value qconst
                                             jvar-value-base
                                             jvar-value-index))
       (jblock value-jblock)
       (jexpr (jexpr-smethod *atj-jtype-qconst*
                             "make"
                             (list value-jexpr))))
    (mv jblock jexpr jvar-value-index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-var ((var symbolp "The ACL2 variable."))
  :returns (jexpr jexprp)
  :short "Generate Java code to build a deeply embedded ACL2 variable."
  (jexpr-smethod *atj-jtype-var*
                 "make"
                 (list (atj-gen-symbol var))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-formals ((formals symbol-listp))
  :returns (jexpr jexprp)
  :short "Generate Java code to build a deeply embedded formals parameter list
          of an ACL2 named function or lambda expression."
  :long
  (xdoc::topstring-p
   "The generated code builds an array of the formals as symbols.")
  (jexpr-newarray-init *atj-jtype-symbol*
                       (atj-gen-symbols formals)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-gen-deep-term-fns
  :short "Functions to generate Java code to build deeply embedded ACL2 terms."

  (define atj-gen-deep-fnapp ((fn pseudo-termfnp)
                              (args pseudo-term-listp)
                              (jvar-value-base stringp)
                              (jvar-value-index posp)
                              (jvar-term-base stringp)
                              (jvar-term-index posp)
                              (jvar-lambda-base stringp)
                              (jvar-lambda-index posp)
                              (guards$ booleanp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index))
                 (new-jvar-term-index posp :hyp (posp jvar-term-index))
                 (new-jvar-lambda-index posp :hyp (posp jvar-lambda-index)))
    :parents (atj-code-generation atj-gen-deep-term-fns)
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
    (b* (((mv fn args)
          (if (and (eq fn 'if)
                   (= (len args) 3)
                   (equal (first args) (second args)))
              (mv 'or (list (first args) (third args)))
            (mv fn args)))
         ((mv fn-jblock
              fn-jexpr
              jvar-value-index
              jvar-term-index
              jvar-lambda-index)
          (if (symbolp fn)
              (mv nil
                  (jexpr-smethod *atj-jtype-named-fn*
                                 "make"
                                 (list (atj-gen-symbol fn)))
                  jvar-value-index
                  jvar-term-index
                  jvar-lambda-index)
            (atj-gen-deep-lambda (lambda-formals fn)
                                 (lambda-body fn)
                                 jvar-value-base
                                 jvar-value-index
                                 jvar-term-base
                                 jvar-term-index
                                 jvar-lambda-base
                                 jvar-lambda-index
                                 guards$)))
         ((mv args-jblock
              arg-jexprs
              jvar-value-index
              jvar-term-index
              jvar-lambda-index) (atj-gen-deep-terms args
                                                     jvar-value-base
                                                     jvar-value-index
                                                     jvar-term-base
                                                     jvar-term-index
                                                     jvar-lambda-base
                                                     jvar-lambda-index
                                                     guards$))
         (args-jexpr (jexpr-newarray-init *atj-jtype-term* arg-jexprs))
         (fnapp-jexpr (jexpr-smethod *atj-jtype-fn-app*
                                     "make"
                                     (list fn-jexpr
                                           args-jexpr)))
         ((mv fnapp-locvar-jblock
              fnapp-jvar
              jvar-term-index) (atj-gen-jlocvar-indexed *atj-jtype-term*
                                                        jvar-term-base
                                                        jvar-term-index
                                                        fnapp-jexpr)))
      (mv (append fn-jblock
                  args-jblock
                  fnapp-locvar-jblock)
          (jexpr-name fnapp-jvar)
          jvar-value-index
          jvar-term-index
          jvar-lambda-index))
    ;; 2nd component is greater then the one of ATJ-GEN-DEEP-LAMBDA
    ;; so that the call of ATJ-GEN-DEEP-LAMBDA decreases
    ;; even when FN is a non-symbol atom (impossible under the guard):
    :measure (two-nats-measure (+ (acl2-count fn) (acl2-count args)) 2))

  (define atj-gen-deep-lambda ((formals symbol-listp)
                               (body pseudo-termp)
                               (jvar-value-base stringp)
                               (jvar-value-index posp)
                               (jvar-term-base stringp)
                               (jvar-term-index posp)
                               (jvar-lambda-base stringp)
                               (jvar-lambda-index posp)
                               (guards$ booleanp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index))
                 (new-jvar-term-index posp :hyp (posp jvar-term-index))
                 (new-jvar-lambda-index posp :hyp (posp jvar-lambda-index)))
    :parents (atj-code-generation atj-gen-deep-term-fns)
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
    (b* ((formals-jexpr (atj-gen-deep-formals formals))
         ((mv body-jblock
              body-jexpr
              jvar-value-index
              jvar-term-index
              jvar-lambda-index) (atj-gen-deep-term body
                                                    jvar-value-base
                                                    jvar-value-index
                                                    jvar-term-base
                                                    jvar-term-index
                                                    jvar-lambda-base
                                                    jvar-lambda-index
                                                    guards$))
         (lambda-jexpr (jexpr-smethod *atj-jtype-lambda*
                                      "make"
                                      (list formals-jexpr
                                            body-jexpr)))
         ((mv lambda-locvar-jblock
              lambda-jvar
              jvar-lambda-index) (atj-gen-jlocvar-indexed
                                  *atj-jtype-lambda*
                                  jvar-lambda-base
                                  jvar-lambda-index
                                  lambda-jexpr)))
      (mv (append body-jblock
                  lambda-locvar-jblock)
          (jexpr-name lambda-jvar)
          jvar-value-index
          jvar-term-index
          jvar-lambda-index))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-DEEP-TERM decreases:
    :measure (two-nats-measure (acl2-count body) 1))

  (define atj-gen-deep-term ((term pseudo-termp)
                             (jvar-value-base stringp)
                             (jvar-value-index posp)
                             (jvar-term-base stringp)
                             (jvar-term-index posp)
                             (jvar-lambda-base stringp)
                             (jvar-lambda-index posp)
                             (guards$ booleanp))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index))
                 (new-jvar-term-index posp :hyp (posp jvar-term-index))
                 (new-jvar-lambda-index posp :hyp (posp jvar-lambda-index)))
    :parents (atj-code-generation atj-gen-deep-term-fns)
    :short "Generate Java code to build a deeply embedded ACL2 term."
    (cond ((variablep term) (mv nil
                                (atj-gen-deep-var term)
                                jvar-value-index
                                jvar-term-index
                                jvar-lambda-index))
          ((fquotep term) (b* (((mv jblock
                                    jexpr
                                    jvar-value-index)
                                (atj-gen-deep-qconst (unquote term)
                                                     jvar-value-base
                                                     jvar-value-index)))
                            (mv jblock
                                jexpr
                                jvar-value-index
                                jvar-term-index
                                jvar-lambda-index)))
          (t (atj-gen-deep-fnapp (ffn-symb term)
                                 (fargs term)
                                 jvar-value-base
                                 jvar-value-index
                                 jvar-term-base
                                 jvar-term-index
                                 jvar-lambda-base
                                 jvar-lambda-index
                                 guards$)))
    :measure (two-nats-measure (acl2-count term) 0))

  (define atj-gen-deep-terms ((terms pseudo-term-listp)
                              (jvar-value-base stringp)
                              (jvar-value-index posp)
                              (jvar-term-base stringp)
                              (jvar-term-index posp)
                              (jvar-lambda-base stringp)
                              (jvar-lambda-index posp)
                              (guards$ booleanp))
    :returns (mv (jblock jblockp)
                 (jexprs jexpr-listp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index))
                 (new-jvar-term-index posp :hyp (posp jvar-term-index))
                 (new-jvar-lambda-index posp :hyp (posp jvar-lambda-index)))
    :parents (atj-code-generation atj-gen-deep-term-fns)
    :short "Lift @(tsee atj-gen-deep-term) to lists."
    (if (endp terms)
        (mv nil
            nil
            jvar-value-index
            jvar-term-index
            jvar-lambda-index)
      (b* (((mv first-jblock
                jexpr
                jvar-value-index
                jvar-term-index
                jvar-lambda-index) (atj-gen-deep-term (car terms)
                                                      jvar-value-base
                                                      jvar-value-index
                                                      jvar-term-base
                                                      jvar-term-index
                                                      jvar-lambda-base
                                                      jvar-lambda-index
                                                      guards$))
           ((mv rest-jblock
                jexprs
                jvar-value-index
                jvar-term-index
                jvar-lambda-index) (atj-gen-deep-terms (cdr terms)
                                                       jvar-value-base
                                                       jvar-value-index
                                                       jvar-term-base
                                                       jvar-term-index
                                                       jvar-lambda-base
                                                       jvar-lambda-index
                                                       guards$)))
        (mv (append first-jblock
                    rest-jblock)
            (cons jexpr jexprs)
            jvar-value-index
            jvar-term-index
            jvar-lambda-index)))
    :measure (two-nats-measure (acl2-count terms) 0))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-gen-deep-term
    :hints (("Goal" :in-theory (enable pseudo-termfnp acl2::pseudo-lambdap)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fnname ((fn symbolp)
                                (pkg-class-names string-string-alistp)
                                (fn-method-names symbol-string-alistp)
                                (curr-pkg stringp))
  :guard (not (equal curr-pkg ""))
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
     not dissmilarly to @('<pkg>::<fn>') in ACL2.
     However, inside @('<jclass>'), it suffices to use @('<jmethod>'),
     which is more readable.
     Thus, we prepend the Java class name to the Java method name
     if and only if the current ACL2 package (the @('curr-pkg') argument)
     differs from the ACL2 function's package.")
   (xdoc::p
    "The Java class name @('<jclass>') is looked up
     in the alist @('pkg-class-names'),
     and the Java method name @('<jmethod>') is looked up
      in the alist @('fn-method-names')."))
  (b* ((pkg (symbol-package-name fn))
       (jclass? (if (equal pkg curr-pkg)
                    ""
                  (b* ((pair (assoc-equal pkg pkg-class-names))
                       ((unless (consp pair))
                        (raise "Internal error: ~
                                no class name for package name ~x0." pkg)
                        "")
                       (jclass (cdr pair)))
                    (str::cat jclass "."))))
       (pair (assoc-eq fn fn-method-names))
       ((unless (consp pair))
        (raise "Internal error: no method name for function ~x0." fn)
        "")
       (jmethod (cdr pair)))
    (str::cat jclass? jmethod)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-let-bindings ((vars symbol-listp)
                                      (jblocks jblock-listp)
                                      (jexprs jexpr-listp))
  :guard (and (int= (len jblocks) (len vars))
              (int= (len jexprs) (len vars)))
  :returns (jblock jblockp :hyp (jblock-listp jblocks))
  :verify-guards nil
  :short "Generate shallowly embedded ACL2 @(tsee let) bindings."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     ACL2 lambda expressions (i.e. @(tsee let)s)
     are handled by assigning the Java expressions
     generated from the actual parameters of the lambda expression
     to Java local variables corresponding to the formal parameters.
     This function generates these bindings,
     given the ACL2 variables that are the formal arguments
     and the Java expressions to assign to them.
     Each binding is preceded by the block (if any)
     generated for the corresponding actual argument of the lambda expression.")
   (xdoc::p
    "Prior to calling this function,
     the variables of all the lambda expressiona have been marked
     as `new' or `old' via @(tsee atj-mark-term).
     We extract this mark and use it to generate
     either a variable declaration with initializer (for `new')
     or an assignment to an existing variable (for `old').")
   (xdoc::p
    "Prior to calling this function,
     the variables of all the lambda expressions have been annotated
     via @(tsee atj-type-annotate-term).
     Thus, each ACL2 variable name carries its own type,
     which we use to determine the Java type of the Java variable.")
   (xdoc::p
    "Prior to calling this function,
     the variables of all the lambda expressions have been renamed
     via @(tsee atj-rename-term).
     Thus, we directly turn each ACL2 variable into a Java variable name
     (after removing the type annotations)."))
  (b* (((when (endp vars)) nil)
       (var (car vars))
       (jexpr (car jexprs))
       ((mv var new?) (atj-unmark-var var))
       ((mv var type) (atj-type-unannotate-var var))
       (jvar (symbol-name var))
       (var-jblock (if new?
                       (jblock-locvar (atj-type-to-jtype type) jvar jexpr)
                     (jblock-asg (jexpr-name jvar) jexpr)))
       (first-jblock (append (car jblocks) var-jblock))
       (rest-jblock (atj-gen-shallow-let-bindings (cdr vars)
                                                  (cdr jblocks)
                                                  (cdr jexprs))))
    (append first-jblock rest-jblock)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-convert-jexpr-from-jint-to-value ((jexpr jexprp))
  :returns (new-jexpr jexprp)
  :short "Convert a Java expression from type @('int') to type @('Acl2Value')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee atj-adapt-jexpr-to-type),
     when the source ATJ type is @(':jint')
     and the destination ATJ type is @(':value').
     In ACL2, Java @('int') values are represented as
     values satisfying @(tsee int-value-p):
     this function converts the Java @('int') returned by the expression
     to the Java @('Acl2Value') that represents
     the ACL2 representation of the Java @('int') value.")
   (xdoc::p
    "The representation is explicated and checked "
    (xdoc::seetopic "atj-jint-representation-check" "here")
    ". We create an @('Acl2Integer') from the @('int'),
     and then a list of length 2 (as two @('Acl2ConsPair')s)
     whose first element is the @('Acl2Symbol') for the keyword @(':int')
     and whose second element is the @('Acl2Integer')."))
  (b* ((acl2-integer-jexpr (jexpr-smethod *atj-jtype-int*
                                          "make"
                                          (list jexpr)))
       (acl2-symbol-nil-jexpr (jexpr-name "Acl2Symbol.NIL"))
       (acl2-inner-cons-jexpr (jexpr-smethod *atj-jtype-cons*
                                             "make"
                                             (list acl2-integer-jexpr
                                                   acl2-symbol-nil-jexpr)))
       (acl2-keyword-int-jexpr (jexpr-smethod *atj-jtype-symbol*
                                              "makeKeyword"
                                              (list
                                               (jexpr-literal-string "INT"))))
       (acl2-outer-cons-jexpr (jexpr-smethod *atj-jtype-cons*
                                             "make"
                                             (list acl2-keyword-int-jexpr
                                                   acl2-inner-cons-jexpr))))
    acl2-outer-cons-jexpr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-convert-jexpr-from-value-to-jint ((jexpr jexprp))
  :returns (new-jexpr jexprp)
  :short "Convert a Java expression from type @('Acl2Value') to type @('int')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee atj-adapt-jexpr-to-type),
     when the source ATJ type is @(':value')
     and the destination ATJ type is @(':jint').
     In ACL2, Java @('int') values are represented as
     values satisfying @(tsee int-value-p):
     this function converts the Java @('Acl2Value') returned by the expression
     to the Java @('int') that is represented by
     the @('Acl2Value') in ACL2.")
   (xdoc::p
    "Assuming guard verification,
     the argument of this function should always be
     an expression that returns an @('Acl2Value') with the right representation,
     i.e. the representation explicated and checked "
    (xdoc::seetopic "atj-jint-representation-check" "here")
    ". We cast the @('Acl2Value') to a @('Acl2ConsPair'),
     get its @(tsee cdr),
     cast that to @('Acl2ConsPair'),
     get its @(tsee car),
     cast it to @('Acl2Integer'),
     and get its numeric value as an @('int')."))
  (b* ((acl2-outer-cons-jexpr (jexpr-paren (jexpr-cast *atj-jtype-cons* jexpr)))
       (acl2-cdr-jexpr (jexpr-imethod acl2-outer-cons-jexpr "getCdr" nil))
       (acl2-inner-cons-jexpr (jexpr-paren
                               (jexpr-cast *atj-jtype-cons* acl2-cdr-jexpr)))
       (acl2-car-jexpr (jexpr-imethod acl2-inner-cons-jexpr "getCar" nil))
       (acl2-integer-jexpr (jexpr-paren
                            (jexpr-cast *atj-jtype-int* acl2-car-jexpr))))
    (jexpr-imethod acl2-integer-jexpr "getJavaInt" nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-adapt-jexpr-to-type ((jexpr jexprp)
                                 (src-type atj-typep)
                                 (dst-type atj-typep))
  :returns (new-jexpr jexprp :hyp (jexprp jexpr))
  :short "Adapt a Java expression from a source type to a destination type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when generating
     shallowly embedded ACL2 calls of named functions.
     As explained " (xdoc::seetopic "atj-types" "here") ",
     when the type of an actual argument of a function call
     is not the same as or a subtype (in Java) of
     the type of the formal argument,
     ATJ adds Java code to convert from the former type to the latter type.
     Note that being a subtype in Java is not the same as
     satisfying @(tsee atj-type-subeqp),
     which only corresponds to subtyping (i.e. inclusion) in ACL2.")
   (xdoc::p
    "This code generation function does that.
     The input Java expression is the one generated for the actual argument,
     whose type is @('src-type') (for `source type').
     The input @('dst-type') (for `destination type')
     is the type of the corresponding formal argument.")
   (xdoc::p
    "To convert from @(':jint') to any other type
     we first convert to @(':value')
     via @(tsee atj-convert-jexpr-from-jint-to-value),
     and then we cast to the other type
     (unless the other type is already @(':value')).
     To convert to @(':jint') from any other type,
     we use @(tsee atj-convert-jexpr-from-value-to-jint);
     note that any other type is a subtype of @('Acl2Value') in Java,
     so there is not need for casts.
     To convert between the AIJ types,
     if the source type is a subtype of or the same type as
     the destination type (checked via @(tsee atj-type-subeqp)),
     we leave the expression unchanged;
     otherwise, we insert a cast to the destination type,
     which is expected to always succeed
     under the assumption of guard verification."))
  (cond ((eq src-type dst-type) jexpr)
        ((eq src-type :jint)
         (b* ((acl2-value-jexpr (atj-convert-jexpr-from-jint-to-value jexpr)))
           (if (eq dst-type :value)
               acl2-value-jexpr
             (jexpr-cast (atj-type-to-jtype dst-type) acl2-value-jexpr))))
        ((eq dst-type :jint)
         (atj-convert-jexpr-from-value-to-jint jexpr))
        ((atj-type-subeqp src-type dst-type) jexpr)
        (t (jexpr-cast (atj-type-to-jtype dst-type) jexpr))))

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

(defval *atj-gen-cond-exprs*
  :short "Flag saying whether ATJ should attempt to
          generate Java conditional expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an internal flag, developer-oriented.
     If @('t'), ATJ will generate shallowly embedded
     Java conditional expressions @('... ? ... : ...')
     under suitable conditions;
     see the code generation functions that reference this flag.")
   (xdoc::p
    "This flag is currently @('nil'),
     because, with the current tests,
     the code looked less readable overall
     then when this flag is @('t').
     This flag may be removed eventually."))
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-gen-shallow-term-fns
  :short "Functions to generate shallowly embedded ACL2 terms."
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
    "These code generation functions assume that the ACL2 terms
     have been type-annotated via @(tsee atj-type-annotate-term).
     They also assume that all the variables of the ACL2 terms have been marked
     via @(tsee atj-mark-var-new) and @(tsee atj-mark-var-old),
     and renamed via @(tsee atj-rename-term).
     If the @(':guards') input is @('nil'),
     then all the type annotations consist of
     the type @(':value') of all ACL2 values,
     i.e. it is as if there were no types."))
  :verify-guards nil

  (define atj-gen-shallow-ifapp ((test pseudo-termp)
                                 (then pseudo-termp)
                                 (else pseudo-termp)
                                 (type atj-typep)
                                 (jvar-value-base stringp)
                                 (jvar-value-index posp)
                                 (jvar-result-base stringp)
                                 (jvar-result-index posp)
                                 (pkg-class-names string-string-alistp)
                                 (fn-method-names symbol-string-alistp)
                                 (curr-pkg stringp)
                                 (guards$ booleanp)
                                 (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
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
      "<a-block>"
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
       derived from the ATJ type passed to this code generation function.
       See @(tsee atj-gen-shallow-fnapp) for details.")
     (xdoc::p
      "If the flag @(tsee *atj-gen-cond-exprs*) is set,
       and if both @('<b-block>') and @('<c-block>') are empty,
       we generate the Java block")
     (xdoc::codeblock
      "<a-block>")
     (xdoc::p
      "and the Java expression")
     (xdoc::codeblock
      "Acl2Symbol.NIL.equals(<a-expr>) ? <c-expr> : <b-expr>"))
    (b* (((mv test-jblock
              test-jexpr
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-term test
                                                       jvar-value-base
                                                       jvar-value-index
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       guards$
                                                       wrld))
         ((mv else-jblock
              else-jexpr
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-term else
                                                       jvar-value-base
                                                       jvar-value-index
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       guards$
                                                       wrld))
         ((mv then-jblock
              then-jexpr
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-term then
                                                       jvar-value-base
                                                       jvar-value-index
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       guards$
                                                       wrld))
         ((when (and *atj-gen-cond-exprs*
                     (null then-jblock)
                     (null else-jblock)))
          (b* ((jblock test-jblock)
               (jexpr (jexpr-cond (jexpr-imethod (jexpr-name "Acl2Symbol.NIL")
                                                 "equals"
                                                 (list test-jexpr))
                                  else-jexpr
                                  then-jexpr)))
            (mv jblock
                jexpr
                jvar-value-index
                jvar-result-index)))
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
          jvar-value-index
          jvar-result-index))
    ;; 2nd component is non-0
    ;; so that each call of ATJ-GEN-SHALLOW-TERM decreases
    ;; even when the ACL2-COUNTs of the other two addends are 0:
    :measure (two-nats-measure (+ (acl2-count test)
                                  (acl2-count then)
                                  (acl2-count else))
                               1))

  (define atj-gen-shallow-orapp ((first pseudo-termp)
                                 (second pseudo-termp)
                                 (type atj-typep)
                                 (jvar-value-base stringp)
                                 (jvar-value-index posp)
                                 (jvar-result-base stringp)
                                 (jvar-result-index posp)
                                 (pkg-class-names string-string-alistp)
                                 (fn-method-names symbol-string-alistp)
                                 (curr-pkg stringp)
                                 (guards$ booleanp)
                                 (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 @('or') application."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is for the @('or') ACL2 ``pseudo-function''
       (see the AIJ documentation for details).
       We treat @('(or a b)') non-strictly like @('(if a a b)'),
       but we avoid calculating @('a') twice.
       Somewhat similarly to how we treat @(tsee if),
       we generate the Java block")
     (xdoc::codeblock
      "<a-block>"
      "<type> <result> = <a-expr>;"
      "if (Acl2Symbol.NIL.equals(<result>)) {"
      "    <b-blocks>"
      "    <result> = <b-expr>;")
     (xdoc::p
      "and the Java expression @('<result>')."))
    (b* (((mv first-jblock
              first-jexpr
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-term first
                                                       jvar-value-base
                                                       jvar-value-index
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       guards$
                                                       wrld))
         ((mv second-jblock
              second-jexpr
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-term second
                                                       jvar-value-base
                                                       jvar-value-index
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       guards$
                                                       wrld))
         (jtype (atj-type-to-jtype type))
         ((mv result-locvar-jblock jvar-result jvar-result-index)
          (atj-gen-jlocvar-indexed jtype
                                   jvar-result-base
                                   jvar-result-index
                                   first-jexpr))
         (if-jblock (jblock-if
                     (jexpr-imethod (jexpr-name "Acl2Symbol.NIL")
                                    "equals"
                                    (list (jexpr-name jvar-result)))
                     (append second-jblock
                             (jblock-asg-name jvar-result second-jexpr))))
         (jblock (append first-jblock
                         result-locvar-jblock
                         if-jblock))
         (jexpr (jexpr-name jvar-result)))
      (mv jblock
          jexpr
          jvar-value-index
          jvar-result-index))
    ;; 2nd component is non-0
    ;; so that each call of ATJ-GEN-SHALLOW-TERM decreases
    ;; even when the ACL2-COUNT of the other addend is 0:
    :measure (two-nats-measure (+ (acl2-count first)
                                  (acl2-count second))
                               1))

  (define atj-gen-shallow-intvalapp ((arg pseudo-termp)
                                     (src-type atj-typep)
                                     (dst-type atj-typep)
                                     (jvar-value-base stringp)
                                     (jvar-value-index posp)
                                     (jvar-result-base stringp)
                                     (jvar-result-index posp)
                                     (pkg-class-names string-string-alistp)
                                     (fn-method-names symbol-string-alistp)
                                     (curr-pkg stringp)
                                     (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 (@tsee int-val) application."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the function @(tsee int-value) is treated specially.
       If the argument is a quoted natural number,
       the function application is translated
       to the corresponding Java integer literal;
       the assumption of guard verification ensures that
       the literal is not too large.
       If the argument is a quoted negative integer,
       the function application is translated to a Java unary minus expression
       whose argument is the literal corresponding to the negation of @('x');
       the assumption of guard verification ensures that
       the literal is not too large.
       If the argument is not a quoted integer,
       we translate it to a Java expression,
       which will have the type @(':integer') required by @(tsee int-value);
       we then wrap the expression with code
       to convert it to the Java type @('int').")
     (xdoc::p
      "Note that we are dealing with annotated terms,
       so the argument of @(tsee int-value) must be unwrapped
       to be examined."))
    (b* (((mv arg & &) (atj-type-unwrap-term arg))
         ((unless arg) ; for termination proof
          (mv nil (jexpr-name "dummy") jvar-value-index jvar-result-index)))
      (if (and (quotep arg)
               (integerp (unquote arg)))
          (b* ((int (unquote-term arg))
               (jexpr (if (>= int 0)
                          (jexpr-literal-integer-decimal int)
                        (jexpr-unary (junop-uminus)
                                     (jexpr-literal-integer-decimal
                                      (- int)))))
               (jexpr (atj-adapt-jexpr-to-type jexpr :jint dst-type)))
            (mv nil
                (atj-adapt-jexpr-to-type jexpr src-type dst-type)
                jvar-value-index
                jvar-result-index))
        (b* (((mv arg-jblock
                  arg-jexpr
                  jvar-value-index
                  jvar-result-index) (atj-gen-shallow-term arg
                                                           jvar-value-base
                                                           jvar-value-index
                                                           jvar-result-base
                                                           jvar-result-index
                                                           pkg-class-names
                                                           fn-method-names
                                                           curr-pkg
                                                           t ; GUARDS$
                                                           wrld))
             (jexpr (atj-adapt-jexpr-to-type arg-jexpr :integer :jint)))
          (mv arg-jblock
              (atj-adapt-jexpr-to-type jexpr src-type dst-type)
              jvar-value-index
              jvar-result-index))))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count arg)
                               1))

  (define atj-gen-shallow-intbinapp ((fn (member-eq fn *atj-primitive-binops*))
                                     (left pseudo-termp)
                                     (right pseudo-termp)
                                     (src-type atj-typep)
                                     (dst-type atj-typep)
                                     (jvar-value-base stringp)
                                     (jvar-value-index posp)
                                     (jvar-result-base stringp)
                                     (jvar-result-index posp)
                                     (pkg-class-names string-string-alistp)
                                     (fn-method-names symbol-string-alistp)
                                     (curr-pkg stringp)
                                     (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 application of a function
            that models a Java @('int') binary operation."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model Java @('int') binary operations
       (i.e. @(tsee jint-add) etc.) are treated specially.
       (For now we only consider some of them;
       more will be considered in the future.)
       We generate Java code to compute the left and right operands,
       which will have the Java type @('int') required by
       @(tsee jint-add) and the other ACL2 functions.
       Then we convert those to @(':jint') if needed,
       via @('atj-adapt-jexpr-to-type').
       Finally, we generate a Java binary expression
       whose operator corresponds to the function.
       The type of the function application is @(':jint').
       We parenthesize the Java expression
       to avoid errors due to operator precedences
       when expressions are nested;
       in the future we should take precedences into account
       to avoid unnecessary parentheses and make the code more readable
       (it may be better to handle this in the pretty-printer)."))
    (b* (((mv left-jblock
              left-jexpr
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-term left
                                                       jvar-value-base
                                                       jvar-value-index
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       t ; GUARDS$
                                                       wrld))
         ((mv right-jblock
              right-jexpr
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-term right
                                                       jvar-value-base
                                                       jvar-value-index
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       t ; GUARDS$
                                                       wrld))
         (binop (case fn
                  (jint-add (jbinop-add))
                  (jint-sub (jbinop-sub))
                  (jint-mul (jbinop-mul))
                  (jint-div (jbinop-div))
                  (jint-rem (jbinop-rem))))
         (jexpr (jexpr-paren (jexpr-binary binop left-jexpr right-jexpr)))
         (jblock (append left-jblock right-jblock)))
      (mv jblock
          (atj-adapt-jexpr-to-type jexpr src-type dst-type)
          jvar-value-index
          jvar-result-index))
    ;; 2nd component is non-0
    ;; so that each call of ATJ-GEN-SHALLOW-TERM decreases
    ;; even when the ACL2-COUNT of the other addend is 0:
    :measure (two-nats-measure (+ (acl2-count left)
                                  (acl2-count right))
                               1))

  (define atj-gen-shallow-fnapp ((fn pseudo-termfnp)
                                 (args pseudo-term-listp)
                                 (src-type atj-typep)
                                 (dst-type atj-typep)
                                 (jvar-value-base stringp)
                                 (jvar-value-index posp)
                                 (jvar-result-base stringp)
                                 (jvar-result-index posp)
                                 (pkg-class-names string-string-alistp)
                                 (fn-method-names symbol-string-alistp)
                                 (curr-pkg stringp)
                                 (guards$ booleanp)
                                 (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 function application."
    :long
    (xdoc::topstring
     (xdoc::topstring
      "Terms of the form @('(if a a b)') are treated as @('(or a b)'),
       via a separate function, non-strictly.
       Other @(tsee if) calls are handled via a separate function,
       also non-strictly.
       We only pass one of @('src-type') or @('dst-type')
       to this separate function,
       because those two types are always equal for @(tsee if):
       see @(tsee atj-type-annotate-term).")
     (xdoc::p
      "If @(':guards') is @('t'),
       calls of @(tsee int-value) are handled via a separate function.
       We only pass @('dst-type') to this separate function,
       because @('src-type') is always @(':jint'),
       i.e. the output type of @(tsee int-value).")
     (xdoc::p
      "If @(':guards') is @('t'),
       calls of ACL2 functions that model Java @('int') binary operations
       are handled via a separate function.")
     (xdoc::p
      "In all other cases, where the call is always strict,
       we first generate Java code to compute all the actual arguments.
       Calls of lambda expression are handled by a separate function.
       If the function is a named one,
       we generate a call of the method that corresponds to the ACL2 function,
       and we wrap into a Java conversion if needed.
       (We treat the Java abstract syntax somewhat improperly here,
       by using a generic method call with a possibly qualified method name,
       which should be therefore a static method call;
       this still produces correct Java code,
       but it should be handled more properly
       in a future version of this implementation.)
       Note that, because of the type annotations of the ACL2 terms,
       the actual argument expressions will have types
       appropriate to the method's formal argument types."))
    (b* (((when (and (eq fn 'if)
                     (int= (len args) 3))) ; should be always true
          (b* ((first (first args))
               (second (second args))
               (athird (third args)))
            (if (equal first second)
                (atj-gen-shallow-orapp first
                                       athird
                                       dst-type ; = SRC-TYPE
                                       jvar-value-base
                                       jvar-value-index
                                       jvar-result-base
                                       jvar-result-index
                                       pkg-class-names
                                       fn-method-names
                                       curr-pkg
                                       guards$
                                       wrld)
              (atj-gen-shallow-ifapp first
                                     second
                                     athird
                                     dst-type ; = SRC-TYPE
                                     jvar-value-base
                                     jvar-value-index
                                     jvar-result-base
                                     jvar-result-index
                                     pkg-class-names
                                     fn-method-names
                                     curr-pkg
                                     guards$
                                     wrld))))
         ((when (and guards$
                     (eq fn 'int-value)
                     (int= (len args) 1))) ; should be always true
          (atj-gen-shallow-intvalapp (car args)
                                     src-type
                                     dst-type
                                     jvar-value-base
                                     jvar-value-index
                                     jvar-result-base
                                     jvar-result-index
                                     pkg-class-names
                                     fn-method-names
                                     curr-pkg
                                     wrld))
         ((when (and guards$
                     (member-eq fn *atj-primitive-binops*)
                     (int= (len args) 2))) ; should be always true
          (atj-gen-shallow-intbinapp fn
                                     (first args)
                                     (second args)
                                     src-type
                                     dst-type
                                     jvar-value-base
                                     jvar-value-index
                                     jvar-result-base
                                     jvar-result-index
                                     pkg-class-names
                                     fn-method-names
                                     curr-pkg
                                     wrld))
         ((mv arg-jblocks
              arg-jexprs
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-terms args
                                                        jvar-value-base
                                                        jvar-value-index
                                                        jvar-result-base
                                                        jvar-result-index
                                                        pkg-class-names
                                                        fn-method-names
                                                        curr-pkg
                                                        guards$
                                                        wrld))
         ((when (symbolp fn))
          (b* ((jexpr (jexpr-method
                       (atj-gen-shallow-fnname fn
                                               pkg-class-names
                                               fn-method-names
                                               curr-pkg)
                       arg-jexprs))
               (jexpr (atj-adapt-jexpr-to-type jexpr src-type dst-type)))
            (mv (flatten arg-jblocks)
                jexpr
                jvar-value-index
                jvar-result-index)))
         ((mv lambda-jblock
              lambda-jexpr
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-lambda (lambda-formals fn)
                                                         (lambda-body fn)
                                                         arg-jblocks
                                                         arg-jexprs
                                                         src-type
                                                         dst-type
                                                         jvar-value-base
                                                         jvar-value-index
                                                         jvar-result-base
                                                         jvar-result-index
                                                         pkg-class-names
                                                         fn-method-names
                                                         curr-pkg
                                                         guards$
                                                         wrld)))
      (mv lambda-jblock
          lambda-jexpr
          jvar-value-index
          jvar-result-index))
    ;; 2nd component is greater than the one of ATJ-GEN-SHALLOW-LAMBDA
    ;; so that the call of ATJ-GEN-SHALLOW-LAMBDA decreases
    ;; even when FN is a non-symbol atom (impossible under the guard):
    :measure (two-nats-measure (+ (acl2-count fn)
                                  (acl2-count args))
                               2))

  (define atj-gen-shallow-lambda ((formals symbol-listp)
                                  (body pseudo-termp)
                                  (arg-jblocks jblock-listp)
                                  (arg-jexprs jexpr-listp)
                                  (src-type atj-typep)
                                  (dst-type atj-typep)
                                  (jvar-value-base stringp)
                                  (jvar-value-index posp)
                                  (jvar-result-base stringp)
                                  (jvar-result-index posp)
                                  (pkg-class-names string-string-alistp)
                                  (fn-method-names symbol-string-alistp)
                                  (curr-pkg stringp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :guard (and (int= (len arg-jblocks) (len formals))
                (int= (len arg-jexprs) (len formals))
                (not (equal curr-pkg "")))
    :returns (mv (jblock jblockp :hyp (jblock-listp arg-jblocks))
                 (jexpr jexprp)
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 lambda expression,
            applied to given Java expressions as arguments."
    :long
    (xdoc::topstring
     (xdoc::p
      "We generate @(tsee let) bindings for the formal parameters.
       Then we generate Java code for the body of the lambda expression."))
    (b* ((let-jblock (atj-gen-shallow-let-bindings formals
                                                   arg-jblocks
                                                   arg-jexprs))
         ((mv body-jblock
              body-jexpr
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-term body
                                                       jvar-value-base
                                                       jvar-value-index
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       guards$
                                                       wrld)))
      (mv (append let-jblock body-jblock)
          (atj-adapt-jexpr-to-type body-jexpr src-type dst-type)
          jvar-value-index
          jvar-result-index))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count body) 1))

  (define atj-gen-shallow-term ((term pseudo-termp)
                                (jvar-value-base stringp)
                                (jvar-value-index posp)
                                (jvar-result-base stringp)
                                (jvar-result-index posp)
                                (pkg-class-names string-string-alistp)
                                (fn-method-names symbol-string-alistp)
                                (curr-pkg stringp)
                                (guards$ booleanp)
                                (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (jblock jblockp)
                 (jexpr jexprp)
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 term."
    :long
    (xdoc::topstring
     (xdoc::p
      "Prior to calling this function,
       the term has been type-annotated via @(tsee atj-type-annotate-term).
       Thus, we first unwrap it and decompose its wrapper.")
     (xdoc::p
      "Prior to calling this function,
       the ACL2 variables have been renamed, via @(tsee atj-rename-term),
       so that they have the right names as Java variables.
       Thus, if the ACL2 term is a variable,
       we remove its type annotation
       and generate a Java variable with the same name.
       Then we wrap it with a Java conversion, if needed.")
     (xdoc::p
      "If the ACL2 term is a quoted constant,
       we represent it as its value.
       We wrap the resulting expression with a Java conversion, if needed."))
    (b* (((mv term src-type dst-type) (atj-type-unwrap-term term))
         ((unless term) ; for termination proof
          (mv nil (jexpr-name "dummy") jvar-value-index jvar-result-index))
         ((when (variablep term))
          (b* (((mv var &) (atj-unmark-var term))
               ((mv var &) (atj-type-unannotate-var var))
               (jexpr (jexpr-name (symbol-name var)))
               (jexpr (atj-adapt-jexpr-to-type jexpr src-type dst-type)))
            (mv nil jexpr jvar-value-index jvar-result-index)))
         ((when (fquotep term))
          (b* ((value (unquote-term term))
               ((mv jblock jexpr jvar-value-index)
                (atj-gen-value value jvar-value-base jvar-value-index))
               (jexpr (atj-adapt-jexpr-to-type jexpr src-type dst-type)))
            (mv jblock jexpr jvar-value-index jvar-result-index))))
      (atj-gen-shallow-fnapp (ffn-symb term)
                             (fargs term)
                             src-type
                             dst-type
                             jvar-value-base
                             jvar-value-index
                             jvar-result-base
                             jvar-result-index
                             pkg-class-names
                             fn-method-names
                             curr-pkg
                             guards$
                             wrld))
    :measure (two-nats-measure (acl2-count term) 0))

  (define atj-gen-shallow-terms ((terms pseudo-term-listp)
                                 (jvar-value-base stringp)
                                 (jvar-value-index posp)
                                 (jvar-result-base stringp)
                                 (jvar-result-index posp)
                                 (pkg-class-names string-string-alistp)
                                 (fn-method-names symbol-string-alistp)
                                 (curr-pkg stringp)
                                 (guards$ booleanp)
                                 (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (jblocks jblock-listp)
                 (jexpr jexpr-listp)
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Lift @(tsee atj-gen-shallow-term) to lists."
    (if (endp terms)
        (mv nil nil jvar-value-index jvar-result-index)
      (b* (((mv first-jblock
                first-jexpr
                jvar-value-index
                jvar-result-index) (atj-gen-shallow-term (car terms)
                                                         jvar-value-base
                                                         jvar-value-index
                                                         jvar-result-base
                                                         jvar-result-index
                                                         pkg-class-names
                                                         fn-method-names
                                                         curr-pkg
                                                         guards$
                                                         wrld))
           ((mv rest-jblocks
                rest-jexprs
                jvar-value-index
                jvar-result-index) (atj-gen-shallow-terms (cdr terms)
                                                          jvar-value-base
                                                          jvar-value-index
                                                          jvar-result-base
                                                          jvar-result-index
                                                          pkg-class-names
                                                          fn-method-names
                                                          curr-pkg
                                                          guards$
                                                          wrld)))
        (mv (cons first-jblock rest-jblocks)
            (cons first-jexpr rest-jexprs)
            jvar-value-index
            jvar-result-index)))
    :measure (two-nats-measure (acl2-count terms) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-pkg-jmethod-name ((pkg stringp))
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
            (implode (atj-chars-to-jchars-id (explode pkg) nil nil))))

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
      (jexpr-smethod *atj-jtype-pkg-name*
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

(define atj-gen-pkg-jmethod ((pkg stringp) (verbose$ booleanp))
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
        (cw "  ~s0~%" pkg))
       (jvar-aimports "imports")
       (jmethod-name (atj-gen-pkg-jmethod-name pkg))
       (aimports (pkg-imports pkg))
       (len-jexpr (jexpr-literal-integer-decimal (len aimports)))
       (newlist-jexpr (jexpr-newclass (jtype-class "ArrayList<>")
                                      (list len-jexpr)))
       (imports-jblock (jblock-locvar (jtype-class "List<Acl2Symbol>")
                                      jvar-aimports
                                      newlist-jexpr))
       (imports-jblock (append imports-jblock
                               (atj-gen-pkg-jmethod-aux aimports
                                                        jvar-aimports)))
       (pkg-name-jexpr (atj-gen-pkg-name pkg))
       (defpkg-jblock (jblock-smethod *atj-jtype-pkg*
                                      "define"
                                      (list pkg-name-jexpr
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
  ((define atj-gen-pkg-jmethod-aux ((imports symbol-listp)
                                    (jvar-aimports stringp))
     :returns (jblock jblockp)
     :parents nil
     (cond ((endp imports) nil)
           (t (b* ((import-jexpr (atj-gen-symbol (car imports)))
                   (first-jblock (jblock-imethod (jexpr-name jvar-aimports)
                                                 "add"
                                                 (list import-jexpr)))
                   (rest-jblock (atj-gen-pkg-jmethod-aux (cdr imports)
                                                         jvar-aimports)))
                (append first-jblock rest-jblock)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-pkg-jmethods ((pkgs string-listp) (verbose$ booleanp))
  :returns (jmethods jmethod-listp)
  :short "Generate all the Java methods that add the ACL2 package definitions."
  (if (endp pkgs)
      nil
    (b* ((first-jmethod (atj-gen-pkg-jmethod (car pkgs) verbose$))
         (rest-jmethods (atj-gen-pkg-jmethods (cdr pkgs) verbose$)))
      (cons first-jmethod rest-jmethods))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-pkgs ((pkgs string-listp))
  :returns (jblock jblockp)
  :short "Generate Java code to build the ACL2 packages."
  :long
  (xdoc::topstring-p
   "This is a sequence of calls to the methods
    generated by @(tsee atj-gen-pkg-jmethods).
    These calls are part of the code that
    initializes (the Java representation of) the ACL2 environment.")
  (if (endp pkgs)
      nil
    (b* ((jmethod-name (atj-gen-pkg-jmethod-name (car pkgs)))
         (first-jblock (jblock-method jmethod-name nil))
         (rest-jblock (atj-gen-pkgs (cdr pkgs))))
      (append first-jblock rest-jblock))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-pkg-witness ()
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

(define atj-gen-deep-fndef-jmethod-name ((fn symbolp))
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
   (implode (atj-chars-to-jchars-id (explode
                                     (symbol-package-name fn)) nil nil))
   "$$$"
   (implode (atj-chars-to-jchars-id (explode (symbol-name fn)) nil t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-fndef-jmethod ((fn symbolp)
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
    "If the @(':guards') input is @('t'),
     we remove all the @(':logic') parts of @(tsee mbe)s;
     if the @(':guards') input is @('nil'),
     we remove all the @(':exec') parts of @(tsee mbe)s.
     We also remove all the non-last arguments
     of @(tsee prog2$)s and @(tsee progn$)s.
     This should remove any occurrences of @(tsee return-last).
     See " (xdoc::seetopic "atj-input-processing" "this discussion")
     " for background.")
   (xdoc::p
    "The indices of the local variables
     to build values, terms, and lambda expressions
     are all reset to 1,
     because each function definition is built in its own method
     (thus, there are no cross-references)."))
  (b* ((wrld (w state))
       ((run-when verbose$)
        (cw "  ~s0~%" fn))
       (jmethod-name (atj-gen-deep-fndef-jmethod-name fn))
       (jvar-function "function")
       (jvar-formals "formals")
       (jvar-body "body")
       (formals (formals fn wrld))
       (body (ubody fn wrld))
       (in-types (repeat (len formals) :value)) ; actually irrelevant
       (out-type :value) ; actually irrelevant
       ((mv formals body)
        (atj-pre-translate fn formals body in-types out-type t guards$ wrld))
       (fn-jblock (jblock-locvar *atj-jtype-named-fn*
                                 jvar-function
                                 (jexpr-smethod *atj-jtype-named-fn*
                                                "make"
                                                (list (atj-gen-symbol fn)))))
       (formals-jblock (jblock-locvar (jtype-array *atj-jtype-symbol*)
                                      jvar-formals
                                      (atj-gen-deep-formals formals)))
       ((mv body-jblock
            body-jexpr
            & & &) (atj-gen-deep-term
                    body "value" 1 "term" 1 "lambda" 1 guards$))
       (body-jblock (append body-jblock
                            (jblock-locvar *atj-jtype-term*
                                           jvar-body
                                           body-jexpr)))
       (def-jblock (jblock-imethod (jexpr-name jvar-function)
                                   "define"
                                   (list (jexpr-name jvar-formals)
                                         (jexpr-name jvar-body))))
       (jmethod-body (append fn-jblock
                             formals-jblock
                             body-jblock
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

(define atj-gen-deep-fndef-jmethods ((fns symbol-listp)
                                     (guards$ booleanp)
                                     (verbose$ booleanp)
                                     state)
  :returns (jmethods jmethod-listp)
  :verify-guards nil
  :short "Generate all the Java methods that build
          the deeply embedded ACL2 function definitions."
  (if (endp fns)
      nil
    (b* ((first-jmethod
          (atj-gen-deep-fndef-jmethod (car fns) guards$ verbose$ state))
         (rest-jmethods
          (atj-gen-deep-fndef-jmethods (cdr fns) guards$ verbose$ state)))
      (cons first-jmethod rest-jmethods))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-deep-fndefs ((fns symbol-listp))
  :returns (jblock jblockp)
  :short "Generate Java code to build
          the deeply embedded ACL2 function definitions."
  :long
  (xdoc::topstring-p
   "This is a sequence of calls to the methods
    generated by @(tsee atj-gen-deep-fndef-jmethods).
    These calls are part of the code that
    initializes (the Java representation of) the ACL2 environment.")
  (if (endp fns)
      nil
    (b* ((jmethod-name (atj-gen-deep-fndef-jmethod-name (car fns)))
         (first-jblock (jblock-method jmethod-name nil))
         (rest-jblock (atj-gen-deep-fndefs (cdr fns))))
      (append first-jblock rest-jblock))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fnnative ((fn symbolp)
                                  (pkg-class-names string-string-alistp)
                                  (fn-method-names symbol-string-alistp)
                                  (guards$ booleanp)
                                  (curr-pkg stringp)
                                  (wrld plist-worldp))
  :guard (and (atj-aij-nativep fn)
              (equal (symbol-package-name fn) curr-pkg)
              (not (equal curr-pkg "")))
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
  (b* ((jmethod-name (atj-gen-shallow-fnname fn
                                             pkg-class-names
                                             fn-method-names
                                             curr-pkg))
       (jmethod-param-names
        (case fn
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
       (fn-type (atj-get-function-type fn guards$ wrld))
       (fn-in-types (atj-function-type->inputs fn-type))
       (fn-out-type (atj-function-type->output fn-type))
       (jmethod-params (atj-gen-jparamlist jmethod-param-names
                                           (atj-types-to-jtypes fn-in-types)))
       (jcall-method-name
        (case fn
          (characterp "execCharacterp")
          (stringp "execStringp")
          (symbolp "execSymbolp")
          (integerp "execIntegerp")
          (rationalp "execRationalp")
          (complex-rationalp "execComplexRationalp")
          (acl2-numberp "execAcl2Numberp")
          (consp "execConsp")
          (char-code (if (equal fn-in-types '(:character))
                         "execCharCodeUnderGuard"
                       "execCharCode"))
          (code-char (if (equal fn-in-types '(:integer))
                         "execCodeCharUnderGuard"
                       "execCodeChar"))
          (coerce (if (equal fn-in-types '(:value :symbol))
                      "execCoerceUnderGuard"
                    "execCoerce"))
          (intern-in-package-of-symbol
           (if (equal fn-in-types '(:string :symbol))
               "execInternInPackageOfSymbolUnderGuard"
             "execInternInPackageOfSymbol"))
          (symbol-package-name (if (equal fn-in-types '(:symbol))
                                   "execSymbolPackageNameUnderGuard"
                                 "execSymbolPackageName"))
          (symbol-name (if (equal fn-in-types '(:symbol))
                           "execSymbolNameUnderGuard"
                         "execSymbolName"))
          (pkg-imports (if (equal fn-in-types '(:string))
                           "execPkgImportsUnderGuard"
                         "execPkgImports"))
          (pkg-witness (if (equal fn-in-types '(:string))
                           "execPkgWitnessUnderGuard"
                         "execPkgWitness"))
          (unary-- (if (equal fn-in-types '(:number))
                       "execUnaryMinusUnderGuard"
                     "execUnaryMinus"))
          (unary-/ (if (equal fn-in-types '(:number))
                       "execUnarySlashUnderGuard"
                     "execUnarySlash"))
          (binary-+ (if (equal fn-in-types '(:number :number))
                        "execBinaryPlusUnderGuard"
                      "execBinaryPlus"))
          (binary-* (if (equal fn-in-types '(:number :number))
                        "execBinaryStarUnderGuard"
                      "execBinaryStar"))
          (< (if (equal fn-in-types '(:rational :rational))
                 "execLessThanUnderGuard"
               "execLessThan"))
          (complex (if (equal fn-in-types '(:rational :rational))
                       "execComplexUnderGuard"
                     "execComplex"))
          (realpart (if (equal fn-in-types '(:number))
                        "execRealPartUnderGuard"
                      "execRealPart"))
          (imagpart (if (equal fn-in-types '(:number))
                        "execImagPartUnderGuard"
                      "execImagPart"))
          (numerator (if (equal fn-in-types '(:rational))
                         "execNumeratorUnderGuard"
                       "execNumerator"))
          (denominator (if (equal fn-in-types '(:rational))
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
                  :result (jresult-type (atj-type-to-jtype fn-out-type))
                  :name jmethod-name
                  :params jmethod-params
                  :throws (list *atj-jclass-eval-exc*)
                  :body jmethod-body))
  :guard-hints (("Goal" :in-theory (enable atj-aij-nativep primitivep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fndef ((fn symbolp)
                               (pkg-class-names string-string-alistp)
                               (fn-method-names symbol-string-alistp)
                               (guards$ booleanp)
                               (verbose$ booleanp)
                               (curr-pkg stringp)
                               state)
  :guard (and (equal (symbol-package-name fn) curr-pkg)
              (not (equal curr-pkg "")))
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
    "If the @(':guards') input is @('t'),
     we remove all the @(':logic') parts of @(tsee mbe)s;
     if the @(':guards') input is @('nil'),
     we remove all the @(':exec') parts of @(tsee mbe)s.
     We also remove all the non-last arguments
     of @(tsee prog2$)s and @(tsee progn$)s.
     This should remove any occurrences of @(tsee return-last).
     See " (xdoc::seetopic "atj-input-processing" "this discussion")
     " for background.")
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
        (cw "  ~s0~%" fn))
       (formals (formals fn wrld))
       (body (ubody fn (w state)))
       (fn-type (atj-get-function-type fn guards$ wrld))
       (in-types (atj-function-type->inputs fn-type))
       (out-type (atj-function-type->output fn-type))
       ((mv formals body)
        (atj-pre-translate fn formals body in-types out-type nil guards$ wrld))
       (jmethod-name (atj-gen-shallow-fnname fn
                                             pkg-class-names
                                             fn-method-names
                                             curr-pkg))
       ((mv formals &) (atj-unmark-vars formals))
       ((mv formals &) (atj-type-unannotate-vars formals))
       (jmethod-params (atj-gen-jparamlist (symbol-name-lst formals)
                                           (atj-types-to-jtypes in-types)))
       ((mv body-jblock body-jexpr & &)
        (atj-gen-shallow-term body
                              "$value" 1
                              "$result" 1
                              pkg-class-names
                              fn-method-names
                              curr-pkg
                              guards$
                              wrld))
       (jmethod-body (append body-jblock
                             (jblock-return body-jexpr)))
       (jmethod-body (atj-post-translate jmethod-body)))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type (atj-type-to-jtype out-type))
                  :name jmethod-name
                  :params jmethod-params
                  :throws (list *atj-jclass-eval-exc*)
                  :body jmethod-body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fn ((fn symbolp)
                            (pkg-class-names string-string-alistp)
                            (fn-method-names symbol-string-alistp)
                            (guards$ booleanp)
                            (verbose$ booleanp)
                            (curr-pkg stringp)
                            state)
  :guard (and (equal (symbol-package-name fn) curr-pkg)
              (not (equal curr-pkg "")))
  :returns (jmethod jmethodp)
  :verify-guards nil
  :short "Generate a shallowly embedded
          ACL2 function natively implemented in AIJ
          or ACL2 function definition."
  (if (atj-aij-nativep fn)
      (atj-gen-shallow-fnnative fn
                                pkg-class-names
                                fn-method-names
                                guards$
                                curr-pkg
                                (w state))
    (atj-gen-shallow-fndef fn
                           pkg-class-names
                           fn-method-names
                           guards$
                           verbose$
                           curr-pkg
                           state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fns ((fns symbol-listp)
                             (pkg-class-names string-string-alistp)
                             (fn-method-names symbol-string-alistp)
                             (guards$ booleanp)
                             (verbose$ booleanp)
                             (curr-pkg stringp)
                             state)
  :guard (and (equal (symbol-package-name-lst fns)
                     (repeat (len fns) curr-pkg))
              (not (equal curr-pkg "")))
  :returns (jmethods jmethod-listp)
  :verify-guards nil
  :short "Lift @(tsee atj-gen-shallow-fn) to lists."
  (cond ((endp fns) nil)
        (t (b* ((first-jmethod (atj-gen-shallow-fn (car fns)
                                                   pkg-class-names
                                                   fn-method-names
                                                   guards$
                                                   verbose$
                                                   curr-pkg
                                                   state))
                (rest-jmethods (atj-gen-shallow-fns (cdr fns)
                                                    pkg-class-names
                                                    fn-method-names
                                                    guards$
                                                    verbose$
                                                    curr-pkg
                                                    state)))
             (cons first-jmethod rest-jmethods)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fns-in-pkg ((fns symbol-listp)
                                    (pkg stringp)
                                    (pkg-class-names string-string-alistp)
                                    (fn-method-names symbol-string-alistp)
                                    (guards$ booleanp)
                                    (verbose$ booleanp)
                                    state)
  :guard (equal (symbol-package-name-lst fns)
                (repeat (len fns) pkg))
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
  (b* ((pair (assoc-equal pkg pkg-class-names))
       ((unless (consp pair))
        (raise "Internal error: no class name for package name ~x0." pkg)
        ;; irrelevant:
        (make-jclass :access (jaccess-public) :name ""))
       (jclass-name (cdr pair))
       (jclass-methods (atj-gen-shallow-fns fns
                                            pkg-class-names
                                            fn-method-names
                                            guards$
                                            verbose$
                                            pkg
                                            state)))
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

(define atj-gen-shallow-fns-by-pkg ((fns symbol-listp)
                                    (fns-by-pkg string-symbollist-alistp)
                                    (guards$ booleanp)
                                    (java-class$ stringp)
                                    (verbose$ booleanp)
                                    state)
  :returns (mv (jclasses jclass-listp)
               (pkg-class-names "A @(tsee string-string-alistp).")
               (fn-method-names "A @(tsee symbol-string-alistp)."))
  :verify-guards nil
  :short "Generate shallowly embedded ACL2 functions, by ACL2 packages."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through each pair in the alist
     from ACL2 package names to ACL2 functions,
     and generate all the Java classes corresponding to the ACL2 packages.")
   (xdoc::p
    "We also return the alist from ACL2 package names to Java class names
     and the alist from ACL2 function symbols to Java method names,
     which must be eventually passed to the functions that generate
     the Java test class."))
  (b* ((pkgs (remove-duplicates-equal (strip-cars fns-by-pkg)))
       (pkg-class-names (atj-pkgs-to-classes pkgs java-class$))
       (fn-method-names (atj-fns-to-methods (remove-duplicates-equal fns))))
    (mv (atj-gen-shallow-fns-by-pkg-aux pkgs
                                        fns-by-pkg
                                        pkg-class-names
                                        fn-method-names
                                        guards$
                                        java-class$
                                        verbose$
                                        state)
        pkg-class-names
        fn-method-names))

  :prepwork
  ((define atj-gen-shallow-fns-by-pkg-aux
     ((pkgs string-listp)
      (fns-by-pkg string-symbollist-alistp)
      (pkg-class-names string-string-alistp)
      (fn-method-names symbol-string-alistp)
      (guards$ booleanp)
      (java-class$ stringp)
      (verbose$ booleanp)
      state)
     :returns (jclasses jclass-listp)
     :verify-guards nil
     (b* (((when (endp pkgs)) nil)
          (pkg (car pkgs))
          (fns (cdr (assoc-equal pkg fns-by-pkg)))
          (first-jclass (atj-gen-shallow-fns-in-pkg fns
                                                    pkg
                                                    pkg-class-names
                                                    fn-method-names
                                                    guards$
                                                    verbose$
                                                    state))
          (rest-jclasses (atj-gen-shallow-fns-by-pkg-aux (cdr pkgs)
                                                         fns-by-pkg
                                                         pkg-class-names
                                                         fn-method-names
                                                         guards$
                                                         java-class$
                                                         verbose$
                                                         state)))
       (cons first-jclass rest-jclasses)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-init-jmethod ((pkgs string-listp)
                              (fns symbol-listp)
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
       (pkgs-jblock (atj-gen-pkgs pkgs))
       (pkg-witness-jblock (atj-gen-pkg-witness))
       (fns-jblock? (if deep$
                        (atj-gen-deep-fndefs fns)
                      nil))
       (validate-jblock (and deep$
                             (jblock-smethod *atj-jtype-named-fn*
                                             "validateAll"
                                             nil)))
       (initialize-jblock (jblock-asg-name "initialized"
                                           (jexpr-literal-true)))
       (jmethod-body (append if-jblock
                             pkgs-jblock
                             pkg-witness-jblock
                             fns-jblock?
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

(define atj-gen-jclass ((pkgs string-listp)
                        (fns symbol-listp)
                        (deep$ booleanp)
                        (guards$ booleanp)
                        (java-class$ stringp)
                        (verbose$ booleanp)
                        state)
  :returns (mv (jclass jclassp)
               (pkg-class-names "A @(tsee string-string-alistp).")
               (fn-method-names "A @(tsee sybmol-string-alistp)."))
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
     and we proceed to generate the Java nested classes and methods.")
   (xdoc::p
    "We also return the alist from ACL2 package names to Java class names
     and the alist from ACL2 function symbols to Java method names,
     which must be eventually passed to the functions that generate
     the Java test class.
     These are @('nil') in the deep embedding approach;
     they is only used in the shallow embedding approach."))
  (b* ((init-jfield (atj-gen-init-jfield))
       ((run-when verbose$)
        (cw "~%Generating Java code for the ACL2 packages:~%"))
       (pkg-jmethods (atj-gen-pkg-jmethods pkgs verbose$))
       ((run-when verbose$)
        (cw "~%Generating Java code for the ACL2 functions:~%"))
       ((mv fn-jmembers pkg-class-names fn-method-names)
        (if deep$
            (mv (jmethods-to-jcmembers
                 (atj-gen-deep-fndef-jmethods fns guards$ verbose$ state))
                nil
                nil)
          (b* ((fns+natives
                (remove-duplicates-eq
                 (append fns
                         (strip-cars *primitive-formals-and-guards*))))
               (fns-by-pkg (organize-symbols-by-pkg fns+natives))
               ((mv jclasses pkg-class-names fn-method-names)
                (atj-gen-shallow-fns-by-pkg fns+natives
                                            fns-by-pkg
                                            guards$
                                            java-class$
                                            verbose$
                                            state)))
            (mv (jclasses-to-jcmembers jclasses)
                pkg-class-names
                fn-method-names))))
       (init-jmethod (atj-gen-init-jmethod pkgs fns deep$))
       (call-jmethod? (and deep$
                           (list (atj-gen-call-jmethod))))
       (body-jclass (append (list (jcmember-field init-jfield))
                            (jmethods-to-jcmembers pkg-jmethods)
                            fn-jmembers
                            (list (jcmember-method init-jmethod))
                            (jmethods-to-jcmembers call-jmethod?))))
    (mv (make-jclass :access (jaccess-public)
                     :abstract? nil
                     :static? nil
                     :final? nil
                     :strictfp? nil
                     :name java-class$
                     :superclass? nil
                     :superinterfaces nil
                     :body body-jclass)
        pkg-class-names
        fn-method-names)))

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
                              (guards$ booleanp)
                              (java-class$ stringp)
                              (verbose$ booleanp)
                              (pkg-class-names string-string-alistp)
                              (fn-method-names symbol-string-alistp)
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
      thus, we use @('\"KEYWORD\"') as current package name,
      which never contains any functions."))
   (xdoc::p
    "Examining any generated instance of this method
     should make the above documentation,
     and the implementation of this code generation function,
     much clearer."))
  (b* (((atj-test test) test$)
       ((run-when verbose$)
        (cw "  ~s0~%" test.name))
       (jmethod-name (atj-gen-test-jmethod-name test.name))
       ((mv args-jblock
            args-jexprs
            jvar-value-index) (atj-gen-values test.arguments "value" 1))
       ((mv ares-jblock
            ares-jexpr
            &) (atj-gen-value test.result "value" jvar-value-index))
       (current-time-jexpr (jexpr-smethod (jtype-class "System")
                                          "currentTimeMillis"
                                          nil))
       (fn-type (atj-get-function-type test.function guards$ wrld))
       (in-types (atj-function-type->inputs fn-type))
       ((mv shallow-arg-jblock shallow-arg-jvars)
        (if deep$
            (mv nil nil)
          (atj-gen-test-jmethod-aux args-jexprs in-types 1)))
       (n!=0-jexpr (jexpr-binary (jbinop-ne)
                                 (jexpr-name "n")
                                 (jexpr-literal-0)))
       (jmethod-body
        (append
         (jblock-imethod (jexpr-name "System.out")
                         "print"
                         (list (atj-gen-jstring
                                (str::cat "Testing '" test.name "'..."))))
         args-jblock ; build test.arguments
         (if deep$
             (jblock-locvar (jtype-array *atj-jtype-value*)
                            "functionArguments"
                            (jexpr-newarray-init *atj-jtype-value*
                                                 args-jexprs))
           shallow-arg-jblock) ; assign to argument1, argument2, ...
         ares-jblock ; build test.result
         (jblock-locvar *atj-jtype-value* "resultAcl2" ares-jexpr)
         (and deep$
              (jblock-locvar *atj-jtype-symbol*
                             "functionName"
                             (atj-gen-symbol test.function)))
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
                                           (atj-gen-shallow-fnname
                                            test.function
                                            pkg-class-names
                                            fn-method-names
                                            "KEYWORD")
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
  ((define atj-gen-test-jmethod-aux ((args-jexprs jexpr-listp)
                                     (types atj-type-listp)
                                     (index posp))
     :guard (= (len args-jexprs) (len types))
     :returns (mv (jblock jblockp)
                  (jvars string-listp))
     (cond ((endp args-jexprs) (mv nil nil))
           (t (b* ((first-jvar (str::cat "argument" (str::natstr index)))
                   (first-type (car types))
                   (first-jtype (atj-type-to-jtype first-type))
                   (first-jexpr (jexpr-cast (atj-type-to-jtype first-type)
                                            (car args-jexprs)))
                   (first-jblock (jblock-locvar first-jtype
                                                first-jvar
                                                first-jexpr))
                   ((mv rest-jblock rest-jvars)
                    (atj-gen-test-jmethod-aux (cdr args-jexprs)
                                              (cdr types)
                                              (1+ index))))
                (mv (append first-jblock rest-jblock)
                    (cons first-jvar rest-jvars))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-jmethods ((tests$ atj-test-listp)
                               (deep$ booleanp)
                               (guards$ booleanp)
                               (java-class$ stringp)
                               (verbose$ booleanp)
                               (pkg-class-names string-string-alistp)
                               (fn-method-names symbol-string-alistp)
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
          (atj-gen-test-jmethod (car tests$)
                                deep$
                                guards$
                                java-class$
                                verbose$
                                pkg-class-names
                                fn-method-names
                                wrld))
         (rest-jmethods
          (atj-gen-test-jmethods (cdr tests$)
                                 deep$
                                 guards$
                                 java-class$
                                 verbose$
                                 pkg-class-names
                                 fn-method-names
                                 wrld)))
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
                             (guards$ booleanp)
                             (java-class$ stringp)
                             (verbose$ booleanp)
                             (pkg-class-names string-string-alistp)
                             (fn-method-names symbol-string-alistp)
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
       (test-jmethods (atj-gen-test-jmethods tests$
                                             deep$
                                             guards$
                                             java-class$
                                             verbose$
                                             pkg-class-names
                                             fn-method-names
                                             wrld))
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
                        (pkgs string-listp)
                        (fns symbol-listp)
                        (verbose$ booleanp)
                        state)
  :returns (mv (jcunit jcunitp)
               (pkg-class-names "A @(tsee string-string-alistp).")
               (fn-method-names "A @(tsee symbol-string-alistp)."))
  :verify-guards nil
  :short "Generate the main Java compilation unit."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the generated imports are changed,
     the constant @(tsee *atj-disallowed-class-names*)
     must be modified accordingly.")
   (xdoc::p
    "We also return the alist from ACL2 package names to Java class names
     and the alist from ACL2 function symbols to Java method names,
     which must be eventually passed to the functions that generate
     the Java test class.
     These are @('nil') in the deep embedding approach;
     they are only used in the shallow embedding approach."))
  (b* (((mv class pkg-class-names fn-method-names)
        (atj-gen-jclass pkgs
                        fns
                        deep$
                        guards$
                        java-class$
                        verbose$
                        state))
       (cunit
        (make-jcunit
         :package? java-package$
         :imports (list (str::cat *atj-aij-jpackage* ".*")
                        ;; keep in sync with *ATJ-DISALLOWED-CLASS-NAMES*:
                        "java.math.BigInteger"
                        "java.util.ArrayList"
                        "java.util.List")
         :types (list class))))
    (mv cunit pkg-class-names fn-method-names)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-jcunit ((deep$ booleanp)
                             (guards$ booleanp)
                             (java-package$ maybe-stringp)
                             (java-class$ stringp)
                             (tests$ atj-test-listp)
                             (verbose$ booleanp)
                             (pkg-class-names string-string-alistp)
                             (fn-method-names symbol-string-alistp)
                             (wrld plist-worldp))
  :returns (jcunit jcunitp)
  :verify-guards nil
  :short "Generate the test Java compilation unit."
  (make-jcunit :package? java-package$
               :imports (list (str::cat *atj-aij-jpackage* ".*")
                              "java.math.BigInteger")
               :types (list (atj-gen-test-jclass tests$
                                                 deep$
                                                 guards$
                                                 java-class$
                                                 verbose$
                                                 pkg-class-names
                                                 fn-method-names
                                                 wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jfile ((deep$ booleanp)
                       (guards$ booleanp)
                       (java-package$ maybe-stringp)
                       (java-class$ maybe-stringp)
                       (output-file$ stringp)
                       (pkgs string-listp)
                       (fns symbol-listp)
                       (verbose$ booleanp)
                       state)
  :returns (mv (pkg-class-names "A @(tsee string-string-alistp).")
               (fn-method-names "A @(tsee symbol-string-alistp).")
               state)
  :mode :program
  :short "Generate the main Java file."
  :long
  (xdoc::topstring
   (xdoc::p
    "We also return the alist from ACL2 package names to Java class names
     and the alist from ACL2 function symbols to Java method names,
     which must be eventually passed to the functions that generate
     the Java test class.
     These are @('nil') in the deep embedding approach;
     they are only used in the shallow embedding approach."))
  (b* (((mv cunit
            pkg-class-names
            fn-method-names) (atj-gen-jcunit deep$
                                             guards$
                                             java-package$
                                             java-class$
                                             pkgs
                                             fns
                                             verbose$
                                             state))
       (state (print-to-jfile (print-jcunit cunit)
                              output-file$
                              state)))
    (mv pkg-class-names fn-method-names state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-jfile ((deep$ booleanp)
                            (guards$ booleanp)
                            (java-package$ maybe-stringp)
                            (java-class$ stringp)
                            (output-file-test$ stringp)
                            (tests$ atj-test-listp)
                            (verbose$ booleanp)
                            (pkg-class-names string-string-alistp)
                            (fn-method-names symbol-string-alistp)
                            state)
  :returns state
  :mode :program
  :short "Generate the test Java file."
  (print-to-jfile (print-jcunit (atj-gen-test-jcunit deep$
                                                     guards$
                                                     java-package$
                                                     java-class$
                                                     tests$
                                                     verbose$
                                                     pkg-class-names
                                                     fn-method-names
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
                            (pkgs string-listp)
                            (fns symbol-listp)
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
     We generate the test Java file only if @(':tests') is not @('nil').")
   (xdoc::p
    "We pass the alist from ACL2 package names to Java class names
     from one file generation function to the other.
     This is @('nil') in the deep embedding approach."))
  (state-global-let*
   ((fmt-soft-right-margin 100000 set-fmt-soft-right-margin)
    (fmt-hard-right-margin 100000 set-fmt-hard-right-margin))
   (b* (((mv pkg-class-names
             fn-method-names
             state) (atj-gen-jfile deep$
                                   guards$
                                   java-package$
                                   java-class$
                                   output-file$
                                   pkgs
                                   fns
                                   verbose$
                                   state))
        (state (if tests$
                   (atj-gen-test-jfile deep$
                                       guards$
                                       java-package$
                                       java-class$
                                       output-file-test$
                                       tests$
                                       verbose$
                                       pkg-class-names
                                       fn-method-names
                                       state)
                 state)))
     (value nil))))
