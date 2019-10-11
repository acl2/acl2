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

(include-book "abstract-syntax")
(include-book "aij-notions")
(include-book "name-translation")
(include-book "test-structures")

(include-book "kestrel/std/typed-alists/symbol-string-alistp" :dir :system)
(include-book "kestrel/utilities/strings/char-kinds" :dir :system)
(include-book "std/strings/decimal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-common-translation
  :parents (atj-code-generation)
  :short "Portion of the ACL2-to-Java translation performed by ATJ
          that is common to the deep and shallow embedding approaches."
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
