; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "common-translation")
(include-book "pre-translation")
(include-book "post-translation")
(include-book "primitives")

(include-book "kestrel/std/basic/symbol-package-name-lst" :dir :system)
(include-book "kestrel/std/system/ubody" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-shallow-translation
  :parents (atj-code-generation)
  :short "Portion of the ACL2-to-Java translation performed by ATJ
          that is specific to the shallow embedding approach."
  :order-subtopics t
  :default-parent t)

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

(define atj-gen-shallow-fns ((fns-in-curr-pkg symbol-listp)
                             (pkg-class-names string-string-alistp)
                             (fn-method-names symbol-string-alistp)
                             (guards$ booleanp)
                             (verbose$ booleanp)
                             (curr-pkg stringp)
                             state)
  :guard (and (equal (symbol-package-name-lst fns-in-curr-pkg)
                     (repeat (len fns-in-curr-pkg) curr-pkg))
              (not (equal curr-pkg "")))
  :returns (jmethods jmethod-listp)
  :verify-guards nil
  :short "Lift @(tsee atj-gen-shallow-fn) to lists."
  :long
  (xdoc::topstring-p
   "This function is called on the functions to translate to Java
    that are all in the same package, namely @('curr-pkg').")
  (cond ((endp fns-in-curr-pkg) nil)
        (t (b* ((first-jmethod (atj-gen-shallow-fn (car fns-in-curr-pkg)
                                                   pkg-class-names
                                                   fn-method-names
                                                   guards$
                                                   verbose$
                                                   curr-pkg
                                                   state))
                (rest-jmethods (atj-gen-shallow-fns (cdr fns-in-curr-pkg)
                                                    pkg-class-names
                                                    fn-method-names
                                                    guards$
                                                    verbose$
                                                    curr-pkg
                                                    state)))
             (cons first-jmethod rest-jmethods)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fns-in-pkg ((fns-in-pkg symbol-listp)
                                    (pkg stringp)
                                    (pkg-class-names string-string-alistp)
                                    (fn-method-names symbol-string-alistp)
                                    (guards$ booleanp)
                                    (verbose$ booleanp)
                                    state)
  :guard (equal (symbol-package-name-lst fns-in-pkg)
                (repeat (len fns-in-pkg) pkg))
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
     nested into the main Java class that ATJ generates.")
   (xdoc::p
    "This function is called on the functions to translate to Java
     that are all in the same package, namely @('pkg')."))
  (b* ((pair (assoc-equal pkg pkg-class-names))
       ((unless (consp pair))
        (raise "Internal error: no class name for package name ~x0." pkg)
        ;; irrelevant:
        (make-jclass :access (jaccess-public) :name ""))
       (jclass-name (cdr pair))
       (jclass-methods (atj-gen-shallow-fns fns-in-pkg
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
