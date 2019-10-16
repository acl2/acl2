; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "common-code-generation")
(include-book "pre-translation")
(include-book "post-translation")
(include-book "primitives")

(include-book "kestrel/std/basic/organize-symbols-by-pkg" :dir :system)
(include-book "kestrel/std/basic/symbol-package-name-lst" :dir :system)
(include-book "kestrel/std/system/ubody" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-shallow-code-generation
  :parents (atj-code-generation)
  :short "Code generation that is specific to the shallow embedding approach."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-integer-field-name ((integer integerp))
  :returns (name stringp)
  :short "Generate the name of the Java field for an ACL2 integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each quoted integer constant in the ACL2 code
     is translated to a static final field
     that is calculate once at class initialization time
     and then just referenced in the Java code.
     Since ACL2 integers are objects,
     this avoids recalculating the object every time
     the shallowly embedded quoted integer constant
     is executed in the Java code.")
   (xdoc::p
    "The name of the field consists of the decimal digits of the integer
     preceded by @('$CONST_'), if the integer is non-negative.
     For a negative integer, we put @('minus') just before the digits.."))
  (str::cat "$CONST_" (if (>= integer 0)
                          (str::natstr integer)
                        (str::cat "minus" (str::natstr (- integer))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-integer ((integer integerp))
  :returns (expr jexprp)
  :short "Generate a shallowly embedded ACL2 integer."
  :long
  (xdoc::topstring-p
   "As explained in @(tsee atj-gen-shallow-integer-field-name),
    we translate each quoted integer to the corresponding field name.")
  (jexpr-name (atj-gen-shallow-integer-field-name integer)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-symbol ((symbol symbolp))
  :returns (expr jexprp)
  :short "Generate a shallowly embedded ACL2 symbol."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee atj-gen-symbol),
     which can be used in both deep and shallow embedding,
     but it is specialized to the shallow embedding
     for increasing efficiency and readability.")
   (xdoc::p
    "Since AIJ has a number of constants (i.e. static final fields)
     for certain common symbols,
     we just reference the appropriate constant
     if the symbol in question is among those symbols.
     Otherwise, we build it in the general way.
     Overall, this makes the generated Java code faster.")
   (xdoc::p
    "We reference the constants without the class name
     because we import all these constants;
     see @(tsee atj-gen-shallow-jcunit)."))
  (b* ((pair (assoc-eq symbol *aij-symbol-constants*)))
    (if pair
        (jexpr-name (cdr pair))
      (jexpr-smethod *aij-type-symbol*
                     "make"
                     (list (atj-gen-jstring
                            (symbol-package-name symbol))
                           (atj-gen-jstring
                            (symbol-name symbol)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-gen-shallow-value
  :short "Generate a shallowly  embedded ACL2 value."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently, this is essentially like @(tsee atj-gen-value),
     which can be used in both deep and shallow embedding,
     but it uses
     @(tsee atj-gen-shallow-symbol) instead of @(tsee atj-gen-symbol),
     and @(tsee atj-gen-shallow-integer) instead of @(tsee atj-gen-integer).")
   (xdoc::@def "atj-gen-shallow-value")
   (xdoc::@def "atj-gen-shallow-cons"))

  (define atj-gen-shallow-cons ((conspair consp)
                                (jvar-value-base stringp)
                                (jvar-value-index posp))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index)))
    :parents nil
    (b* (((unless (mbt (consp conspair)))
          (mv nil (jexpr-name "irrelevant") jvar-value-index))
         ((mv car-block
              car-expr
              jvar-value-index) (atj-gen-shallow-value (car conspair)
                                                       jvar-value-base
                                                       jvar-value-index))
         ((mv car-locvar-block
              car-jvar
              jvar-value-index) (atj-gen-jlocvar-indexed *aij-type-value*
                                                         jvar-value-base
                                                         jvar-value-index
                                                         car-expr))
         ((mv cdr-block
              cdr-expr
              jvar-value-index) (atj-gen-shallow-value (cdr conspair)
                                                       jvar-value-base
                                                       jvar-value-index))
         ((mv cdr-locvar-block
              cdr-jvar
              jvar-value-index) (atj-gen-jlocvar-indexed *aij-type-value*
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

  (define atj-gen-shallow-value (value
                                 (jvar-value-base stringp)
                                 (jvar-value-index posp))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-value-index posp :hyp (posp jvar-value-index)))
    :parents nil
    (cond ((characterp value) (mv nil
                                  (atj-gen-char value)
                                  jvar-value-index))
          ((stringp value) (mv nil
                               (atj-gen-string value)
                               jvar-value-index))
          ((symbolp value) (mv nil
                               (atj-gen-shallow-symbol value)
                               jvar-value-index))
          ((integerp value) (mv nil
                                (atj-gen-shallow-integer value)
                                jvar-value-index))
          ((rationalp value) (mv nil
                                 (atj-gen-rational value)
                                 jvar-value-index))
          ((acl2-numberp value) (mv nil
                                    (atj-gen-number value)
                                    jvar-value-index))
          ((consp value) (atj-gen-shallow-cons value
                                               jvar-value-base
                                               jvar-value-index))
          (t (prog2$ (raise "Internal error: the value ~x0 is a bad atom."
                            value)
                     (mv nil (jexpr-name "irrelevant") jvar-value-index))))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-SHALLOW-CONS decreases:
    :measure (two-nats-measure (acl2-count value) 1))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-gen-shallow-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fnname ((fn symbolp)
                                (pkg-class-names string-string-alistp)
                                (fn-method-names symbol-string-alistp)
                                (curr-pkg stringp))
  :guard (not (equal curr-pkg ""))
  :returns (method-name stringp)
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
     @('<class>.<method>') in Java code,
     not dissmilarly to @('<pkg>::<fn>') in ACL2.
     However, inside @('<class>'), it suffices to use @('<method>'),
     which is more readable.
     Furthermore, since we generate method synonyms under certain conditions,
     as explained in @(tsee atj-gen-shallow-fnsynonym),
     it suffices to use @('<method>')
     if the function is imported by the package.
     Thus, we prepend the Java class name to the Java method name
     if and only if the current ACL2 package (the @('curr-pkg') argument)
     differs from the ACL2 function's package
     and the package does not import the function.")
   (xdoc::p
    "The Java class name @('<class>') is looked up
     in the alist @('pkg-class-names'),
     and the Java method name @('<method>') is looked up
      in the alist @('fn-method-names')."))
  (b* ((pkg (symbol-package-name fn))
       (class? (if (or (equal pkg curr-pkg)
                       (member-eq fn (pkg-imports curr-pkg)))
                   ""
                 (b* ((pair (assoc-equal pkg pkg-class-names))
                      ((unless (consp pair))
                       (raise "Internal error: ~
                                no class name for package name ~x0." pkg)
                       "")
                      (class (cdr pair)))
                   (str::cat class "."))))
       (pair (assoc-eq fn fn-method-names))
       ((unless (consp pair))
        (raise "Internal error: no method name for function ~x0." fn)
        "")
       (method (cdr pair)))
    (str::cat class? method)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-let-bindings ((vars symbol-listp)
                                      (blocks jblock-listp)
                                      (exprs jexpr-listp))
  :guard (and (int= (len blocks) (len vars))
              (int= (len exprs) (len vars)))
  :returns (block jblockp :hyp (jblock-listp blocks))
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
       (expr (car exprs))
       ((mv var new?) (atj-unmark-var var))
       ((mv var type) (atj-type-unannotate-var var))
       (jvar (symbol-name var))
       (var-block (if new?
                      (jblock-locvar (atj-type-to-jtype type) jvar expr)
                    (jblock-asg (jexpr-name jvar) expr)))
       (first-block (append (car blocks) var-block))
       (rest-block (atj-gen-shallow-let-bindings (cdr vars)
                                                 (cdr blocks)
                                                 (cdr exprs))))
    (append first-block rest-block)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-convert-expr-from-jint-to-value ((expr jexprp))
  :returns (new-expr jexprp)
  :short "Convert a Java expression from type @('int') to type @('Acl2Value')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee atj-adapt-expr-to-type),
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
  (b* ((acl2-integer-expr (jexpr-smethod *aij-type-int*
                                         "make"
                                         (list expr)))
       (acl2-symbol-nil-expr (jexpr-name "NIL"))
       (acl2-inner-cons-expr (jexpr-smethod *aij-type-cons*
                                            "make"
                                            (list acl2-integer-expr
                                                  acl2-symbol-nil-expr)))
       (acl2-keyword-int-expr (jexpr-smethod *aij-type-symbol*
                                             "makeKeyword"
                                             (list
                                              (jexpr-literal-string "INT"))))
       (acl2-outer-cons-expr (jexpr-smethod *aij-type-cons*
                                            "make"
                                            (list acl2-keyword-int-expr
                                                  acl2-inner-cons-expr))))
    acl2-outer-cons-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-convert-expr-from-value-to-jint ((expr jexprp))
  :returns (new-expr jexprp)
  :short "Convert a Java expression from type @('Acl2Value') to type @('int')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee atj-adapt-expr-to-type),
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
  (b* ((acl2-outer-cons-expr (jexpr-paren (jexpr-cast *aij-type-cons* expr)))
       (acl2-cdr-expr (jexpr-imethod acl2-outer-cons-expr "getCdr" nil))
       (acl2-inner-cons-expr (jexpr-paren
                              (jexpr-cast *aij-type-cons* acl2-cdr-expr)))
       (acl2-car-expr (jexpr-imethod acl2-inner-cons-expr "getCar" nil))
       (acl2-integer-expr (jexpr-paren
                           (jexpr-cast *aij-type-int* acl2-car-expr))))
    (jexpr-imethod acl2-integer-expr "getJavaInt" nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-adapt-expr-to-type ((expr jexprp)
                                (src-type atj-typep)
                                (dst-type atj-typep))
  :returns (new-expr jexprp :hyp (jexprp expr))
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
     via @(tsee atj-convert-expr-from-jint-to-value),
     and then we cast to the other type
     (unless the other type is already @(':value')).
     To convert to @(':jint') from any other type,
     we use @(tsee atj-convert-expr-from-value-to-jint);
     note that any other type is a subtype of @('Acl2Value') in Java,
     so there is not need for casts.
     To convert between the AIJ types,
     if the source type is a subtype of or the same type as
     the destination type (checked via @(tsee atj-type-subeqp)),
     we leave the expression unchanged;
     otherwise, we insert a cast to the destination type,
     which is expected to always succeed
     under the assumption of guard verification."))
  (cond ((eq src-type dst-type) expr)
        ((eq src-type :jint)
         (b* ((acl2-value-expr (atj-convert-expr-from-jint-to-value expr)))
           (if (eq dst-type :value)
               acl2-value-expr
             (jexpr-cast (atj-type-to-jtype dst-type) acl2-value-expr))))
        ((eq dst-type :jint)
         (atj-convert-expr-from-value-to-jint expr))
        ((atj-type-subeqp src-type dst-type) expr)
        (t (jexpr-cast (atj-type-to-jtype dst-type) expr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-adapt-exprs-to-types ((exprs jexpr-listp)
                                  (src-types atj-type-listp)
                                  (dst-types atj-type-listp))
  :guard (and (= (len exprs) (len src-types))
              (= (len exprs) (len dst-types)))
  :returns (new-exprs jexpr-listp :hyp (jexpr-listp exprs))
  :short "Lift @(tsee atj-adapt-expr-to-type) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for all the arguments of a function call."))
  (cond ((endp exprs) nil)
        (t (cons (atj-adapt-expr-to-type (car exprs)
                                         (car src-types)
                                         (car dst-types))
                 (atj-adapt-exprs-to-types (cdr exprs)
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
    :returns (mv (block jblockp)
                 (expr jexprp)
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
      "if (<a-expr> == NIL) {"
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
      "<a-expr> == NIL ? <c-expr> : <b-expr>"))
    (b* (((mv test-block
              test-expr
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
         ((mv else-block
              else-expr
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
         ((mv then-block
              then-expr
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
                     (null then-block)
                     (null else-block)))
          (b* ((block test-block)
               (expr (jexpr-cond (jexpr-binary (jbinop-eq)
                                               test-expr
                                               (jexpr-name "NIL"))
                                 else-expr
                                 then-expr)))
            (mv block
                expr
                jvar-value-index
                jvar-result-index)))
         (jtype (atj-type-to-jtype type))
         ((mv result-locvar-block jvar-result jvar-result-index)
          (atj-gen-jlocvar-indexed jtype
                                   jvar-result-base
                                   jvar-result-index
                                   (jexpr-literal-null)))
         (if-block (jblock-ifelse
                    (jexpr-binary (jbinop-eq)
                                  test-expr
                                  (jexpr-name "NIL"))
                    (append else-block
                            (jblock-asg-name jvar-result else-expr))
                    (append then-block
                            (jblock-asg-name jvar-result then-expr))))
         (block (append test-block
                        result-locvar-block
                        if-block))
         (expr (jexpr-name jvar-result)))
      (mv block
          expr
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
    :returns (mv (block jblockp)
                 (expr jexprp)
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
      "if (<result> == NIL) {"
      "    <b-blocks>"
      "    <result> = <b-expr>;")
     (xdoc::p
      "and the Java expression @('<result>')."))
    (b* (((mv first-block
              first-expr
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
         ((mv second-block
              second-expr
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
         ((mv result-locvar-block jvar-result jvar-result-index)
          (atj-gen-jlocvar-indexed jtype
                                   jvar-result-base
                                   jvar-result-index
                                   first-expr))
         (if-block (jblock-if
                    (jexpr-binary (jbinop-eq)
                                  (jexpr-name jvar-result)
                                  (jexpr-name "NIL"))
                    (append second-block
                            (jblock-asg-name jvar-result second-expr))))
         (block (append first-block
                        result-locvar-block
                        if-block))
         (expr (jexpr-name jvar-result)))
      (mv block
          expr
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
    :returns (mv (block jblockp)
                 (expr jexprp)
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
               (expr (if (>= int 0)
                         (jexpr-literal-integer-decimal int)
                       (jexpr-unary (junop-uminus)
                                    (jexpr-literal-integer-decimal
                                     (- int)))))
               (expr (atj-adapt-expr-to-type expr :jint dst-type)))
            (mv nil
                (atj-adapt-expr-to-type expr src-type dst-type)
                jvar-value-index
                jvar-result-index))
        (b* (((mv arg-block
                  arg-expr
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
             (expr (atj-adapt-expr-to-type arg-expr :integer :jint)))
          (mv arg-block
              (atj-adapt-expr-to-type expr src-type dst-type)
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
    :returns (mv (block jblockp)
                 (expr jexprp)
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
       via @('atj-adapt-expr-to-type').
       Finally, we generate a Java binary expression
       whose operator corresponds to the function.
       The type of the function application is @(':jint').
       We parenthesize the Java expression
       to avoid errors due to operator precedences
       when expressions are nested;
       in the future we should take precedences into account
       to avoid unnecessary parentheses and make the code more readable
       (it may be better to handle this in the pretty-printer)."))
    (b* (((mv left-block
              left-expr
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
         ((mv right-block
              right-expr
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
         (expr (jexpr-paren (jexpr-binary binop left-expr right-expr)))
         (block (append left-block right-block)))
      (mv block
          (atj-adapt-expr-to-type expr src-type dst-type)
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
    :returns (mv (block jblockp)
                 (expr jexprp)
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
         ((mv arg-blocks
              arg-exprs
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
          (b* ((expr (jexpr-method
                      (atj-gen-shallow-fnname fn
                                              pkg-class-names
                                              fn-method-names
                                              curr-pkg)
                      arg-exprs))
               (expr (atj-adapt-expr-to-type expr src-type dst-type)))
            (mv (flatten arg-blocks)
                expr
                jvar-value-index
                jvar-result-index)))
         ((mv lambda-block
              lambda-expr
              jvar-value-index
              jvar-result-index) (atj-gen-shallow-lambda (lambda-formals fn)
                                                         (lambda-body fn)
                                                         arg-blocks
                                                         arg-exprs
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
      (mv lambda-block
          lambda-expr
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
                                  (arg-blocks jblock-listp)
                                  (arg-exprs jexpr-listp)
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
    :guard (and (int= (len arg-blocks) (len formals))
                (int= (len arg-exprs) (len formals))
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp :hyp (jblock-listp arg-blocks))
                 (expr jexprp)
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
    (b* ((let-block (atj-gen-shallow-let-bindings formals
                                                  arg-blocks
                                                  arg-exprs))
         ((mv body-block
              body-expr
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
      (mv (append let-block body-block)
          (atj-adapt-expr-to-type body-expr src-type dst-type)
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
    :returns (mv (block jblockp)
                 (expr jexprp)
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
               (expr (jexpr-name (symbol-name var)))
               (expr (atj-adapt-expr-to-type expr src-type dst-type)))
            (mv nil expr jvar-value-index jvar-result-index)))
         ((when (fquotep term))
          (b* ((value (unquote-term term))
               ((mv block expr jvar-value-index)
                (atj-gen-shallow-value value jvar-value-base jvar-value-index))
               (expr (atj-adapt-expr-to-type expr src-type dst-type)))
            (mv block expr jvar-value-index jvar-result-index))))
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
    :returns (mv (blocks jblock-listp)
                 (expr jexpr-listp)
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp)."))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Lift @(tsee atj-gen-shallow-term) to lists."
    (if (endp terms)
        (mv nil nil jvar-value-index jvar-result-index)
      (b* (((mv first-block
                first-expr
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
           ((mv rest-blocks
                rest-exprs
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
        (mv (cons first-block rest-blocks)
            (cons first-expr rest-exprs)
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
  :guard (and (aij-nativep fn)
              (equal (symbol-package-name fn) curr-pkg)
              (not (equal curr-pkg "")))
  :verify-guards nil
  :returns (method jmethodp)
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
  (b* ((method-name (atj-gen-shallow-fnname fn
                                            pkg-class-names
                                            fn-method-names
                                            curr-pkg))
       (method-param-names
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
       (method-params (atj-gen-paramlist method-param-names
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
       (jcall-arg-exprs (jexpr-name-list method-param-names))
       (jcall (jexpr-smethod *aij-type-native-fn*
                             jcall-method-name
                             jcall-arg-exprs))
       (method-body (jblock-return jcall)))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type (atj-type-to-jtype fn-out-type))
                  :name method-name
                  :params method-params
                  :throws (list *aij-class-eval-exc*)
                  :body method-body))
  :guard-hints (("Goal" :in-theory (enable aij-nativep primitivep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-quoted-integers-in-term
  :short "Collect all the quoted integers in a term."
  :long
  (xdoc::topstring
   "We return all the integers that appear directly quoted in the term.
    That is, for each sub-term of the form @('(quote <integer>)'),
    we return @('<integer>').
    This excludes integers that occur inside other quoted values,
    e.g. @('(quote (<integer> . ...))').
    The result list has no duplicates.")

  (define atj-quoted-integers-in-term ((term pseudo-termp))
    :returns (integers integer-listp)
    (b* (((when (variablep term)) nil)
         ((when (fquotep term)) (b* ((value (unquote-term term)))
                                  (if (integerp value)
                                      (list value)
                                    nil)))
         (integers-in-args (atj-quoted-integers-in-terms (fargs term)))
         (fn (ffn-symb term)))
      (if (flambdap fn)
          (union$ integers-in-args
                  (atj-quoted-integers-in-term (lambda-body fn)))
        integers-in-args)))

  (define atj-quoted-integers-in-terms ((terms pseudo-term-listp))
    :returns (integers integer-listp)
    (cond ((endp terms) nil)
          (t (union$ (atj-quoted-integers-in-term (car terms))
                     (atj-quoted-integers-in-terms (cdr terms))))))

  :prepwork
  ((local (include-book "std/typed-lists/integer-listp" :dir :system)))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-quoted-integers-in-term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fndef ((fn symbolp)
                               (pkg-class-names string-string-alistp)
                               (fn-method-names symbol-string-alistp)
                               (guards$ booleanp)
                               (verbose$ booleanp)
                               (curr-pkg stringp)
                               (wrld plist-worldp))
  :guard (and (equal (symbol-package-name fn) curr-pkg)
              (not (equal curr-pkg "")))
  :returns (mv (method jmethodp)
               (quoted-integers integer-listp))
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
     followed by a @('return') statement with that Java expression.")
   (xdoc::p
    "We also collect and return all the quoted integers
     in the pre-translated function body.
     These are used to generate (in other code generation functions)
     the corresponding Java fields;
     see @(tsee atj-gen-shallow-integer) for motivation.
     The list of quoted integers has no duplicates."))
  (b* (((run-when verbose$)
        (cw "  ~s0~%" fn))
       (formals (formals fn wrld))
       (body (ubody fn wrld))
       (fn-type (atj-get-function-type fn guards$ wrld))
       (in-types (atj-function-type->inputs fn-type))
       (out-type (atj-function-type->output fn-type))
       ((mv formals body)
        (atj-pre-translate fn formals body in-types out-type nil guards$ wrld))
       (quoted-integers (atj-quoted-integers-in-term body))
       (method-name (atj-gen-shallow-fnname fn
                                            pkg-class-names
                                            fn-method-names
                                            curr-pkg))
       ((mv formals &) (atj-unmark-vars formals))
       ((mv formals &) (atj-type-unannotate-vars formals))
       (method-params (atj-gen-paramlist (symbol-name-lst formals)
                                         (atj-types-to-jtypes in-types)))
       ((mv body-block body-expr & &)
        (atj-gen-shallow-term body
                              "$value" 1
                              "$result" 1
                              pkg-class-names
                              fn-method-names
                              curr-pkg
                              guards$
                              wrld))
       (method-body (append body-block
                            (jblock-return body-expr)))
       (method-body (atj-post-translate method-body))
       (method (make-jmethod :access (jaccess-public)
                             :abstract? nil
                             :static? t
                             :final? nil
                             :synchronized? nil
                             :native? nil
                             :strictfp? nil
                             :result (jresult-type (atj-type-to-jtype out-type))
                             :name method-name
                             :params method-params
                             :throws (list *aij-class-eval-exc*)
                             :body method-body)))
    (mv method quoted-integers)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fn ((fn symbolp)
                            (pkg-class-names string-string-alistp)
                            (fn-method-names symbol-string-alistp)
                            (guards$ booleanp)
                            (verbose$ booleanp)
                            (curr-pkg stringp)
                            (wrld plist-worldp))
  :guard (and (equal (symbol-package-name fn) curr-pkg)
              (not (equal curr-pkg "")))
  :returns (mv (method jmethodp)
               (quoted-integers integer-listp))
  :verify-guards nil
  :short "Generate a shallowly embedded
          ACL2 function natively implemented in AIJ
          or ACL2 function definition."
  :long
  (xdoc::topstring-p
   "We also return the list of quoted integers:
    see @(tsee atj-gen-shallow-fndef).
    This is @('nil') for native functions.")
  (if (aij-nativep fn)
      (mv (atj-gen-shallow-fnnative fn
                                    pkg-class-names
                                    fn-method-names
                                    guards$
                                    curr-pkg
                                    wrld)
          nil)
    (atj-gen-shallow-fndef fn
                           pkg-class-names
                           fn-method-names
                           guards$
                           verbose$
                           curr-pkg
                           wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fns ((fns symbol-listp)
                             (pkg-class-names string-string-alistp)
                             (fn-method-names symbol-string-alistp)
                             (guards$ booleanp)
                             (verbose$ booleanp)
                             (curr-pkg stringp)
                             (wrld plist-worldp))
  :guard (and (equal (symbol-package-name-lst fns)
                     (repeat (len fns) curr-pkg))
              (not (equal curr-pkg "")))
  :returns (mv (methods jmethod-listp)
               (quoted-integers integer-listp))
  :verify-guards nil
  :short "Lift @(tsee atj-gen-shallow-fn) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function is called on the functions to translate to Java
     that are all in the same package, namely @('curr-pkg').")
   (xdoc::p
    "The quoted integers for all the functions are all joined together,
     without duplicates."))
  (b* (((when (endp fns)) (mv nil nil))
       ((mv first-method
            first-qints) (atj-gen-shallow-fn (car fns)
                                             pkg-class-names
                                             fn-method-names
                                             guards$
                                             verbose$
                                             curr-pkg
                                             wrld))
       ((mv rest-methods
            rest-qints) (atj-gen-shallow-fns (cdr fns)
                                             pkg-class-names
                                             fn-method-names
                                             guards$
                                             verbose$
                                             curr-pkg
                                             wrld))
       (methods (cons first-method rest-methods))
       (qints (union$ first-qints rest-qints)))
    (mv methods qints))
  :prepwork
  ((local (include-book "std/typed-lists/integer-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fnsynonym-formals ((n natp))
  :returns (formals string-listp)
  :short "Generate shallowly embedded formal parameters for
          the function synonyms generated by @(tsee atj-gen-shallow-fnsynonym)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The exact formal parameters are not important,
     so for now we just generate @('x1'), @('x2'), ..., @('xn'),
     where @('n') is the arity.
     These are valid Java parameter names."))
  (atj-gen-shallow-fnsynonym-formals-aux n nil)

  :prepwork
  ((define atj-gen-shallow-fnsynonym-formals-aux ((n natp) (acc string-listp))
     :returns (formals string-listp :hyp (string-listp acc))
     (cond ((zp n) acc)
           (t (atj-gen-shallow-fnsynonym-formals-aux
               (1- n) (cons (str::cat "x" (str::natstr n)) acc)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fnsynonym ((fn symbolp)
                                   (pkg-class-names string-string-alistp)
                                   (fn-method-names symbol-string-alistp)
                                   (guards$ booleanp)
                                   (curr-pkg stringp)
                                   (wrld plist-worldp))
  :guard (member-eq fn (pkg-imports curr-pkg))
  :returns (method jmethodp)
  :verify-guards nil
  :short "Generate a shallowly embedded ACL2 function synonym."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to mimic, as far as name references are concerned,
     the importing of a function symbol in a package.")
   (xdoc::p
    "For instance,
     the built-in @(tsee cons) is in the @('\"COMMON-LISP\"') package
     (i.e. that is its @(tsee symbol-package-name)),
     but that symbol is imported by the @('\"ACL2\"') package,
     making it referenceable as @('acl2::cons')
     besides the ``canonical'' @('common-lisp::cons').
     In particular, in the @('\"ACL2\"')
     it can be referenced as just @('cons'),
     which makes ACL2 code much more readable.")
   (xdoc::p
    "In the shallow embedding we translate these two ACL2 packages
     to two different Java classes,
     and the method that corresponds to @(tsee cons)
     is in the class for @('\"COMMON-LISP\"'),
     where the method can be referenced by simple name,
     without qualifying it with the class name.
     But in classes for other packages, e.g. the class for @('\"ACL2\"'),
     it would have to be qualified.")
   (xdoc::p
    "To avoid this verbosity,
     we generate a ``synonym'' of the method for @(tsee cons)
     in each class of a package that imports @(tsee cons),
     e.g. in the class for @('\"ACL2\"').
     This function generates this synonym method,
     which is just defined to call the method
     in the class of its proper package.
     This makes the generated Java code much more readable.
     It is hoped that the JVM JIT may optimize the indirection away.")
   (xdoc::p
    "The @('fn') parameter is the name of the ACL2 function in question,
     e.g. @(tsee cons) in the example above.
     The @('curr-pkg') parameter is the one that imports @('fn'),
     e.g. @('\"ACL2\"') in the example above.")
   (xdoc::p
    "We pass the @(tsee symbol-package-name) of @('fn')
     to @(tsee atj-gen-shallow-fnname)
     to ensure that the result is the simple name of the method,
     which goes into the generated method declaration."))
  (b* ((fn-type (atj-get-function-type fn guards$ wrld))
       (in-types (atj-function-type->inputs fn-type))
       (out-type (atj-function-type->output fn-type))
       (fn-pkg (symbol-package-name fn))
       (method-name (atj-gen-shallow-fnname fn
                                            pkg-class-names
                                            fn-method-names
                                            fn-pkg))
       (method-param-names (atj-gen-shallow-fnsynonym-formals (arity fn wrld)))
       (method-params (atj-gen-paramlist method-param-names
                                         (atj-types-to-jtypes in-types)))
       (pkg+class (assoc-equal fn-pkg pkg-class-names))
       ((unless (consp pkg+class))
        (raise "Internal error: no class name for package name ~x0." curr-pkg)
        ;; irrelevant:
        (make-jmethod :access (jaccess-public)
                      :result (jresult-type (atj-type-to-jtype :value))
                      :name ""
                      :body (jblock-return nil)))
       (class (cdr pkg+class))
       (method-body (jblock-return
                     (jexpr-smethod (jtype-class class)
                                    method-name
                                    (jexpr-name-list method-param-names)))))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type (atj-type-to-jtype out-type))
                  :name method-name
                  :params method-params
                  :throws (list *aij-class-eval-exc*)
                  :body method-body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fnsynonyms ((fns symbol-listp)
                                    (pkg-class-names string-string-alistp)
                                    (fn-method-names symbol-string-alistp)
                                    (guards$ booleanp)
                                    (curr-pkg stringp)
                                    (wrld plist-worldp))
  :guard (subsetp-equal fns (pkg-imports curr-pkg))
  :returns (methods jmethod-listp)
  :verify-guards nil
  :short "Lift @(tsee atj-gen-shallow-fnsynonym) to lists."
  (cond ((endp fns) nil)
        (t (cons (atj-gen-shallow-fnsynonym (car fns)
                                            pkg-class-names
                                            fn-method-names
                                            guards$
                                            curr-pkg
                                            wrld)
                 (atj-gen-shallow-fnsynonyms (cdr fns)
                                             pkg-class-names
                                             fn-method-names
                                             guards$
                                             curr-pkg
                                             wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fns-in-pkg ((fns-in-pkg symbol-listp)
                                    (fns-to-translate symbol-listp)
                                    (pkg stringp)
                                    (pkg-class-names string-string-alistp)
                                    (fn-method-names symbol-string-alistp)
                                    (guards$ booleanp)
                                    (verbose$ booleanp)
                                    (wrld plist-worldp))
  :guard (equal (symbol-package-name-lst fns-in-pkg)
                (repeat (len fns-in-pkg) pkg))
  :returns (mv (class jclassp)
               (quoted-integers integer-listp))
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
     that are all in the same package, namely @('pkg').")
   (xdoc::p
    "We also generate additional methods for all the functions to translate
     that are in other ACL2 packages but that are imported by @('pkg').
     See @(tsee atj-gen-shallow-fnsynonym) for motivation."))
  (b* ((pair (assoc-equal pkg pkg-class-names))
       ((unless (consp pair))
        (raise "Internal error: no class name for package name ~x0." pkg)
        ;; irrelevant:
        (mv (make-jclass :access (jaccess-public) :name "") nil))
       (class-name (cdr pair))
       ((mv fn-methods qints) (atj-gen-shallow-fns fns-in-pkg
                                                   pkg-class-names
                                                   fn-method-names
                                                   guards$
                                                   verbose$
                                                   pkg
                                                   wrld))
       (imported-fns (intersection-eq fns-to-translate (pkg-imports pkg)))
       (synonym-methods (atj-gen-shallow-fnsynonyms imported-fns
                                                    pkg-class-names
                                                    fn-method-names
                                                    guards$
                                                    pkg
                                                    wrld))
       (all-methods (append fn-methods synonym-methods))
       (class (make-jclass :access (jaccess-public)
                           :abstract? nil
                           :static? t
                           :final? nil
                           :strictfp? nil
                           :name class-name
                           :superclass? nil
                           :superinterfaces nil
                           :body (jmethods-to-jcbody-elements all-methods))))
    (mv class qints)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fns-by-pkg ((fns-to-translate symbol-listp)
                                    (fns-by-pkg string-symbollist-alistp)
                                    (guards$ booleanp)
                                    (java-class$ stringp)
                                    (verbose$ booleanp)
                                    (wrld plist-worldp))
  :returns (mv (classes jclass-listp)
               (pkg-class-names "A @(tsee string-string-alistp).")
               (fn-method-names "A @(tsee symbol-string-alistp).")
               (quoted-integers integer-listp))
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
     the Java test class.")
   (xdoc::p
    "We also return all the quoted integers
     from the pre-translated function bodies.
     The list of integers is without duplicates."))
  (b* ((pkgs (remove-duplicates-equal (strip-cars fns-by-pkg)))
       (pkg-class-names (atj-pkgs-to-classes pkgs java-class$))
       (fn-method-names (atj-fns-to-methods
                         (remove-duplicates-equal fns-to-translate)))
       ((mv classes qints) (atj-gen-shallow-fns-by-pkg-aux pkgs
                                                           fns-to-translate
                                                           fns-by-pkg
                                                           pkg-class-names
                                                           fn-method-names
                                                           guards$
                                                           java-class$
                                                           verbose$
                                                           wrld)))
    (mv classes
        pkg-class-names
        fn-method-names
        qints))

  :prepwork

  ((local (include-book "std/typed-lists/integer-listp" :dir :system))

   (define atj-gen-shallow-fns-by-pkg-aux
     ((pkgs string-listp)
      (fns-to-translate symbol-listp)
      (fns-by-pkg string-symbollist-alistp)
      (pkg-class-names string-string-alistp)
      (fn-method-names symbol-string-alistp)
      (guards$ booleanp)
      (java-class$ stringp)
      (verbose$ booleanp)
      (wrld plist-worldp))
     :returns (mv (classes jclass-listp)
                  (quoted-integers integer-listp))
     :verify-guards nil
     (b* (((when (endp pkgs)) (mv nil nil))
          (pkg (car pkgs))
          (fns-in-pkg (cdr (assoc-equal pkg fns-by-pkg)))
          ((mv first-class
               first-qints) (atj-gen-shallow-fns-in-pkg fns-in-pkg
                                                        fns-to-translate
                                                        pkg
                                                        pkg-class-names
                                                        fn-method-names
                                                        guards$
                                                        verbose$
                                                        wrld))
          ((mv rest-classes
               rest-qints) (atj-gen-shallow-fns-by-pkg-aux (cdr pkgs)
                                                           fns-to-translate
                                                           fns-by-pkg
                                                           pkg-class-names
                                                           fn-method-names
                                                           guards$
                                                           java-class$
                                                           verbose$
                                                           wrld))
          (classes (cons first-class rest-classes))
          (qints (union$ first-qints rest-qints)))
       (mv classes qints)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-integer-field ((integer integerp))
  :returns (field jfieldp)
  :short "Generate a Java field for an ACL2 integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee atj-gen-shallow-integer) for motivation.")
   (xdoc::p
    "This is a private static final field with an initializer.
     The initializer constructs the integer value."))
  (b* ((name (atj-gen-shallow-integer-field-name integer))
       (init (atj-gen-integer integer)))
    (make-jfield :access (jaccess-private)
                 :static? t
                 :final? t
                 :transient? nil
                 :volatile? nil
                 :type *aij-type-int*
                 :name name
                 :init init)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-integer-fields ((integers integer-listp))
  :returns (fields jfield-listp)
  :short "Lift @(tsee atj-gen-shallow-integer-field) to lists."
  (cond ((endp integers) nil)
        (t (cons (atj-gen-shallow-integer-field (car integers))
                 (atj-gen-shallow-integer-fields (cdr integers))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-static-initializer ((pkgs string-listp))
  :returns (initializer jcinitializerp)
  :short "Generate the static initializer
          for the main (i.e. non-test) Java class declaration,
          in the shallow embedding approach."
  :long
  (xdoc::topstring
   (xdoc::p
    "This contains code to initialize the ACL2 environment:
     we build the Java representation of the ACL2 packages,
     and we set the package witness."))
  (b* ((pkgs-block (atj-gen-pkgs pkgs))
       (pkg-witness-block (atj-gen-pkg-witness)))
    (make-jcinitializer :static? t
                        :code (append pkgs-block
                                      pkg-witness-block))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-init-method ()
  :returns (method jmethodp)
  :short "Generate the Java public method to initialize the ACL2 environment,
          in the shallow embedding approach."
  :long
  (xdoc::topstring
   (xdoc::p
    "This method just checks and sets the initialization flag,
     because the actual initialization of the ACL2 environment
     is performed by the static initializer generated by
     @(tsee atj-gen-shallow-static-initializer).
     Still, external users of the generated Java code must call this method
     to trigger, if it has not happened already,
     the initialization of the Java class
     and thus the execution of the static initializer.
     This seems a bit clumsy; it will be improved in the future."))
  (b* ((exception-message "The ACL2 environment is already initialized.")
       (exception-message-expr (atj-gen-jstring exception-message))
       (throw-block (jblock-throw (jexpr-newclass
                                   (jtype-class "IllegalStateException")
                                   (list exception-message-expr))))
       (if-block (jblock-if (jexpr-name "initialized")
                            throw-block))
       (initialize-block (jblock-asg-name "initialized"
                                          (jexpr-literal-true)))
       (method-body (append if-block
                            initialize-block)))
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
                  :body method-body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-class ((pkgs string-listp)
                               (fns-to-translate symbol-listp)
                               (guards$ booleanp)
                               (java-class$ stringp)
                               (verbose$ booleanp)
                               (wrld plist-worldp))
  :returns (mv (class jclassp)
               (pkg-class-names "A @(tsee string-string-alistp).")
               (fn-method-names "A @(tsee symbol-string-alistp)."))
  :verify-guards nil
  :short "Generate the main (i.e. non-test) Java class declaration,
          in the shallow embedding approach."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a public class.
     [JLS] says that a Java implementation may require
     public classes to be in files with the same names (plus extension).
     The code that we generate satisfies this requirement.")
   (xdoc::p
    "The class contains the initialization field and method,
     the methods to build the ACL2 packages,
     the classes that contain methods for the ACL2 functions,
     the fields for quoted integers,
     and the static initializer.")
   (xdoc::p
    "It is critical that the static initializer
     comes before the fields for the quoted integers,
     so that the ACL2 environment is initialized
     before the field initializers, which construct ACL2 values,
     are executed;
     [JLS:12.4.1] says that the class initialization code
     is executed in textual order.")
   (xdoc::p
    "After the static initializer,
     we generate the fields for the quoted integers,
     followed by the initialization flag field
     (so all the fields are together).")
   (xdoc::p
    "After the fields, we generate the methods to build the packages.")
   (xdoc::p
    "We ensure that the ACL2 functions natively implemented in AIJ
     (currently the ACL2 primitive functions)
     are included,
     we organize the resulting functions by packages,
     and we proceed to generate the Java nested classes,
     after the methods to build the packages.")
   (xdoc::p
    "The initialization method is at the very end, after the nested classes.")
   (xdoc::p
    "We also return the alist from ACL2 package names to Java class names
     and the alist from ACL2 function symbols to Java method names,
     which must be eventually passed to the functions that generate
     the Java test class."))
  (b* ((static-init (atj-gen-shallow-static-initializer pkgs))
       (init-field (atj-gen-init-field))
       (init-method (atj-gen-shallow-init-method))
       ((run-when verbose$)
        (cw "~%Generating Java code for the ACL2 packages:~%"))
       (pkg-methods (atj-gen-pkg-methods pkgs verbose$))
       ((run-when verbose$)
        (cw "~%Generating Java code for the ACL2 functions:~%"))
       (fns+natives (remove-duplicates-eq
                     (append fns-to-translate
                             (strip-cars *primitive-formals-and-guards*))))
       (fns-by-pkg (organize-symbols-by-pkg fns+natives))
       ((mv fn-classes pkg-class-names fn-method-names qints)
        (atj-gen-shallow-fns-by-pkg fns+natives
                                    fns-by-pkg
                                    guards$
                                    java-class$
                                    verbose$
                                    wrld))
       (qint-fields (atj-gen-shallow-integer-fields qints))
       (body-class (append (list (jcbody-element-init static-init))
                           (jfields-to-jcbody-elements (append qint-fields
                                                               (list
                                                                init-field)))
                           (jmethods-to-jcbody-elements pkg-methods)
                           (jclasses-to-jcbody-elements fn-classes)
                           (list (jcbody-element-member
                                  (jcmember-method init-method))))))
    (mv (make-jclass :access (jaccess-public)
                     :abstract? nil
                     :static? nil
                     :final? nil
                     :strictfp? nil
                     :name java-class$
                     :superclass? nil
                     :superinterfaces nil
                     :body body-class)
        pkg-class-names
        fn-method-names)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-symbol-imports ()
  :returns (imports jimport-listp)
  :short "Generate Java static import declarations
          for the constants for symbols in AIJ."
  (atj-gen-shallow-symbol-imports-aux (strip-cdrs *aij-symbol-constants*))

  :prepwork
  ((define atj-gen-shallow-symbol-imports-aux ((constants string-listp))
     :returns (imports jimport-listp)
     (cond ((endp constants) nil)
           (t (cons (make-jimport :static? t
                                  :target (str::cat *aij-package*
                                                    "."
                                                    *aij-class-symbol*
                                                    "."
                                                    (car constants)))
                    (atj-gen-shallow-symbol-imports-aux (cdr constants))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-jcunit ((guards$ booleanp)
                                (java-package$ maybe-stringp)
                                (java-class$ maybe-stringp)
                                (pkgs string-listp)
                                (fns-to-translate symbol-listp)
                                (verbose$ booleanp)
                                (wrld plist-worldp))
  :returns (mv (jcunit jcunitp)
               (pkg-class-names "A @(tsee string-string-alistp).")
               (fn-method-names "A @(tsee symbol-string-alistp)."))
  :verify-guards nil
  :short "Generate the main Java compilation unit,
          in the shallow embedding approach."
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
     the Java test class."))
  (b* (((mv class pkg-class-names fn-method-names)
        (atj-gen-shallow-class
         pkgs fns-to-translate guards$ java-class$ verbose$ wrld))
       (cunit
        (make-jcunit
         :package? java-package$
         :imports (append
                   (list
                    (make-jimport :static? nil
                                  :target (str::cat *aij-package* ".*"))
                    ;; keep in sync with *ATJ-DISALLOWED-CLASS-NAMES*:
                    (make-jimport :static? nil :target "java.math.BigInteger")
                    (make-jimport :static? nil :target "java.util.ArrayList")
                    (make-jimport :static? nil :target "java.util.List"))
                   (atj-gen-shallow-symbol-imports))
         :types (list class))))
    (mv cunit pkg-class-names fn-method-names)))
