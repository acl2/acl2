; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "pre-translation")
(include-book "post-translation")
(include-book "java-primitives")
(include-book "java-primitive-arrays")
(include-book "shallow-quoted-constant-generation")
(include-book "array-write-method-names")

(include-book "kestrel/std/basic/organize-symbols-by-pkg" :dir :system)
(include-book "kestrel/std/basic/symbol-package-name-lst" :dir :system)
(include-book "kestrel/std/system/check-unary-lambda-call" :dir :system)
(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "kestrel/std/system/tail-recursive-p" :dir :system)

(local (include-book "kestrel/std/basic/symbol-name-lst" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-shallow-code-generation
  :parents (atj-code-generation)
  :short "Code generation that is specific to the shallow embedding approach."
  :order-subtopics t
  :default-parent t)

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
     as explained in @(tsee atj-gen-shallow-synonym-method),
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
                 (b* ((class (atj-get-pkg-class-name pkg pkg-class-names)))
                   (str::cat class "."))))
       (method (atj-get-fn-method-name fn fn-method-names)))
    (str::cat class? method)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-mv-class-name ((types atj-type-listp))
  :guard (>= (len types) 2)
  :returns (class-name stringp)
  :short "Generate the name of the @(tsee mv) class for the given types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since Java does not allow methods to return multiple values directly,
     we need to create, for ACL2 functions that return @(tsee mv) results,
     Java classes that group these multiple values into single objects.
     There is a different class for each tuple of types
     of the multiple values.
     Here we generate the names of these classes,
     based on the ATJ types of the multiple values.")
   (xdoc::p
    "These classes have names of the form @('MV_A_B_C_...'),
     where @('A'), @('B'), @('C'), etc. correspond to the ATJ types,
     or more precisely to their Java types counterparts.
     For AIJ classes, we use the class names themselves.
     For Java primitive types, we use the primitive types themselves.
     For Java primitive array types,
     we use the element types followed by @('array').
     For instance, for the ATJ types @('(:asymbol :jint :jbyte[])'),
     the class name is @('MV_Acl2Symbol_int_bytearray').")
   (xdoc::p
    "The list of ATJ types must have at least two elements.
     It does not make sense to have a multiple value
     consisting of zero or one values."))
  (str::cat "MV" (atj-gen-shallow-mv-class-name-aux types))

  :prepwork
  ((define atj-gen-shallow-mv-class-name-aux ((types atj-type-listp))
     :returns (class-name-suffix stringp)
     (b* (((when (endp types)) "")
          (type (car types))
          (jtype (atj-type-to-jitype type))
          (first (cond
                  ((equal jtype (jtype-boolean)) "_boolean")
                  ((equal jtype (jtype-char)) "_char")
                  ((equal jtype (jtype-byte)) "_byte")
                  ((equal jtype (jtype-short)) "_short")
                  ((equal jtype (jtype-int)) "_int")
                  ((equal jtype (jtype-long)) "_long")
                  ((equal jtype (jtype-float)) "_float")
                  ((equal jtype (jtype-double)) "_double")
                  ((equal jtype (jtype-array (jtype-boolean))) "_booleanarray")
                  ((equal jtype (jtype-array (jtype-char))) "_chararray")
                  ((equal jtype (jtype-array (jtype-byte))) "_bytearray")
                  ((equal jtype (jtype-array (jtype-short))) "_shortarray")
                  ((equal jtype (jtype-array (jtype-int))) "_intarray")
                  ((equal jtype (jtype-array (jtype-long))) "_longarray")
                  ((equal jtype (jtype-array (jtype-float))) "_floatarray")
                  ((equal jtype (jtype-array (jtype-double))) "_doublearray")
                  (t (str::cat "_" (jtype-class->name jtype)))))
          (rest (atj-gen-shallow-mv-class-name-aux (cdr types))))
       (str::cat first rest))
     :verify-guards nil ; done below
     ///
     (verify-guards atj-gen-shallow-mv-class-name-aux
       :hints (("Goal" :in-theory (enable atj-type-to-jitype)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-mv-field-name ((index natp))
  :returns (field-name stringp)
  :short "Generate the name of the field with the given index
          in an @(tsee mv) class."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-gen-shallow-mv-class-name),
     we generate Java classes that represent @(tsee mv) values.
     These classes have non-private fields named after the indices (0-based)
     of the components of the @(tsee mv) values.")
   (xdoc::p
    "Currently we generate field names of the form @('$<i>'),
     where @('<i>') is the base-10 representation of the index,
     i.e. @('$0'), @('$1'), etc."))
  (str::cat "$" (natstr index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-mv-factory-method-name*
  :short "Name of the package-private static factory method
          of an @(tsee mv) class."
  :long
  (xdoc::topstring-p
   "All the @(tsee mv) classes use the same name for this method.")
  "make")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-jtype ((types atj-type-listp))
  :guard (consp types)
  :returns (jtype jtypep)
  :short "Generate a Java type, in the shallow embedding approach."
  :long
  (xdoc::topstring
   (xdoc::p
    "We map a non-empty list of ATJ types to a Java type as follows.
     If the list is a singleton,
     we map the (only) type to the corresponding Java type,
     according to @(tsee atj-type-to-jitype).
     Otherwise, we map the list of two or more types
     to the @(tsee mv) class for the types,
     according to @(tsee atj-gen-shallow-mv-class-name)."))
  (if (= (len types) 1)
      (atj-type-to-jitype (car types))
    (jtype-class (atj-gen-shallow-mv-class-name types))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-convert-expr-to-jprim ((expr jexprp) (type primitive-typep))
  :returns (new-expr jexprp)
  :short "Convert a Java expression to a Java primitive type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to translate some calls of
     Java primitive constructors like @(tsee byte-value).
     (Other calls are translated to Java literals instead.)")
   (xdoc::p
    "If the type is @('boolean'),
     the input expression must have type @('Acl2Symbol');
     see the input and output types of @(tsee boolean-value).
     In this case, we convert the expression
     by comparing it with (the Java representation of) @('nil').")
   (xdoc::p
    "If the type is @('char'), @('byte'), or @('short'),
     the input expression must have type @('Acl2Integer');
     see the input and output types of
     @(tsee char-value), @(tsee byte-value), and @(tsee short-value).
     In this case, we convert the input expression
     by extracting a Java @('int') from the @('Acl2Integer')
     and we cast to the appropriate primitive type.")
   (xdoc::p
    "If the type is @('int'),
     the input expression must have type @('Acl2Integer');
     see the input and output types of @(tsee int-value).
     In this case, we convert the input expression
     by extracting a Java @('int') from the @('Acl2Integer').")
   (xdoc::p
    "If the type is @('long'),
     the input expression must have type @('Acl2Integer');
     see the input and output types of @(tsee long-value).
     In this case, we convert the input expression
     by extracting a Java @('long') from the @('Acl2Integer').")
   (xdoc::p
    "If the type is @('float') and @('double'), an error occurs.
     These conversions are not supported yet,
     because we have only an abstract model of these two types for now."))
  (case (primitive-type-kind type)
    (:boolean (jexpr-binary (jbinop-ne) expr (atj-gen-symbol nil)))
    ((:char :byte :short) (jexpr-cast
                           (jtype-prim type)
                           (jexpr-imethod (jexpr-cast *aij-type-int* expr)
                                          "getJavaInt"
                                          nil)))
    (:int (jexpr-imethod (jexpr-cast *aij-type-int* expr) "getJavaInt" nil))
    (:long (jexpr-imethod (jexpr-cast *aij-type-int* expr) "getJavaLong" nil))
    (t (prog2$ (raise "Internal error: ~
                       cannot convert expression ~x0 to type ~x1."
                      expr type)
               (ec-call (jexpr-fix :irrelevant)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-convert-expr-from-jprim ((expr jexprp) (type primitive-typep))
  :returns (new-expr jexprp)
  :short "Convert a Java expression from a Java primitive type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to translate calls of
     Java primitive deconstructors like @(tsee byte-value->int).")
   (xdoc::p
    "If the type is @('boolean'),
     we convert it to the @('Acl2Symbol') @('t') or @('nil')
     via a Java conditional expression.")
   (xdoc::p
    "If the type is @('char'), @('byte'), @('short'), @('int'), or @('long'),
     we convert it to an @('Acl2Integer') by calling @('make').
     The method called is @('Acl2Integer.make(int)')
     if the type is @('char'), @('byte'), @('short'), or @('int'),
     while it is @('Acl2Integer.make(long)') if the type is @('long').")
   (xdoc::p
    "If the type is @('float') and @('double'), an error occurs.
     These conversions are not supported yet,
     because we have only an abstract model of these two types for now."))
  (case (primitive-type-kind type)
    (:boolean (jexpr-cond expr (atj-gen-symbol t) (atj-gen-symbol nil)))
    ((:char :byte :short :int :long) (jexpr-smethod *aij-type-int*
                                                    "make"
                                                    (list expr)))
    (t (prog2$ (raise "Internal error: ~
                       cannot convert expression ~x0 to type ~x1."
                      expr type)
               (ec-call (jexpr-fix :irrelevant)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-convert-expr-to-jprimarr-method-name ((type primitive-typep))
  :returns (method-name stringp :hyp :guard)
  :short "Name of the method to convert
          a Java expression from a Java primitive array type."
  :long
  (xdoc::topstring-p
   "See @(tsee atj-convert-expr-to-jprimarr-method).")
  (primitive-type-case type
                       :boolean "convertToBooleanArray"
                       :char "convertToCharArray"
                       :byte "convertToByteArray"
                       :short "convertToShortArray"
                       :int "convertToIntArray"
                       :long "convertToLongArray"
                       :float (prog2$
                               (raise "Internal error: type ~x0 not supported."
                                      type)
                               "irrelevant")
                       :double (prog2$
                                (raise "Internal error: type ~x0 not supported."
                                       type)
                                "irrelevant"))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-convert-expr-to-jprimarr-method ((type primitive-typep))
  :returns (method jmethodp)
  :short "Method to convert a Java expression to a Java primitive array type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to translate some calls of
     Java primitive array constructors like @(tsee byte-array->components).
     (Other calls are translated to array creation expressions instead.)")
   (xdoc::p
    "The Java expression must return an ACL2 list (assuming guard verification),
     which we want to convert to a corresponding Java array
     whose components are Java primitive values
     obtained by converting the elements of the list.
     This should be done with a Java loop, of course.
     However, we want the conversion code generated from the constructors
     to be a relatively simple ``inline'' expression.
     Thus, we generate private methods to perform the loop conversion,
     and translate the deconstructor calls to calls of these methods.")
   (xdoc::p
    "The generated method has the following form:")
   (xdoc::codeblock
    "private static <type>[] <name>(Acl2Value list) {"
    "    int length = 0;"
    "    Acl2Value saveList = list;"
    "    while (list instanceof Acl2Cons) {"
    "        ++length;"
    "        list = ((Acl2ConsPair) list).getCdr();"
    "    }"
    "    <type>[] array = new <type>(length);"
    "    int index = 0;"
    "    list = savedList;"
    "    while (index < length) {"
    "        Acl2ConsPair pair = (Acl2ConsPair) list;"
    "        array[index] = <conv-type(pair.getCar())>;"
    "        list = pair.getCdr();"
    "        ++index;"
    "    }"
    "    return array;"
    "}")
   (xdoc::p
    "where @('<type>') is a Java primitive type
     and @('<conv-type(...)>') is the conversion code
     generated by @(tsee atj-convert-expr-to-jprim)
     for that primitive type."))
  (b* ((method-name (atj-convert-expr-to-jprimarr-method-name type))
       (jtype (atj-type-to-jitype (atj-type-jprim type)))
       (array "array")
       (index "index")
       (length "length")
       (list "list")
       (pair "pair")
       (saved "savedList")
       (array[index] (jexpr-array (jexpr-name array) (jexpr-name index)))
       (pair.getcar (jexpr-imethod (jexpr-name pair) "getCar" nil))
       (conv-pair.getcar (atj-convert-expr-to-jprim pair.getcar type))
       (method-body
        (append
         (jblock-locvar (jtype-int)
                        length
                        (jexpr-literal-0))
         (jblock-locvar *aij-type-value*
                        saved
                        (jexpr-name list))
         (jblock-while (jexpr-instanceof (jexpr-name list) *aij-type-cons*)
                       (append
                        (jblock-expr (jexpr-unary (junop-preinc)
                                                  (jexpr-name length)))
                        (jblock-asg (jexpr-name list)
                                    (jexpr-imethod (jexpr-cast
                                                    *aij-type-cons*
                                                    (jexpr-name list))
                                                   "getCdr"
                                                   nil))))
         (jblock-locvar (jtype-array jtype)
                        array
                        (jexpr-newarray jtype (jexpr-name length)))
         (jblock-locvar (jtype-int)
                        index
                        (jexpr-literal-0))
         (jblock-asg (jexpr-name list)
                     (jexpr-name saved))
         (jblock-while (jexpr-binary (jbinop-lt)
                                     (jexpr-name index)
                                     (jexpr-name length))
                       (append
                        (jblock-locvar *aij-type-cons*
                                       pair
                                       (jexpr-cast *aij-type-cons*
                                                   (jexpr-name list)))
                        (jblock-asg array[index] conv-pair.getcar)
                        (jblock-asg (jexpr-name list)
                                    (jexpr-imethod (jexpr-name pair)
                                                   "getCdr"
                                                   nil))
                        (jblock-expr (jexpr-unary (junop-preinc)
                                                  (jexpr-name index)))))
         (jblock-return (jexpr-name array)))))
    (make-jmethod :access (jaccess-private)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type (jtype-array jtype))
                  :name method-name
                  :params (list (jparam nil *aij-type-value* list))
                  :throws nil
                  :body method-body))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-convert-expr-to-jprimarr ((expr jexprp) (type primitive-typep))
  :returns (new-expr jexprp)
  :short "Convert a Java expression to a Java primitive array type."
  (b* ((method-name (atj-convert-expr-to-jprimarr-method-name type)))
    (jexpr-method method-name (list expr)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-convert-expr-from-jprimarr-method-name ((type primitive-typep))
  :returns (method-name stringp :hyp :guard)
  :short "Name of the method to convert
          a Java expression from a Java primitive array type."
  :long
  (xdoc::topstring-p
   "See @(tsee atj-convert-expr-from-jprimarr-method).")
  (primitive-type-case type
                       :boolean "convertFromBooleanArray"
                       :char "convertFromCharArray"
                       :byte "convertFromByteArray"
                       :short "convertFromShortArray"
                       :int "convertFromIntArray"
                       :long "convertFromLongArray"
                       :float (prog2$
                               (raise "Internal error: type ~x0 not supported."
                                      type)
                               "irrelevant")
                       :double (prog2$
                                (raise "Internal error: type ~x0 not supported."
                                       type)
                                "irrelevant"))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-convert-expr-from-jprimarr-method ((type primitive-typep))
  :returns (method jmethodp)
  :short "Method to convert a Java expression from a Java primitive array type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to translate calls of
     Java primitive array deconstructors like @(tsee byte-array->components).")
   (xdoc::p
    "We want to convert the array to a corresponding ACL2 list,
     whose elements are instances of (subtypes of) @('Acl2Value')
     obtained by converting the components of the array.
     This should be done with a Java loop, of course.
     However, we want the conversion code generated from the deconstructors
     to be a relatively simple ``inline'' expression.
     Thus, we generate private methods to perform the loop conversion,
     and translate the deconstructor calls to calls of these methods.")
   (xdoc::p
    "This function generates these methods,
     one for each Java primitive type except @('float') and @('double').
     These methods are generated directly in the main Java class.
     The method names are chosen to avoid conflicts
     with other generated methods in the same class.")
   (xdoc::p
    "The method has the following form:")
   (xdoc::codeblock
    "private static Acl2Value <name>(<type>[] array) {"
    "    Acl2Value result = Acl2Symbol.NIL;"
    "    int index = array.length - 1;"
    "    while (index >= 0) {"
    "        result = Acl2ConsPair.make(<conv-type(array[index])>, result);"
    "        --index;"
    "    }"
    "    return result;"
    "}")
   (xdoc::p
    "where @('<type>') is a Java primitive type
     and @('<conv-type(...)>') is the conversion code
     generated by @(tsee atj-convert-expr-from-jprim)
     for that primitive type.")
   (xdoc::p
    "Note that we generate an expression name for @('array.length'),
     because grammatically this is not a field access expression in Java:
     it cannot be generated from the nonterminal @('field-acces');
     it can be generated from the nonterminal @('expression-name')."))
  (b* ((method-name (atj-convert-expr-from-jprimarr-method-name type))
       (jtype (atj-type-to-jitype (atj-type-jprim type)))
       (array "array")
       (index "index")
       (result "result")
       (array[index] (jexpr-array (jexpr-name array) (jexpr-name index)))
       (conv-array[index] (atj-convert-expr-from-jprim array[index] type))
       (method-body
        (append
         (jblock-locvar *aij-type-value*
                        result
                        (atj-gen-symbol nil))
         (jblock-locvar (jtype-int)
                        index
                        (jexpr-binary (jbinop-sub)
                                      (jexpr-name (str::cat array "." "length"))
                                      (jexpr-literal-1)))
         (jblock-while (jexpr-binary (jbinop-ge)
                                     (jexpr-name index)
                                     (jexpr-literal-0))
                       (append
                        (jblock-asg (jexpr-name result)
                                    (jexpr-smethod *aij-type-cons*
                                                   "make"
                                                   (list conv-array[index]
                                                         (jexpr-name result))))
                        (jblock-expr (jexpr-unary (junop-predec)
                                                  (jexpr-name index)))))
         (jblock-return (jexpr-name result)))))
    (make-jmethod :access (jaccess-private)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type *aij-type-value*)
                  :name method-name
                  :params (list (jparam nil (jtype-array jtype) array))
                  :throws nil
                  :body method-body))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-convert-expr-from-jprimarr ((expr jexprp) (type primitive-typep))
  :returns (new-expr jexprp)
  :short "Convert a Java expression from a Java primitive array type."
  (b* ((method-name (atj-convert-expr-from-jprimarr-method-name type)))
    (jexpr-method method-name (list expr)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-jprimarr-conversion-methods ()
  :returns (methods jmethod-listp)
  :short "Generate all the twelve methods to convert
          to and from Java primitive arrays."
  (list (atj-convert-expr-to-jprimarr-method (primitive-type-boolean))
        (atj-convert-expr-to-jprimarr-method (primitive-type-char))
        (atj-convert-expr-to-jprimarr-method (primitive-type-byte))
        (atj-convert-expr-to-jprimarr-method (primitive-type-short))
        (atj-convert-expr-to-jprimarr-method (primitive-type-int))
        (atj-convert-expr-to-jprimarr-method (primitive-type-long))
        (atj-convert-expr-from-jprimarr-method (primitive-type-boolean))
        (atj-convert-expr-from-jprimarr-method (primitive-type-char))
        (atj-convert-expr-from-jprimarr-method (primitive-type-byte))
        (atj-convert-expr-from-jprimarr-method (primitive-type-short))
        (atj-convert-expr-from-jprimarr-method (primitive-type-int))
        (atj-convert-expr-from-jprimarr-method (primitive-type-long))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-adapt-expr-to-type ((expr jexprp)
                                (src-type atj-typep)
                                (dst-type atj-typep))
  :returns (new-expr jexprp)
  :short "Adapt a Java expression from a source type to a destination type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when generating
     shallowly embedded ACL2 calls of named functions.
     As explained " (xdoc::seetopic "atj-types" "here") ",
     when, for instance, the type of an actual argument of a function call
     is not the same as or a subtype (according to Java subtyping) of
     the type of the formal argument,
     ATJ adds Java code to convert from the former type to the latter type.")
   (xdoc::p
    "This code generation function does that.
     The input Java expression is the one generated for the actual argument,
     whose type is @('src-type') (for `source type').
     The input @('dst-type') (for `destination type')
     is the type of the corresponding formal argument.")
   (xdoc::p
    "These type conversions are determined from
     the wrapping conversion functions added by the type annotation step.
     Those prohibit any conversion between @(':j...') and @(':acl2') types
     (see @(tsee atj-type-wrap-term) and @(tsee atj-type-conv-allowed-p)),
     save for a temporary exception needed to accommodate
     terms that construct Java primitive arrays
     (the exception is described in @(tsee atj-type-conv-allowed-p)).
     However, those conversions are changed prior to the translation to Java
     (see @(tsee atj-type-rewrap-array-initializer-elements)).
     So, by the time we call this function @('atj-adapt-expr-to-type'),
     the @('src-type') and @('dst-type') inputs should never be
     one a @(':j...') type and one a @(':acl2') type.
     If it is, it means that such a conversion was used somewhere else
     than in the array constructions that get rewrapped,
     and so here we cause a (deep input validation) failure
     if that's the case.
     For extra safety, we also cause an implementation error
     if we are trying to do any other disallowed conversion,
     but this should never happen.")
   (xdoc::p
    "To convert between the @(':acl2') types,
     if the source type is a subtype of or the same type as
     the destination type
     (which can be checked via @(tsee atj-type-<=),
     we leave the expression unchanged;
     otherwise, we insert a cast to the destination type,
     which is expected to always succeed
     under the assumption of guard verification."))
  (cond ((atj-type-equiv src-type dst-type) (jexpr-fix expr))
        ((and (atj-type-case src-type :jprim)
              (atj-type-equiv dst-type (atj-type-acl2 (atj-atype-value))))
         (prog2$ (raise "Type annotation failure: ~
                         attempting to convert from ~x0 to ~x1."
                        src-type dst-type)
                 (jexpr-fix expr)))
        ((and (atj-type-case src-type :acl2)
              (atj-type-case dst-type :acl2))
         (cond ((atj-type-<= src-type dst-type) (jexpr-fix expr))
               ((atj-type-< dst-type src-type)
                (jexpr-cast (atj-type-to-jitype dst-type) expr))
               (t (prog2$ (raise "Internal error: ~
                                  unexpected conversion from ~x0 to ~x1."
                                 src-type dst-type)
                          (jexpr-fix expr)))))
        (t (prog2$ (raise "Internal error: ~
                           unexpected conversion from ~x0 to ~x1."
                          src-type dst-type)
                   (jexpr-fix expr))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-adapt-exprs-to-types ((exprs jexpr-listp)
                                  (src-types atj-type-listp)
                                  (dst-types atj-type-listp))
  :guard (and (= (len exprs) (len src-types))
              (= (len exprs) (len dst-types)))
  :returns (new-exprs jexpr-listp)
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

(define atj-adapt-expr-to-types ((expr jexprp)
                                 (src-types atj-type-listp)
                                 (dst-types atj-type-listp)
                                 (jvar-tmp-base stringp)
                                 (jvar-tmp-index posp))
  :guard (and (consp src-types)
              (consp dst-types)
              (= (len src-types) (len dst-types)))
  :returns (mv (block jblockp)
               (new-expr jexprp)
               (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
  :short "Adapt a Java expression from source types to destination types."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the two lists are singletons, we use @(tsee atj-adapt-expr-to-type).
     Otherwise, we are converting a multi-valued expression
     to another multi-valued expression with the same number of components;
     here `multi-valued' is in the sense of ACL2's @(tsee mv).
     We project the components of the expressions by reading the fields,
     call @(tsee atj-adapt-expr-to-type) on each of them,
     and then build a new multi-valued expression
     with the resulting expressions as arguments.
     That is, we adapt the expression component-wise.")
   (xdoc::p
    "Unless the starting expression is an expression name,
     we use an intermediate variable to store the value of the expression
     before projecting the components;
     otherwise, we would be re-evaluating the starting expression
     multiple times.
     Thus, in general we return a block and an expression,
     and the index for the temporary variable is threaded though."))
  (b* (((when (= (len src-types) 1))
        (mv nil
            (atj-adapt-expr-to-type expr (car src-types) (car dst-types))
            jvar-tmp-index))
       (src-jtype (jtype-class (atj-gen-shallow-mv-class-name src-types)))
       (dst-jtype (jtype-class (atj-gen-shallow-mv-class-name src-types)))
       ((when (equal src-jtype dst-jtype))
        (mv nil (jexpr-fix expr) jvar-tmp-index))
       ((mv block
            expr
            jvar-tmp-index)
        (if (jexpr-case expr :name)
            (mv nil (jexpr-fix expr) jvar-tmp-index)
          (b* (((mv block var jvar-tmp-index)
                (atj-gen-jlocvar-indexed src-jtype
                                         jvar-tmp-base
                                         jvar-tmp-index
                                         expr)))
            (mv block (jexpr-name var) jvar-tmp-index))))
       (exprs (atj-adapt-expr-to-types-aux expr 0 (len src-types)))
       (exprs (atj-adapt-exprs-to-types exprs src-types dst-types)))
    (mv block
        (jexpr-smethod dst-jtype
                       *atj-mv-factory-method-name*
                       exprs)
        jvar-tmp-index))

  :prepwork
  ((define atj-adapt-expr-to-types-aux ((expr jexprp) (i natp) (n natp))
     :returns (exprs jexpr-listp)
     (if (or (not (mbt (natp i)))
             (not (mbt (natp n)))
             (>= i n))
         nil
       (cons (jexpr-get-field expr (atj-gen-shallow-mv-field-name i))
             (atj-adapt-expr-to-types-aux expr (1+ i) n)))
     :measure (nfix (- n i))
     ///
     (defret len-of-atj-adapt-expr-to-types-aux
       (equal (len exprs)
              (if (and (natp n) (natp i))
                  (nfix (- n i))
                0))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-check-type-annotated-list-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (elements pseudo-term-listp :hyp :guard))
  :short "Check if a term is a type-annotated (translated)
          call of @(tsee list)."
  :long
  (xdoc::topstring
   (xdoc::p
    "In translated form, a term @('(list x y z ...)') is
     @('(cons x (cons y (cons z ... \'nil)...)'),
     i.e. a nest of @(tsee cons)es that ends in a quoted @('nil').
     The nest may be empty, i.e. the term may be just a quoted @('nil').
     But here we are looking at terms with ATJ type annotations,
     so the term really appears as
     @('(<C> (cons x (<C> (cons y (<C> (cons z ... (<C> \'nil)...)'),
     where @('<C>') represents (possibly different) type conversion functions.
     If a term has this latter form,
     we return @('t') as first result
     and the list @('(x y z ...)') as second result;
     otherwise, we return @('nil') as both results.")
   (xdoc::p
    "This function is used to generate
     Java array creation expressions with initializers
     from terms @('(<T>-array (list ...))'),
     where @('<T>') is a Java primitive type.
     In this case, we want to retrieve the elements of the list
     and use the corresponding Java expressions for the array initializer."))
  (b* (((mv term & &) (atj-type-unwrap-term term))
       ((when (variablep term)) (mv nil nil))
       ((when (fquotep term)) (if (equal term *nil*)
                                  (mv t nil)
                                (mv nil nil)))
       (fn (ffn-symb term))
       ((unless (eq fn 'cons)) (mv nil nil))
       (args (fargs term))
       ((unless (= (len args) 2))
        (raise "Internal error: found CONS with ~x0 arguments." (len args))
        (mv nil nil))
       (car (first args))
       (cdr (second args))
       ((mv yes/no-rest elements-rest) (atj-check-type-annotated-list-call cdr))
       ((unless yes/no-rest) (mv nil nil)))
    (mv t (cons car elements-rest)))
  :prepwork ((local (in-theory (enable atj-type-unwrap-term))))
  ///

  (defret atj-check-type-annotated-list-call-decreases
    (implies yes/no
             (< (acl2-count elements)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-rewrap-array-initializer-elements
  ((terms pseudo-term-listp)
   (new-dst-type primitive-typep))
  :returns (new-terms pseudo-term-listp :hyp :guard)
  :short "Adjust the type conversion functions of the terms
          to use for a Java array creation expression with initializer."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function is used on
     the result of @(tsee atj-check-type-annotated-list-call);
     see that function's documentation first.
     Since the terms returned by that function were arguments of @(tsee cons),
     they are wrapped by type conversion functions
     whose destination type is @(':avalue'),
     i.e. the input type of @(tsee cons).
     However, when using the Java counterparts of these terms
     in an array initializer,
     we do not want to convert them to @('Acl2Value'):
     we want the destination type to be the one corresponding to
     the Java primitive type of the array,
     which we pass as argument to this function.")
   (xdoc::p
    "Thus, here we go through the terms,
     which must all be wrapped with a type conversion function,
     and we re-wrap them with a type conversion function
     with a modified destination type."))
  (b* (((when (or (primitive-type-case new-dst-type :float)
                  (primitive-type-case new-dst-type :double)))
        (raise "Type ~x0 nor supported." new-dst-type))
       ((when (endp terms)) nil)
       (term (car terms))
       ((mv term src-types dst-types) (atj-type-unwrap-term term))
       ((unless term) nil) ; to prove ACL2-COUNT theorem below
       ((unless (equal dst-types (list (atj-type-acl2 (atj-atype-value)))))
        (raise "Internal error: ~
                the term ~x0 is wrapped with a conversion function ~
                from types ~x1 to types ~x2."
               term src-types dst-types))
       (new-term (atj-type-wrap-term term
                                     src-types
                                     (list (atj-type-jprim new-dst-type))))
       (new-terms (atj-type-rewrap-array-initializer-elements (cdr terms)
                                                              new-dst-type)))
    (cons new-term new-terms))
  ///

  (defret atj-type-rewrap-array-initializer-elements-not-increases
    (<= (acl2-count new-terms)
        (acl2-count terms))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable atj-type-unwrap-term
                                       atj-type-wrap-term)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-check-marked-annotated-mv-let-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (mv-var symbolp)
               (mv-term pseudo-termp)
               (vars symbol-listp)
               (indices nat-listp)
               (body-term pseudo-termp))
  :short "Recognize translated @(tsee mv-let)s after pre-translation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type annotation pre-translation step recognizes @(tsee mv-let)s
     and transforms them as explained in @(tsee atj-type-annotate-term).
     the variable reuse pre-translation step additionally marks the variables,
     and the variable renaming pre-translation step
     may change their (unmarked, unannotated) names.
     So the resulting term should have the form")
   (xdoc::codeblock
    "([reqinf>reqinf]"
    " ((lambda ([m][types]mv)"
    "          ([reqinf>reqinf]"
    "           ((lambda ([m1][type1]var1 ... [mn][typen]varn)"
    "                    ([...>reqinf] body-term))"
    "            ([AV>type1] (mv-nth ([AI>AI] '0)"
    "                                ([types>types] [m][types]mv)))"
    "            ..."
    "            ([AV>typen] (mv-nth ([AI>AI] 'n-1)"
    "                                ([types>types] [m][types]mv))))))"
    "  ([types>types] mv-term)))")
   (xdoc::p
    "where @('[m]'), @('[m1]'), ..., @('[mn]') are new/old markings,
     and where @('mv') may not be the symbol `@('mv')' but some other symbol.
     Because of the pre-translation steps that removes unused variables,
     the formals and arguments of the inner lambda
     may be fewer than the elements of @('types');
     i.e. some @(tsee mv-nth) indices may be skipped.")
   (xdoc::p
    "This code recognizes terms of the form above,
     returning some of the constituents if successful.
     The @('mv-var') result is @('[m][types]mv'),
     i.e. the marked and annotated multi-value variable.
     The @('mv-term') result is @('([types>types] mv-term)'),
     i.e. the wrapped multi-value term.
     The @('vars') result is @('([m1][type1]var1 ... [mn][typen]varn)')
     (possibly skipping some indices),
     i.e. the list of formals of the inner lambda expression,
     all marked and annotated.
     The @('indices') result is the ordered list of @(tsee mv-nth) indices
     actually present; these are 0-based.
     The @('body-term') result is @('([...>reqinf] body-term)'),
     i.e. the wrapped body of the inner lambda expression.
     The term and variable results are marked/annotated/wrapped so that
     they can be treated uniformly by the code generation functions."))
  (b* (((mv outer-lambda-call reqinf reqinf2) (atj-type-unwrap-term term))
       ((unless (equal reqinf reqinf2)) (mv nil nil nil nil nil nil))
       ((mv okp mv-var wrapped-inner-lambda-call mv-term)
        (check-unary-lambda-call outer-lambda-call))
       ((unless okp) (mv nil nil nil nil nil nil))
       ((mv mv-var-unmarked &) (atj-unmark-var mv-var))
       ((mv & types) (atj-type-unannotate-var mv-var-unmarked))
       ((unless (> (len types) 1)) (mv nil nil nil nil nil nil))
       ((mv & src-types dst-types) (atj-type-unwrap-term mv-term))
       ((unless (and (equal src-types types)
                     (equal dst-types types)))
        (raise "Internal error: malformed term ~x0." term)
        (mv nil nil nil nil nil nil))
       ((mv inner-lambda-call src-types dst-types)
        (atj-type-unwrap-term wrapped-inner-lambda-call))
       ((unless (and (equal src-types reqinf)
                     (equal dst-types reqinf))) (mv nil nil nil nil nil nil))
       ((mv okp vars body-term args) (check-lambda-call inner-lambda-call))
       ((unless okp)
        (raise "Internal error: malformed term ~x0." term)
        (mv nil nil nil nil nil nil))
       ((mv & & dst-types) (atj-type-unwrap-term body-term))
       ((unless (equal dst-types reqinf))
        (raise "Internal error: malformed term ~x0." term)
        (mv nil nil nil nil nil nil))
       (indices (atj-check-marked-annotated-mv-let-call-aux
                 args vars types mv-var)))
    (mv t mv-var mv-term vars indices body-term))
  :guard-hints (("Goal"
                 :in-theory
                 (enable acl2::len-of-check-lambda-calls.formals-is-args)))

  :prepwork

  ((define atj-check-marked-annotated-mv-let-call-aux ((args pseudo-term-listp)
                                                       (vars symbol-listp)
                                                       (types atj-type-listp)
                                                       (mv-var symbolp))
     :guard (and (= (len vars) (len args))
                 (consp types))
     :returns (indices nat-listp)
     (b* (((when (endp args)) nil)
          ((mv arg arg-src arg-dst) (atj-type-unwrap-term (car args)))
          ((unless (and (not (variablep arg))
                        (not (fquotep arg))
                        (eq (ffn-symb arg) 'mv-nth)
                        (= (len (fargs arg)) 2)
                        (equal (fargn arg 2)
                               (atj-type-wrap-term mv-var types types))))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0))
          ((mv index index-src index-dst) (atj-type-unwrap-term (fargn arg 1)))
          ((unless (and (quotep index)
                        (equal index-src (list (atj-type-acl2
                                                (atj-atype-integer))))
                        (equal index-dst (list (atj-type-acl2
                                                (atj-atype-integer))))))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0))
          (index (unquote-term index))
          ((unless (integer-range-p 0 (len types) index))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0))
          ((unless (and (equal arg-src (list (atj-type-acl2 (atj-atype-value))))
                        (equal arg-dst (list (nth index types)))))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0))
          ((mv var &) (atj-unmark-var (car vars)))
          ((mv & var-types) (atj-type-unannotate-var var))
          ((unless (equal var-types (list (nth index types))))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0)))
       (cons index (atj-check-marked-annotated-mv-let-call-aux (cdr args)
                                                               (cdr vars)
                                                               types
                                                               mv-var)))

     :prepwork

     ((local (include-book "std/typed-lists/nat-listp" :dir :system))

      (defrulel verify-guards-lemma
        (implies (and (pseudo-termp term)
                      (not (variablep term))
                      (not (fquotep term)))
                 (pseudo-termp (fargn term 1)))
        :expand ((pseudo-termp term))))

     ///

     (defret len-of-atj-check-marked-annotated-mv-let-call-aux
       (equal (len indices) (len args)))))

  ///

  (defret len-of-atj-check-marked-annotated-mv-let.vars/indices
    (equal (len indices)
           (len vars))
    :hints (("Goal"
             :in-theory
             (enable acl2::len-of-check-lambda-calls.formals-is-args))))

  (in-theory (disable len-of-atj-check-marked-annotated-mv-let.vars/indices))

  (defret atj-check-marked-annotated-mv-let-mv-term-smaller
    (implies yes/no
             (< (acl2-count mv-term)
                (acl2-count term)))
    :rule-classes :linear
    :hints (("Goal"
             :use (acl2-count-of-atj-type-unwrap-term-linear
                   (:instance acl2::acl2-count-of-check-unary-lambda-call.arg
                    (term (mv-nth 0 (atj-type-unwrap-term term)))))
             :in-theory (disable
                         acl2-count-of-atj-type-unwrap-term-linear
                         acl2::acl2-count-of-check-unary-lambda-call.arg))))

  (defret atj-check-marked-annotated-mv-let-body-term-smaller
    (implies yes/no
             (< (acl2-count body-term)
                (acl2-count term)))
    :rule-classes :linear
    :hints (("Goal"
             :use (acl2-count-of-atj-type-unwrap-term-linear
                   (:instance acl2::acl2-count-of-check-unary-lambda-call.arg
                    (term (mv-nth 0 (atj-type-unwrap-term term))))
                   (:instance acl2-count-of-atj-type-unwrap-term-linear
                    (term (mv-nth 2 (check-unary-lambda-call
                                     (mv-nth 0 (atj-type-unwrap-term term))))))
                   (:instance acl2::acl2-count-of-check-lambda-call.body
                    (term
                     (mv-nth 0 (atj-type-unwrap-term
                                (mv-nth 2 (check-unary-lambda-call
                                           (mv-nth 0 (atj-type-unwrap-term
                                                      term)))))))))
             :in-theory (disable
                         acl2-count-of-atj-type-unwrap-term-linear
                         acl2::acl2-count-of-check-unary-lambda-call.arg
                         acl2::acl2-count-of-check-lambda-call.body)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprim-constr-of-qconst-to-expr ((fn atj-jprim-constr-p) arg)
  :returns (expr jexprp)
  :short "Map an ACL2 function that models a Java primitive constructor
          to the Java expression that constructs the primitive value,
          when the argument of the constructor is a quoted constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "The parameter @('arg') is the unquoted constant (i.e. the value)."))
  (case fn
    (boolean-value (if (booleanp arg)
                       (atj-gen-jboolean arg)
                     (prog2$
                      (raise "Internal error: BOOLEAN-VALUE applied to ~x0."
                             arg)
                      (ec-call (jexpr-fix :irrelevant)))))
    (char-value (if (ubyte16p arg)
                    (atj-gen-jchar arg)
                  (prog2$
                   (raise "Internal error: CHAR-VALUE applied to ~x0." arg)
                   (ec-call (jexpr-fix :irrelevant)))))
    (byte-value (if (sbyte8p arg)
                    (atj-gen-jbyte arg)
                  (prog2$
                   (raise "Internal error: BYTE-VALUE applied to ~x0." arg)
                   (ec-call (jexpr-fix :irrelevant)))))
    (short-value (if (sbyte16p arg)
                     (atj-gen-jshort arg)
                   (prog2$
                    (raise "Internal error: SHORT-VALUE applied to ~x0." arg)
                    (ec-call (jexpr-fix :irrelevant)))))
    (int-value (if (sbyte32p arg)
                   (atj-gen-jint arg)
                 (prog2$
                  (raise "Internal error: INT-VALUE applied to ~x0." arg)
                  (ec-call (jexpr-fix :irrelevant)))))
    (long-value (if (sbyte64p arg)
                    (atj-gen-jlong arg)
                  (prog2$
                   (raise "Internal error: LONG-VALUE applied to ~x0." arg)
                   (ec-call (jexpr-fix :irrelevant)))))
    (t (prog2$ (impossible)
               (ec-call (jexpr-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprim-constr-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprim-constr-to-ptype ((fn atj-jprim-constr-p))
  :returns (ptype primitive-typep)
  :short "Map an ACL2 function that models a Java primitive constructor
          to the corresponding Java primitive type."
  (case fn
    (boolean-value (primitive-type-boolean))
    (char-value (primitive-type-char))
    (byte-value (primitive-type-byte))
    (short-value (primitive-type-short))
    (int-value (primitive-type-int))
    (long-value (primitive-type-long))
    (t (prog2$ (impossible) (ec-call (primitive-type-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprim-constr-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprim-deconstr-to-ptype ((fn atj-jprim-deconstr-p))
  :returns (ptype primitive-typep)
  :short "Map an ACL2 function that models a Java primitive deconstructor
          to the corresponding Java primitive type."
  (case fn
    (boolean-value->bool$inline (primitive-type-boolean))
    (char-value->nat$inline (primitive-type-char))
    (byte-value->int$inline (primitive-type-byte))
    (short-value->int$inline (primitive-type-short))
    (int-value->int$inline (primitive-type-int))
    (long-value->int$inline (primitive-type-long))
    (t (prog2$ (impossible) (ec-call (primitive-type-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprim-deconstr-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprim-unop-fn-to-junop ((fn atj-jprim-unop-p))
  :returns (unop junopp)
  :short "Map an ACL2 function that models a Java primitive unary operation
          to the corresponding unary operator in the Java abstract syntax."
  (case fn
    (boolean-not (junop-logcompl))
    (int-plus (junop-uplus))
    (long-plus (junop-uplus))
    (int-minus (junop-uminus))
    (long-minus (junop-uminus))
    (int-not (junop-bitcompl))
    (long-not (junop-bitcompl))
    (float-plus (junop-uplus))
    (double-plus (junop-uplus))
    (float-minus (junop-uminus))
    (double-minus (junop-uminus))
    (t (prog2$ (impossible) (ec-call (junop-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprim-unop-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprim-binop-fn-to-jbinop ((fn atj-jprim-binop-p))
  :returns (binop jbinopp)
  :short "Map an ACL2 function that models a Java primitive binary operation
          to the corresponding binary operator in the Java abstract syntax."
  (case fn
    (boolean-and (jbinop-and))
    (boolean-xor (jbinop-xor))
    (boolean-ior (jbinop-ior))
    (boolean-eq (jbinop-eq))
    (boolean-neq (jbinop-ne))
    (int-add (jbinop-add))
    (long-add (jbinop-add))
    (int-sub (jbinop-sub))
    (long-sub (jbinop-sub))
    (int-mul (jbinop-mul))
    (long-mul (jbinop-mul))
    (int-div (jbinop-div))
    (long-div (jbinop-div))
    (int-rem (jbinop-rem))
    (long-rem (jbinop-rem))
    (int-and (jbinop-and))
    (long-and (jbinop-and))
    (int-xor (jbinop-xor))
    (long-xor (jbinop-xor))
    (int-ior (jbinop-ior))
    (long-ior (jbinop-ior))
    (int-eq (jbinop-eq))
    (long-eq (jbinop-eq))
    (int-neq (jbinop-ne))
    (long-neq (jbinop-ne))
    (int-less (jbinop-lt))
    (long-less (jbinop-lt))
    (int-lesseq (jbinop-le))
    (long-lesseq (jbinop-le))
    (int-great (jbinop-gt))
    (long-great (jbinop-gt))
    (int-greateq (jbinop-ge))
    (long-greateq (jbinop-ge))
    (int-int-shiftl (jbinop-shl))
    (long-long-shiftl (jbinop-shl))
    (long-int-shiftl (jbinop-shl))
    (int-long-shiftl (jbinop-shl))
    (int-int-shiftr (jbinop-sshr))
    (long-long-shiftr (jbinop-sshr))
    (long-int-shiftr (jbinop-sshr))
    (int-long-shiftr (jbinop-sshr))
    (int-int-ushiftr (jbinop-ushr))
    (long-long-ushiftr (jbinop-ushr))
    (long-int-ushiftr (jbinop-ushr))
    (int-long-ushiftr (jbinop-ushr))
    (float-add (jbinop-add))
    (double-add (jbinop-add))
    (float-sub (jbinop-sub))
    (double-sub (jbinop-sub))
    (float-mul (jbinop-mul))
    (double-mul (jbinop-mul))
    (float-div (jbinop-div))
    (double-div (jbinop-div))
    (float-rem (jbinop-rem))
    (double-rem (jbinop-rem))
    (float-eq (jbinop-eq))
    (double-eq (jbinop-eq))
    (float-neq (jbinop-ne))
    (double-neq (jbinop-ne))
    (float-less (jbinop-lt))
    (double-less (jbinop-lt))
    (float-lesseq (jbinop-le))
    (double-lesseq (jbinop-le))
    (float-great (jbinop-gt))
    (double-great (jbinop-gt))
    (float-greateq (jbinop-ge))
    (double-greateq (jbinop-ge))
    (t (prog2$ (impossible) (ec-call (jbinop-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprim-binop-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprim-conv-fn-to-jtype ((fn atj-jprim-conv-p))
  :returns (type jtypep)
  :short "Map an ACL2 function that models a Java primitive conversion
          to the result Java type of the conversion."
  (case fn
    (byte-to-short (jtype-short))
    (byte-to-int (jtype-int))
    (byte-to-long (jtype-long))
    (byte-to-float (jtype-float))
    (byte-to-double (jtype-double))
    (short-to-int (jtype-int))
    (short-to-long (jtype-long))
    (short-to-float (jtype-float))
    (short-to-double (jtype-double))
    (char-to-int (jtype-int))
    (char-to-long (jtype-long))
    (char-to-float (jtype-float))
    (char-to-double (jtype-double))
    (int-to-long (jtype-long))
    (int-to-float (jtype-float))
    (int-to-double (jtype-double))
    (long-to-float (jtype-float))
    (long-to-double (jtype-double))
    (float-to-double (jtype-double))
    (short-to-byte (jtype-byte))
    (short-to-char (jtype-char))
    (char-to-byte (jtype-byte))
    (char-to-short (jtype-short))
    (int-to-byte (jtype-byte))
    (int-to-short (jtype-short))
    (int-to-char (jtype-char))
    (long-to-byte (jtype-byte))
    (long-to-short (jtype-short))
    (long-to-char (jtype-char))
    (long-to-int (jtype-int))
    (float-to-byte (jtype-byte))
    (float-to-short (jtype-short))
    (float-to-char (jtype-char))
    (float-to-int (jtype-int))
    (float-to-long (jtype-long))
    (double-to-byte (jtype-byte))
    (double-to-short (jtype-short))
    (double-to-char (jtype-char))
    (double-to-int (jtype-int))
    (double-to-long (jtype-long))
    (double-to-float (jtype-float))
    (byte-to-char (jtype-char))
    (t (prog2$ (impossible) (ec-call (jtype-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprim-conv-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-constr-to-ptype ((fn atj-jprimarr-constr-p))
  :returns (ptype primitive-typep)
  :short "Map an ACL2 function that models a Java primitive array constructor
          to the corresponding Java primitive type."
  (case fn
    (boolean-array (primitive-type-boolean))
    (char-array (primitive-type-char))
    (byte-array (primitive-type-byte))
    (short-array (primitive-type-short))
    (int-array (primitive-type-int))
    (long-array (primitive-type-long))
    (t (prog2$ (impossible) (ec-call (primitive-type-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprimarr-constr-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-deconstr-to-ptype ((fn atj-jprimarr-deconstr-p))
  :returns (ptype primitive-typep)
  :short "Map an ACL2 function that models a Java primitive array deconstructor
          to the corresponding Java primitive type."
  (case fn
    (boolean-array->components$inline (primitive-type-boolean))
    (char-array->components$inline (primitive-type-char))
    (byte-array->components$inline (primitive-type-byte))
    (short-array->components$inline (primitive-type-short))
    (int-array->components$inline (primitive-type-int))
    (long-array->components$inline (primitive-type-long))
    (t (prog2$ (impossible) (ec-call (primitive-type-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprimarr-deconstr-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-lenconstr-to-comp-jtype ((fn atj-jprimarr-lenconstr-p))
  :returns (type jtypep)
  :short "Map an ACL2 function that models a Java primitive array constructor
          to the Java array component type."
  (case fn
    (boolean-array-of-length (jtype-boolean))
    (char-array-of-length (jtype-char))
    (byte-array-of-length (jtype-byte))
    (short-array-of-length (jtype-short))
    (int-array-of-length (jtype-int))
    (long-array-of-length (jtype-long))
    (float-array-of-length (jtype-float))
    (double-array-of-length (jtype-double))
    (otherwise (prog2$ (impossible) (ec-call (jtype-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprimarr-lenconstr-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-constr-to-comp-jtype ((fn atj-jprimarr-constr-p))
  :returns (type jtypep)
  :short "Map an ACL2 function that models
          a Java primitive array constructor with initializer
          to the Java array component type."
  (case fn
    (boolean-array (jtype-boolean))
    (char-array (jtype-char))
    (byte-array (jtype-byte))
    (short-array (jtype-short))
    (int-array (jtype-int))
    (long-array (jtype-long))
    (otherwise (prog2$ (impossible) (ec-call (jtype-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprimarr-constr-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-constr-to-comp-type ((fn atj-jprimarr-constr-p))
  :returns (type primitive-typep)
  :short "Map an ACL2 function that models
          a Java primitive array constructor with initializer
          to the corresponding primitive type."
  (case fn
    (boolean-array (primitive-type-boolean))
    (char-array (primitive-type-char))
    (byte-array (primitive-type-byte))
    (short-array (primitive-type-short))
    (int-array (primitive-type-int))
    (long-array (primitive-type-long))
    (otherwise (prog2$ (impossible)
                       (ec-call (primitive-type-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprimarr-constr-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-primarray-write-method ((type primitive-typep))
  :returns (method jmethodp)
  :short "Generate a Java method to write a primitive array component."
  :long
  (xdoc::topstring
   (xdoc::p
    "In our initial approach to generating Java code
     that destructively updates primitive arrays,
     we will turn calls of the ACL2 functions that model array writes
     into calls of one of eight methods, one for each primitive type,
     that destructively assign the array component and then return the array.
     This function generates these methods,
     which are private because only code in the main class
     (including its nested classes) needs to call them.")
   (xdoc::p
    "The generated method has this form:")
   (xdoc::codeblock
    "private static <type>[] <name>(<type>[] array,"
    "                               int index,"
    "                               <type> component) {"
    "    array[index] = component;"
    "    return array;"
    "}")
   (xdoc::p
    "where @('<type>') is the Java primitive type."))
  (b* ((method-name (atj-primarray-write-method-name type))
       (array-type (jtype-array (jtype-prim type)))
       (index-type (jtype-int))
       (component-type (jtype-prim type))
       (array "array")
       (index "index")
       (component "component")
       (array[index] (jexpr-array (jexpr-name array) (jexpr-name index)))
       (array[index]=component (jblock-asg array[index] (jexpr-name component)))
       (return-array (jblock-return (jexpr-name array)))
       (method-body (append array[index]=component return-array)))
    (make-jmethod :access (jaccess-private)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type array-type)
                  :name method-name
                  :params (list (jparam nil array-type array)
                                (jparam nil index-type index)
                                (jparam nil component-type component))
                  :throws nil
                  :body method-body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-primarray-write-methods ()
  :returns (methods jmethod-listp)
  :short "Generate all the eight methods to write primitive arrays."
  (list (atj-gen-shallow-primarray-write-method (primitive-type-boolean))
        (atj-gen-shallow-primarray-write-method (primitive-type-char))
        (atj-gen-shallow-primarray-write-method (primitive-type-byte))
        (atj-gen-shallow-primarray-write-method (primitive-type-short))
        (atj-gen-shallow-primarray-write-method (primitive-type-int))
        (atj-gen-shallow-primarray-write-method (primitive-type-long))
        (atj-gen-shallow-primarray-write-method (primitive-type-float))
        (atj-gen-shallow-primarray-write-method (primitive-type-double))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-write-to-method-name ((fn atj-jprimarr-write-p))
  :returns (method stringp)
  :short "Map an ACL2 function that models
          a Java primitive array write operation
          to the corresponding Java method name."
  (atj-primarray-write-method-name
   (case fn
     (boolean-array-write (primitive-type-boolean))
     (char-array-write (primitive-type-char))
     (byte-array-write (primitive-type-byte))
     (short-array-write (primitive-type-short))
     (int-array-write (primitive-type-int))
     (long-array-write (primitive-type-long))
     (float-array-write (primitive-type-float))
     (double-array-write (primitive-type-double))
     (t (prog2$ (impossible) ""))))
  :guard-hints (("Goal" :in-theory (enable atj-jprimarr-write-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-let-bindings ((vars symbol-listp)
                                      (blocks jblock-listp)
                                      (exprs jexpr-listp))
  :guard (and (int= (len blocks) (len vars))
              (int= (len exprs) (len vars)))
  :returns (block jblockp :hyp (jblock-listp blocks))
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
     Thus, each ACL2 variable name carries its own non-empty list of types,
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
       ((mv var types) (atj-type-unannotate-var var))
       (jvar (symbol-name var))
       (var-block (if new?
                      (jblock-locvar (atj-gen-shallow-jtype types) jvar expr)
                    (jblock-asg (jexpr-name jvar) expr)))
       (first-block (append (car blocks) var-block))
       (rest-block (atj-gen-shallow-let-bindings (cdr vars)
                                                 (cdr blocks)
                                                 (cdr exprs))))
    (append first-block rest-block)))

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
    "These code generation functions assume that the ACL2 terms
     have been type-annotated via @(tsee atj-type-annotate-term).
     They also assume that all the variables of the ACL2 terms have been marked
     via @(tsee atj-mark-var-new) and @(tsee atj-mark-var-old),
     and renamed via @(tsee atj-rename-term).
     If the @(':guards') input is @('nil'),
     then all the type annotations consist of
     the type @(':avalue') of all ACL2 values,
     i.e. it is as if there were no types.")
   (xdoc::p
    "Our code generation strategy involves
     generating temporary Java local variables
     to store results of arguments of ACL2's non-strict @(tsee if).
     The base name to use for these variables
     is an argument of these code generation functions;
     the index to make these variables unique
     is threaded through the code generation functions."))

  (define atj-gen-shallow-if-test ((test pseudo-termp)
                                   (jvar-tmp-base stringp)
                                   (jvar-tmp-index posp)
                                   (pkg-class-names string-string-alistp)
                                   (fn-method-names symbol-string-alistp)
                                   (curr-pkg stringp)
                                   (qpairs cons-pos-alistp)
                                   (guards$ booleanp)
                                   (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 @(tsee if) test."
    :long
    (xdoc::topstring
     (xdoc::p
      "See @(tsee atj-gen-shallow-if-call) for a general description
       of how ACL2 @(tsee if)s are translated to Java @('if')s.")
     (xdoc::p
      "Here we handle the test of the @(tsee if).
       If the test has the form @('(boolean-value->bool b)'),
       where @('b') is an ACL2 term that returns a @(tsee boolean-value)
       (i.e. a Java boolean value in our model),
       we translate @('b') to its Java equivalent,
       ``ignoring'' @(tsee boolean-value->bool).
       For instance, if @('b') is @('(java::int-less x y)'),
       the generated Java test is @('(jx < jy)'),
       where @('jx') and @('jy') are the Java equivalents of @('x') and @('y').
       More precisely, we are dealing with annotated terms,
       so we look for @(tsee if) tests of the form
       @('([AS>AS] (boolean-value->bool ([JZ>JZ] <jbool>)))'),
       where @('<jbool>') evidently returns
       (our ACL2 model of) a Java boolean value,
       given the @('[JZ>JZ]') (non-)conversion (see @(tsee atj-type-conv)),
       where the destination type @(':jboolean')
       is the one assigned to the input of @(tsee boolean-value->bool).
       When an @(tsee if) test is type-annotated,
       no specific type is required for the test
       (see @(tsee atj-type-annotate-term)),
       so since the output type @(':asymbol')
       is assigned to @(tsee boolean-value->bool),
       the @('[AS>AS]') (non-)conversion will always wrap the test.")
     (xdoc::p
      "So, if the @(tsee if) test has the form just explained,
       we translate just @('<jbool>') to Java.
       Otherwise, we translate the whole test term,
       and return an expression that compares it with
       (the Java representation of) @('nil')."))
    (b* ((jbool? ; non-NIL iff TEST has the form explained above
          (b* (((mv test src-types dst-types) (atj-type-unwrap-term test))
               ((unless (and (equal src-types (list (atj-type-acl2
                                                     (atj-atype-symbol))))
                             (equal dst-types (list (atj-type-acl2
                                                     (atj-atype-symbol))))))
                nil)
               ((unless (and (consp test)
                             (eq (ffn-symb test)
                                 'boolean-value->bool$inline)
                             (int= (len (fargs test)) 1))) ; always true
                nil)
               (test (fargn test 1))
               ((unless (and (consp test)
                             (eq (ffn-symb test)
                                 (atj-type-conv (list
                                                 (atj-type-jprim
                                                  (primitive-type-boolean)))
                                                (list
                                                 (atj-type-jprim
                                                  (primitive-type-boolean)))))
                             (int= (len (fargs test)) 1))) ; always true
                nil))
            test))
         ((mv block
              expr
              jvar-tmp-index)
          (atj-gen-shallow-term (or jbool? test)
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                guards$
                                wrld))
         (expr (if jbool?
                   expr
                 (jexpr-binary (jbinop-ne)
                               expr
                               (atj-gen-shallow-symbol
                                nil pkg-class-names curr-pkg)))))
      (mv block expr jvar-tmp-index))
    ;; 2nd component is greater than 1
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count test) 2))

  (define atj-gen-shallow-if-call ((test pseudo-termp)
                                   (then pseudo-termp)
                                   (else pseudo-termp)
                                   (types atj-type-listp)
                                   (jvar-tmp-base stringp)
                                   (jvar-tmp-index posp)
                                   (pkg-class-names string-string-alistp)
                                   (fn-method-names symbol-string-alistp)
                                   (curr-pkg stringp)
                                   (qpairs cons-pos-alistp)
                                   (guards$ booleanp)
                                   (wrld plist-worldp))
    :guard (and (consp types)
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 @(tsee if) call."
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
      "<type> <tmp>;"
      "if (<a-expr> != NIL) {"
      "    <b-blocks>"
      "    <tmp> = <b-expr>;"
      "} else {"
      "    <c-blocks>"
      "    <tmp> = <c-expr>;"
      "}")
     (xdoc::p
      "and the Java expression @('<tmp>'),
       where @('<tmp>') consists of
       the base name in the parameter @('jvar-tmp-base')
       followed by a numeric index.")
     (xdoc::p
      "In other words, we first compute the test
       and create a local variable to store the final result.
       Based on the test, we execute either branch (for non-strictness),
       storing the result into the variable.")
     (xdoc::p
      "The type @('<type>') of the result variable is
       derived from the ATJ type passed to this code generation function.
       See @(tsee atj-gen-shallow-fn-call) for details.")
     (xdoc::p
      "If the flag @(tsee *atj-gen-cond-exprs*) is set,
       and if both @('<b-block>') and @('<c-block>') are empty,
       we generate the Java block")
     (xdoc::codeblock
      "<a-block>")
     (xdoc::p
      "and the Java expression")
     (xdoc::codeblock
      "<a-expr> != NIL ? <b-expr> : <c-expr>")
     (xdoc::p
      "However, if the test of the @(tsee if) has the form
       @('([AS>AS] (boolean-value->bool ([JZ>JZ] a)))'),
       we generate just @('<a-expr>') as the test of the Java @('if'):
       see @(tsee atj-gen-shallow-if-test) for details."))
    (b* (((mv test-block
              test-expr
              jvar-tmp-index)
          (atj-gen-shallow-if-test test
                                   jvar-tmp-base
                                   jvar-tmp-index
                                   pkg-class-names
                                   fn-method-names
                                   curr-pkg
                                   qpairs
                                   guards$
                                   wrld))
         ((mv then-block
              then-expr
              jvar-tmp-index)
          (atj-gen-shallow-term then
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                guards$
                                wrld))
         ((mv else-block
              else-expr
              jvar-tmp-index)
          (atj-gen-shallow-term else
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                guards$
                                wrld))
         ((when (and *atj-gen-cond-exprs*
                     (null then-block)
                     (null else-block)))
          (b* ((block test-block)
               (expr (jexpr-cond test-expr
                                 then-expr
                                 else-expr)))
            (mv block
                expr
                jvar-tmp-index)))
         (jtype (atj-gen-shallow-jtype types))
         ((mv result-locvar-block
              jvar-tmp
              jvar-tmp-index)
          (atj-gen-jlocvar-indexed jtype
                                   jvar-tmp-base
                                   jvar-tmp-index
                                   nil))
         (if-block (jblock-ifelse
                    test-expr
                    (append then-block
                            (jblock-asg-name jvar-tmp then-expr))
                    (append else-block
                            (jblock-asg-name jvar-tmp else-expr))))
         (block (append test-block
                        result-locvar-block
                        if-block))
         (expr (jexpr-name jvar-tmp)))
      (mv block
          expr
          jvar-tmp-index))
    ;; 2nd component is greater than 1 and 2
    ;; so that the call of ATJ-GEN-SHALLOW-IF-TEST decreases
    ;; and each call of ATJ-GEN-SHALLOW-TERM decreases
    ;; even when the ACL2-COUNTs of the other two addends are 0:
    :measure (two-nats-measure (+ (acl2-count test)
                                  (acl2-count then)
                                  (acl2-count else))
                               3))

  (define atj-gen-shallow-or-call ((first pseudo-termp)
                                   (second pseudo-termp)
                                   (types atj-type-listp)
                                   (jvar-tmp-base stringp)
                                   (jvar-tmp-index posp)
                                   (pkg-class-names string-string-alistp)
                                   (fn-method-names symbol-string-alistp)
                                   (curr-pkg stringp)
                                   (qpairs cons-pos-alistp)
                                   (guards$ booleanp)
                                   (wrld plist-worldp))
    :guard (and (consp types)
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 @('or') call."
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
      "<type> <tmp> = <a-expr>;"
      "if (<tmp> == NIL) {"
      "    <b-blocks>"
      "    <tmp> = <b-expr>;"
      "}")
     (xdoc::p
      "and the Java expression @('<tmp>')."))
    (b* (((mv first-block
              first-expr
              jvar-tmp-index)
          (atj-gen-shallow-term first
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                guards$
                                wrld))
         ((mv second-block
              second-expr
              jvar-tmp-index)
          (atj-gen-shallow-term second
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                guards$
                                wrld))
         (jtype (atj-gen-shallow-jtype types))
         ((mv result-locvar-block jvar-tmp jvar-tmp-index)
          (atj-gen-jlocvar-indexed jtype
                                   jvar-tmp-base
                                   jvar-tmp-index
                                   first-expr))
         (if-block (jblock-if
                    (jexpr-binary (jbinop-eq)
                                  (jexpr-name jvar-tmp)
                                  (atj-gen-shallow-symbol
                                   nil pkg-class-names curr-pkg))
                    (append second-block
                            (jblock-asg-name jvar-tmp second-expr))))
         (block (append first-block
                        result-locvar-block
                        if-block))
         (expr (jexpr-name jvar-tmp)))
      (mv block
          expr
          jvar-tmp-index))
    ;; 2nd component is greater than 1
    ;; so that each call of ATJ-GEN-SHALLOW-TERM decreases
    ;; even when the ACL2-COUNT of the other addend is 0:
    :measure (two-nats-measure (+ (acl2-count first)
                                  (acl2-count second))
                               2))

  (define atj-gen-shallow-jprim-constr-call
    ((fn atj-jprim-constr-p)
     (arg pseudo-termp)
     (src-types atj-type-listp)
     (dst-types atj-type-listp)
     (jvar-tmp-base stringp)
     (jvar-tmp-index posp)
     (pkg-class-names string-string-alistp)
     (fn-method-names symbol-string-alistp)
     (curr-pkg stringp)
     (qpairs cons-pos-alistp)
     (wrld plist-worldp))
    :guard (and (consp src-types)
                (consp dst-types)
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded
            ACL2 call of a Java primitive constructor."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model the construction of Java primitive values
       (i.e. @(tsee byte-value) etc.)
       are treated specially.
       If the argument is a quoted constant,
       the function call is translated
       to the constant Java primitive expression
       whose value is the quoted constant.
       If the argument is not a quoted constant,
       first we translate it to a Java expression in the general way,
       and then we convert it to the appropriate Java primitive type.
       In all cases, we convert the resulting expression, as needed,
       to match the destination type.")
     (xdoc::p
      "Note that we are dealing with annotated terms,
       so the argument of the constructor must be unwrapped
       to be examined."))
    (b* (((mv uarg & &) (atj-type-unwrap-term arg))
         ((unless uarg) ; for termination proof
          (mv nil (jexpr-name "irrelevant") jvar-tmp-index))
         (src-type (atj-type-list-to-type src-types))
         (dst-type (atj-type-list-to-type dst-types)))
      (if (quotep uarg)
          (b* ((uarg (unquote-term uarg))
               (expr (atj-jprim-constr-of-qconst-to-expr fn uarg))
               (expr (atj-adapt-expr-to-type expr src-type dst-type)))
            (mv nil expr jvar-tmp-index))
        (b* (((mv arg-block
                  arg-expr
                  jvar-tmp-index)
              (atj-gen-shallow-term arg
                                    jvar-tmp-base
                                    jvar-tmp-index
                                    pkg-class-names
                                    fn-method-names
                                    curr-pkg
                                    qpairs
                                    t ; GUARDS$
                                    wrld))
             (expr (atj-convert-expr-to-jprim arg-expr
                                              (atj-jprim-constr-to-ptype fn))))
          (mv arg-block
              (atj-adapt-expr-to-type expr src-type dst-type)
              jvar-tmp-index))))
    ;; 2nd component is greater than 1
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count arg) 2))

  (define atj-gen-shallow-jprim-deconstr-call
    ((fn atj-jprim-deconstr-p)
     (arg pseudo-termp)
     (src-types atj-type-listp)
     (dst-types atj-type-listp)
     (jvar-tmp-base stringp)
     (jvar-tmp-index posp)
     (pkg-class-names string-string-alistp)
     (fn-method-names symbol-string-alistp)
     (curr-pkg stringp)
     (qpairs cons-pos-alistp)
     (wrld plist-worldp))
    :guard (and (consp src-types)
                (consp dst-types)
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded
            ACL2 call of a Java primitive deconstructor."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model the deconstruction of Java primitive values
       (i.e. @(tsee byte-value->int) etc.)
       are treated specially.
       First we translate the argument in the general way
       and then we convert that from the Java appropriate primitive type."))
    (b* (((mv arg-block
              arg-expr
              jvar-tmp-index)
          (atj-gen-shallow-term arg
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                t ; GUARDS$
                                wrld))
         (expr (atj-convert-expr-from-jprim arg-expr
                                            (atj-jprim-deconstr-to-ptype fn)))
         (src-type (atj-type-list-to-type src-types))
         (dst-type (atj-type-list-to-type dst-types)))
      (mv arg-block
          (atj-adapt-expr-to-type expr src-type dst-type)
          jvar-tmp-index))
    ;; 2nd component is greater than 1
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count arg) 2))

  (define atj-gen-shallow-jprim-unop-call
    ((fn atj-jprim-unop-p)
     (operand pseudo-termp)
     (src-types atj-type-listp)
     (dst-types atj-type-listp)
     (jvar-tmp-base stringp)
     (jvar-tmp-index posp)
     (pkg-class-names string-string-alistp)
     (fn-method-names symbol-string-alistp)
     (curr-pkg stringp)
     (qpairs cons-pos-alistp)
     (wrld plist-worldp))
    :guard (and (consp src-types)
                (consp dst-types)
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded
            ACL2 call of a Java primitive unary operation."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model Java primitive unary operations
       (i.e. @(tsee int-minus) etc.) are treated specially.
       We generate Java code to compute the operand,
       and generate a Java unary expression
       whose operator corresponds to the function."))
    (b* (((mv operand-block
              operand-expr
              jvar-tmp-index)
          (atj-gen-shallow-term operand
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                t ; GUARDS$
                                wrld))
         (unop (atj-jprim-unop-fn-to-junop fn))
         (expr (jexpr-unary unop operand-expr))
         (block operand-block))
      (mv block
          (atj-adapt-expr-to-type expr
                                  (atj-type-list-to-type src-types)
                                  (atj-type-list-to-type dst-types))
          jvar-tmp-index))
    ;; 2nd component is greater than 1
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count operand) 2))

  (define atj-gen-shallow-jprim-binop-call
    ((fn atj-jprim-binop-p)
     (left pseudo-termp)
     (right pseudo-termp)
     (src-types atj-type-listp)
     (dst-types atj-type-listp)
     (jvar-tmp-base stringp)
     (jvar-tmp-index posp)
     (pkg-class-names string-string-alistp)
     (fn-method-names symbol-string-alistp)
     (curr-pkg stringp)
     (qpairs cons-pos-alistp)
     (wrld plist-worldp))
    :guard (and (consp src-types)
                (consp dst-types)
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded
            ACL2 call of a Java primitive binary operation."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model Java primitive binary operations
       (i.e. @(tsee int-add) etc.) are treated specially.
       We generate Java code to compute the left and right operands,
       and generate a Java binary expression
       whose operator corresponds to the function."))
    (b* (((mv left-block
              left-expr
              jvar-tmp-index)
          (atj-gen-shallow-term left
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                t ; GUARDS$
                                wrld))
         ((mv right-block
              right-expr
              jvar-tmp-index)
          (atj-gen-shallow-term right
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                t ; GUARDS$
                                wrld))
         (binop (atj-jprim-binop-fn-to-jbinop fn))
         (expr (jexpr-binary binop left-expr right-expr))
         (block (append left-block right-block)))
      (mv block
          (atj-adapt-expr-to-type expr
                                  (atj-type-list-to-type src-types)
                                  (atj-type-list-to-type dst-types))
          jvar-tmp-index))
    ;; 2nd component is greater than 1
    ;; so that each call of ATJ-GEN-SHALLOW-TERM decreases
    ;; even when the ACL2-COUNT of the other addend is 0:
    :measure (two-nats-measure (+ (acl2-count left)
                                  (acl2-count right))
                               2))

  (define atj-gen-shallow-jprim-conv-call
    ((fn atj-jprim-conv-p)
     (operand pseudo-termp)
     (src-types atj-type-listp)
     (dst-types atj-type-listp)
     (jvar-tmp-base stringp)
     (jvar-tmp-index posp)
     (pkg-class-names string-string-alistp)
     (fn-method-names symbol-string-alistp)
     (curr-pkg stringp)
     (qpairs cons-pos-alistp)
     (wrld plist-worldp))
    :guard (and (consp src-types)
                (consp dst-types)
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded
            ACL2 call of a Java primitive conversion."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model Java primitive conversions
       (i.e. @(tsee int-to-char) etc.) are treated specially.
       We generate a cast to the target type:
       for widening conversions, this is unnecessary,
       but for now we use this simple scheme
       that may also emphasize clarity in the code;
       we may revisit this decision in the future."))
    (b* (((mv operand-block
              operand-expr
              jvar-tmp-index)
          (atj-gen-shallow-term operand
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                t ; GUARDS$
                                wrld))
         (jtype (atj-jprim-conv-fn-to-jtype fn))
         (expr (jexpr-cast jtype operand-expr))
         (block operand-block))
      (mv block
          (atj-adapt-expr-to-type expr
                                  (atj-type-list-to-type src-types)
                                  (atj-type-list-to-type dst-types))
          jvar-tmp-index))
    ;; 2nd component is greater than 1
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count operand) 2))

  (define atj-gen-shallow-jprimarr-constr-call
    ((fn atj-jprimarr-constr-p)
     (arg pseudo-termp)
     (src-types atj-type-listp)
     (dst-types atj-type-listp)
     (jvar-tmp-base stringp)
     (jvar-tmp-index posp)
     (pkg-class-names string-string-alistp)
     (fn-method-names symbol-string-alistp)
     (curr-pkg stringp)
     (qpairs cons-pos-alistp)
     (wrld plist-worldp))
    :guard (and (consp src-types)
                (consp dst-types)
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded
            ACL2 call of a Java primitive array constructor
            from a list of components."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model
       Java primitive array constructors from components
       (i.e. @(tsee byte-array) etc.) are treated specially.
       If the argument has the form @('(list ...)')
       (in translated form,
       i.e. it is a nest of @(tsee cons)es ending in a quoted @('nil'),
       as checked by the library function used here),
       we generate expressions for all the list elements,
       and then we generate a Java array creation expression
       with an initializer consisting of those generated expressions.
       If the argument has a different form,
       we first translate it to a Java expression in the general way;
       we then wrap the expression with code
       to convert it to the appropriate Java primitive array type.
       In all cases, we convert the resulting expression, as needed,
       to match the destination type.")
     (xdoc::p
      "Note that we are dealing with annotated terms,
       so the argument of the constructor must be unwrapped
       to be examined."))
    (b* (((mv list-call? elements) (atj-check-type-annotated-list-call arg)))
      (if list-call?
          (b* ((type (atj-jprimarr-constr-to-comp-type fn))
               (elements
                (atj-type-rewrap-array-initializer-elements elements type))
               ((mv blocks
                    exprs
                    jvar-tmp-index)
                (atj-gen-shallow-terms elements
                                       jvar-tmp-base
                                       jvar-tmp-index
                                       pkg-class-names
                                       fn-method-names
                                       curr-pkg
                                       qpairs
                                       t ; GUARDS$
                                       wrld))
               (block (flatten blocks))
               (jtype (atj-jprimarr-constr-to-comp-jtype fn))
               (expr (jexpr-newarray-init jtype exprs)))
            (mv block
                (atj-adapt-expr-to-type expr
                                        (atj-type-list-to-type src-types)
                                        (atj-type-list-to-type dst-types))
                jvar-tmp-index))
        (b* (((mv block
                  expr
                  jvar-tmp-index)
              (atj-gen-shallow-term arg
                                    jvar-tmp-base
                                    jvar-tmp-index
                                    pkg-class-names
                                    fn-method-names
                                    curr-pkg
                                    qpairs
                                    t ; GUARDS$
                                    wrld))
             (expr (atj-convert-expr-to-jprimarr
                    expr
                    (atj-jprimarr-constr-to-ptype fn))))
          (mv block
              (atj-adapt-expr-to-type expr
                                      (atj-type-list-to-type src-types)
                                      (atj-type-list-to-type dst-types))
              jvar-tmp-index))))
    ;; 2nd component is greater than 1
    ;; so that the second call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count arg) 2))

  (define atj-gen-shallow-jprimarr-deconstr-call
    ((fn atj-jprimarr-deconstr-p)
     (arg pseudo-termp)
     (src-types atj-type-listp)
     (dst-types atj-type-listp)
     (jvar-tmp-base stringp)
     (jvar-tmp-index posp)
     (pkg-class-names string-string-alistp)
     (fn-method-names symbol-string-alistp)
     (curr-pkg stringp)
     (qpairs cons-pos-alistp)
     (wrld plist-worldp))
    :guard (and (consp src-types)
                (consp dst-types)
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded
            ACL2 call of a Java primitive array deconstructor."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model
       Java primitive array deconstructors
       (i.e. @(tsee byte-array->components) etc.) are treated specially.
       First we translate the argument in the general way
       and then we convert that from the Java appropriate primitive type."))
    (b* (((mv arg-block
              arg-expr
              jvar-tmp-index)
          (atj-gen-shallow-term arg
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                t ; GUARDS$
                                wrld))
         (expr (atj-convert-expr-from-jprimarr
                arg-expr
                (atj-jprimarr-deconstr-to-ptype fn)))
         (src-type (atj-type-list-to-type src-types))
         (dst-type (atj-type-list-to-type dst-types)))
      (mv arg-block
          (atj-adapt-expr-to-type expr src-type dst-type)
          jvar-tmp-index))
    ;; 2nd component is greater than 1
    ;; so that the second call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count arg) 2))

  (define atj-gen-shallow-jprimarr-read-call
    ((array pseudo-termp)
     (index pseudo-termp)
     (src-types atj-type-listp)
     (dst-types atj-type-listp)
     (jvar-tmp-base stringp)
     (jvar-tmp-index posp)
     (pkg-class-names string-string-alistp)
     (fn-method-names symbol-string-alistp)
     (curr-pkg stringp)
     (qpairs cons-pos-alistp)
     (wrld plist-worldp))
    :guard (and (consp src-types)
                (consp dst-types)
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded
            ACL2 call of a Java primitive array read operation."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model Java primitive array read operations
       (i.e. @(tsee byte-array-read) etc.) are treated specially.
       We generate Java code to compute the array and index operands,
       and generate a Java array access expression."))
    (b* (((mv array-block
              array-expr
              jvar-tmp-index)
          (atj-gen-shallow-term array
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                t ; GUARDS$
                                wrld))
         ((mv index-block
              index-expr
              jvar-tmp-index)
          (atj-gen-shallow-term index
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                t ; GUARDS$
                                wrld))
         (block (append array-block index-block))
         (expr (jexpr-array array-expr index-expr)))
      (mv block
          (atj-adapt-expr-to-type expr
                                  (atj-type-list-to-type src-types)
                                  (atj-type-list-to-type dst-types))
          jvar-tmp-index))
    ;; 2nd component is greater than 1
    ;; so that each call of ATJ-GEN-SHALLOW-TERM decreases
    ;; even when the ACL2-COUNT of the other addend is 0:
    :measure (two-nats-measure (+ (acl2-count array)
                                  (acl2-count index))
                               2))

  (define atj-gen-shallow-jprimarr-length-call
    ((array pseudo-termp)
     (src-types atj-type-listp)
     (dst-types atj-type-listp)
     (jvar-tmp-base stringp)
     (jvar-tmp-index posp)
     (pkg-class-names string-string-alistp)
     (fn-method-names symbol-string-alistp)
     (curr-pkg stringp)
     (qpairs cons-pos-alistp)
     (wrld plist-worldp))
    :guard (and (consp src-types)
                (consp dst-types)
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded
            ACL2 call of a Java primitive array length operation."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model Java primitive array length operations
       (i.e. @(tsee byte-array-length) etc.) are treated specially.
       We generate Java code to compute the array operand,
       and generate a Java field access expression for the length.")
     (xdoc::p
      "Note that if the array expression is an expression name,
       we generate an expression name as the resulting expression,
       because grammatically this is not a field access expression in Java:
       it cannot be generated from the nonterminal @('field-acces');
       it can be generated from the nonterminal @('expression-name')."))
    (b* (((mv array-block
              array-expr
              jvar-tmp-index)
          (atj-gen-shallow-term array
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                t ; GUARDS$
                                wrld))
         (block array-block)
         (expr (if (jexpr-case array-expr :name)
                   (jexpr-name (str::cat (jexpr-name->get array-expr)
                                         ".length"))
                 (jexpr-field array-expr "length"))))
      (mv block
          (atj-adapt-expr-to-type expr
                                  (atj-type-list-to-type src-types)
                                  (atj-type-list-to-type dst-types))
          jvar-tmp-index))
    ;; 2nd component is greater than 1
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count array) 2))

  (define atj-gen-shallow-jprimarr-write-call
    ((fn atj-jprimarr-write-p)
     (array pseudo-termp)
     (index pseudo-termp)
     (component pseudo-termp)
     (src-types atj-type-listp)
     (dst-types atj-type-listp)
     (jvar-tmp-base stringp)
     (jvar-tmp-index posp)
     (pkg-class-names string-string-alistp)
     (fn-method-names symbol-string-alistp)
     (curr-pkg stringp)
     (qpairs cons-pos-alistp)
     (wrld plist-worldp))
    :guard (and (consp src-types)
                (consp dst-types)
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded
            ACL2 call of a Java primitive write operation."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model Java primitive array write operations
       (i.e. @(tsee byte-array-write) etc.) are treated specially.
       We generate Java code to compute the operands,
       and generate a call of the Java method to write arrays."))
    (b* (((mv array-block
              array-expr
              jvar-tmp-index)
          (atj-gen-shallow-term array
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                t ; GUARDS$
                                wrld))
         ((mv index-block
              index-expr
              jvar-tmp-index)
          (atj-gen-shallow-term index
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                t ; GUARDS$
                                wrld))
         ((mv component-block
              component-expr
              jvar-tmp-index)
          (atj-gen-shallow-term component
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                t ; GUARDS$
                                wrld))
         (block (append array-block
                        index-block
                        component-block))
         (expr (jexpr-method (atj-jprimarr-write-to-method-name fn)
                             (list array-expr index-expr component-expr))))
      (mv block
          (atj-adapt-expr-to-type expr
                                  (atj-type-list-to-type src-types)
                                  (atj-type-list-to-type dst-types))
          jvar-tmp-index))
    ;; 2nd component is greater than 1
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases
    ;; even when the ACL2-COUNT of the other addends is 0:
    :measure (two-nats-measure (+ (acl2-count array)
                                  (acl2-count index)
                                  (acl2-count component))
                               2))

  (define atj-gen-shallow-jprimarr-lenconstr-call
    ((fn atj-jprimarr-lenconstr-p)
     (length pseudo-termp)
     (src-types atj-type-listp)
     (dst-types atj-type-listp)
     (jvar-tmp-base stringp)
     (jvar-tmp-index posp)
     (pkg-class-names string-string-alistp)
     (fn-method-names symbol-string-alistp)
     (curr-pkg stringp)
     (qpairs cons-pos-alistp)
     (wrld plist-worldp))
    :guard (and (consp src-types)
                (consp dst-types)
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded
            ACL2 call of a Java primitive array constructor
            from a length."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model Java primitive array constructors from lengths
       (i.e. @(tsee byte-array-of-length) etc.) are treated specially.
       We generate Java code to compute the length operand,
       and generate a Java array creation expression without initializer."))
    (b* (((mv length-block
              length-expr
              jvar-tmp-index)
          (atj-gen-shallow-term length
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                t ; GUARDS$
                                wrld))
         (block length-block)
         (jtype (atj-jprimarr-lenconstr-to-comp-jtype fn))
         (expr (jexpr-newarray jtype length-expr)))
      (mv block
          (atj-adapt-expr-to-type expr
                                  (atj-type-list-to-type src-types)
                                  (atj-type-list-to-type dst-types))
          jvar-tmp-index))
    ;; 2nd component is greater than 1
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count length) 2))

  (define atj-gen-shallow-mv-call ((args pseudo-term-listp)
                                   (src-types atj-type-listp)
                                   (dst-types atj-type-listp)
                                   (jvar-tmp-base stringp)
                                   (jvar-tmp-index posp)
                                   (pkg-class-names string-string-alistp)
                                   (fn-method-names symbol-string-alistp)
                                   (curr-pkg stringp)
                                   (qpairs cons-pos-alistp)
                                   (guards$ booleanp)
                                   (wrld plist-worldp))
    :guard (and (consp src-types)
                (consp dst-types)
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 call of @(tsee mv)."
    :long
    (xdoc::topstring
     (xdoc::p
      "Calls of @(tsee mv) are introduced by a pre-translation step: see "
      (xdoc::seetopic "atj-pre-translation-multiple-values" "here")
      "for details.")
     (xdoc::p
      "These calls are treated specially for code generation.
       We generate a call of the factory method
       of the @(tsee mv) class corresponding to
       the destination types of the arguments,
       converting each argument from the source types as needed."))
    (b* (((mv blocks
              exprs
              jvar-tmp-index)
          (atj-gen-shallow-terms args
                                 jvar-tmp-base
                                 jvar-tmp-index
                                 pkg-class-names
                                 fn-method-names
                                 curr-pkg
                                 qpairs
                                 guards$
                                 wrld))
         (block (flatten blocks))
         ((unless (>= (len src-types) 2))
          (raise "Internal error: ~
                  MV has arguments ~x0, which are fewer than two."
                 args)
          (mv nil (jexpr-name "irrelevant") jvar-tmp-index))
         ((unless (= (len src-types) (len dst-types)))
          (raise "Internal error: ~
                  the source types ~x0 and destination types ~x1 ~
                  differ in number."
                 src-types dst-types)
          (mv nil (jexpr-name "irrelevant") jvar-tmp-index))
         ((unless (= (len args) (len dst-types)))
          (raise "Internal error: ~
                  the arguments ~x0 and ~
                  source and destination types ~x1 and ~x2 ~
                  differ in number."
                 args src-types dst-types)
          (mv nil (jexpr-name "irrelevant") jvar-tmp-index))
         (exprs (atj-adapt-exprs-to-types exprs src-types dst-types))
         (expr
          (jexpr-smethod (jtype-class (atj-gen-shallow-mv-class-name dst-types))
                         *atj-mv-factory-method-name*
                         exprs)))
      (mv block
          expr
          jvar-tmp-index))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-SHALLOW-TERMS decreases:
    :measure (two-nats-measure (acl2-count args) 1))

  (define atj-gen-shallow-fn-call ((fn pseudo-termfnp)
                                   (args pseudo-term-listp)
                                   (src-types atj-type-listp)
                                   (dst-types atj-type-listp)
                                   (jvar-tmp-base stringp)
                                   (jvar-tmp-index posp)
                                   (pkg-class-names string-string-alistp)
                                   (fn-method-names symbol-string-alistp)
                                   (curr-pkg stringp)
                                   (qpairs cons-pos-alistp)
                                   (guards$ booleanp)
                                   (wrld plist-worldp))
    :guard (and (consp src-types)
                (consp dst-types)
                (not (equal curr-pkg ""))
                (or (not (pseudo-lambdap fn))
                    (equal (len (lambda-formals fn))
                           (len args))))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 function call."
    :long
    (xdoc::topstring
     (xdoc::p
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
       calls of ACL2 functions that model
       Java primitive and primitive array constructors and operations
       are handled via separate functions.")
     (xdoc::p
      "In all other cases, in which the call is always strict,
       we first generate Java code to compute all the actual arguments.
       Calls of lambda expression are handled by a separate function.
       If the function is a named one,
       we generate a call of the method that corresponds to the ACL2 function,
       and we wrap that into a Java conversion if needed.
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
               (third (third args)))
            (if (equal first second)
                (atj-gen-shallow-or-call first
                                         third
                                         dst-types ; = SRC-TYPES
                                         jvar-tmp-base
                                         jvar-tmp-index
                                         pkg-class-names
                                         fn-method-names
                                         curr-pkg
                                         qpairs
                                         guards$
                                         wrld)
              (atj-gen-shallow-if-call first
                                       second
                                       third
                                       dst-types ; = SRC-TYPES
                                       jvar-tmp-base
                                       jvar-tmp-index
                                       pkg-class-names
                                       fn-method-names
                                       curr-pkg
                                       qpairs
                                       guards$
                                       wrld))))
         ((when (and guards$
                     (atj-jprim-constr-p fn)
                     (int= (len args) 1))) ; should be always true
          (atj-gen-shallow-jprim-constr-call fn
                                             (car args)
                                             src-types
                                             dst-types
                                             jvar-tmp-base
                                             jvar-tmp-index
                                             pkg-class-names
                                             fn-method-names
                                             curr-pkg
                                             qpairs
                                             wrld))
         ((when (and guards$
                     (atj-jprim-deconstr-p fn)
                     (int= (len args) 1))) ; should be always true
          (atj-gen-shallow-jprim-deconstr-call fn
                                               (car args)
                                               src-types
                                               dst-types
                                               jvar-tmp-base
                                               jvar-tmp-index
                                               pkg-class-names
                                               fn-method-names
                                               curr-pkg
                                               qpairs
                                               wrld))
         ((when (and guards$
                     (atj-jprim-unop-p fn)
                     (int= (len args) 1))) ; should be always true
          (atj-gen-shallow-jprim-unop-call fn
                                           (car args)
                                           src-types
                                           dst-types
                                           jvar-tmp-base
                                           jvar-tmp-index
                                           pkg-class-names
                                           fn-method-names
                                           curr-pkg
                                           qpairs
                                           wrld))
         ((when (and guards$
                     (atj-jprim-binop-p fn)
                     (int= (len args) 2))) ; should be always true
          (atj-gen-shallow-jprim-binop-call fn
                                            (first args)
                                            (second args)
                                            src-types
                                            dst-types
                                            jvar-tmp-base
                                            jvar-tmp-index
                                            pkg-class-names
                                            fn-method-names
                                            curr-pkg
                                            qpairs
                                            wrld))
         ((when (and guards$
                     (atj-jprim-conv-p fn)
                     (int= (len args) 1))) ; should be always true
          (atj-gen-shallow-jprim-conv-call fn
                                           (car args)
                                           src-types
                                           dst-types
                                           jvar-tmp-base
                                           jvar-tmp-index
                                           pkg-class-names
                                           fn-method-names
                                           curr-pkg
                                           qpairs
                                           wrld))
         ((when (and guards$
                     (atj-jprimarr-constr-p fn)
                     (int= (len args) 1))) ; should be always true
          (atj-gen-shallow-jprimarr-constr-call fn
                                                (car args)
                                                src-types
                                                dst-types
                                                jvar-tmp-base
                                                jvar-tmp-index
                                                pkg-class-names
                                                fn-method-names
                                                curr-pkg
                                                qpairs
                                                wrld))
         ((when (and guards$
                     (atj-jprimarr-deconstr-p fn)
                     (int= (len args) 1))) ; should be always true
          (atj-gen-shallow-jprimarr-deconstr-call fn
                                                  (car args)
                                                  src-types
                                                  dst-types
                                                  jvar-tmp-base
                                                  jvar-tmp-index
                                                  pkg-class-names
                                                  fn-method-names
                                                  curr-pkg
                                                  qpairs
                                                  wrld))
         ((when (and guards$
                     (atj-jprimarr-read-p fn)
                     (int= (len args) 2))) ; should be always true
          (atj-gen-shallow-jprimarr-read-call (first args)
                                              (second args)
                                              src-types
                                              dst-types
                                              jvar-tmp-base
                                              jvar-tmp-index
                                              pkg-class-names
                                              fn-method-names
                                              curr-pkg
                                              qpairs
                                              wrld))
         ((when (and guards$
                     (atj-jprimarr-length-p fn)
                     (int= (len args) 1))) ; should be always true
          (atj-gen-shallow-jprimarr-length-call (car args)
                                                src-types
                                                dst-types
                                                jvar-tmp-base
                                                jvar-tmp-index
                                                pkg-class-names
                                                fn-method-names
                                                curr-pkg
                                                qpairs
                                                wrld))
         ((when (and guards$
                     (atj-jprimarr-write-p fn)
                     (int= (len args) 3))) ; should be always true
          (atj-gen-shallow-jprimarr-write-call fn
                                               (first args)
                                               (second args)
                                               (third args)
                                               src-types
                                               dst-types
                                               jvar-tmp-base
                                               jvar-tmp-index
                                               pkg-class-names
                                               fn-method-names
                                               curr-pkg
                                               qpairs
                                               wrld))
         ((when (and guards$
                     (atj-jprimarr-lenconstr-p fn)
                     (int= (len args) 1))) ; should be always true
          (atj-gen-shallow-jprimarr-lenconstr-call fn
                                                   (car args)
                                                   src-types
                                                   dst-types
                                                   jvar-tmp-base
                                                   jvar-tmp-index
                                                   pkg-class-names
                                                   fn-method-names
                                                   curr-pkg
                                                   qpairs
                                                   wrld))
         ((when (eq fn 'mv))
          (atj-gen-shallow-mv-call args
                                   src-types
                                   dst-types
                                   jvar-tmp-base
                                   jvar-tmp-index
                                   pkg-class-names
                                   fn-method-names
                                   curr-pkg
                                   qpairs
                                   guards$
                                   wrld))
         ((mv arg-blocks
              arg-exprs
              jvar-tmp-index)
          (atj-gen-shallow-terms args
                                 jvar-tmp-base
                                 jvar-tmp-index
                                 pkg-class-names
                                 fn-method-names
                                 curr-pkg
                                 qpairs
                                 guards$
                                 wrld))
         ((when (symbolp fn))
          (b* ((expr (jexpr-method
                      (atj-gen-shallow-fnname fn
                                              pkg-class-names
                                              fn-method-names
                                              curr-pkg)
                      arg-exprs))
               ((unless (= (len src-types) (len dst-types)))
                (raise "Internal error: ~
                        the source types ~x0 and destination types ~x1 ~
                        differ in number."
                       src-types dst-types)
                (mv nil (jexpr-name "irrelevant") jvar-tmp-index))
               ((mv adapt-block
                    expr
                    jvar-tmp-index)
                (atj-adapt-expr-to-types expr src-types dst-types
                                         jvar-tmp-base jvar-tmp-index)))
            (mv (append (flatten arg-blocks) adapt-block)
                expr
                jvar-tmp-index)))
         ((mv lambda-block
              lambda-expr
              jvar-tmp-index)
          (atj-gen-shallow-lambda (lambda-formals fn)
                                  (lambda-body fn)
                                  arg-blocks
                                  arg-exprs
                                  src-types
                                  dst-types
                                  jvar-tmp-base
                                  jvar-tmp-index
                                  pkg-class-names
                                  fn-method-names
                                  curr-pkg
                                  qpairs
                                  guards$
                                  wrld)))
      (mv lambda-block
          lambda-expr
          jvar-tmp-index))
    ;; 2nd component is greater than 2
    ;; so that the call of ATJ-GEN-SHALLOW-LAMBDA decreases
    ;; even when FN is a non-symbol atom (impossible under the guard),
    ;; and it is non-0
    ;; so that the call of ATJ-GEN-SHALLOW-TERMS decreases
    ;; even when the ACL2-COUNT of FN is 0:
    :measure (two-nats-measure (+ (acl2-count fn)
                                  (acl2-count args))
                               3))

  (define atj-gen-shallow-lambda ((formals symbol-listp)
                                  (body pseudo-termp)
                                  (arg-blocks jblock-listp)
                                  (arg-exprs jexpr-listp)
                                  (src-types atj-type-listp)
                                  (dst-types atj-type-listp)
                                  (jvar-tmp-base stringp)
                                  (jvar-tmp-index posp)
                                  (pkg-class-names string-string-alistp)
                                  (fn-method-names symbol-string-alistp)
                                  (curr-pkg stringp)
                                  (qpairs cons-pos-alistp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :guard (and (consp src-types)
                (consp dst-types)
                (int= (len arg-blocks) (len formals))
                (int= (len arg-exprs) (len formals))
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp :hyp (jblock-listp arg-blocks))
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
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
              jvar-tmp-index)
          (atj-gen-shallow-term body
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                guards$
                                wrld))
         ((unless (= (len src-types) (len dst-types)))
          (raise "Internal error: ~
                  the source types ~x0 and destination types ~x1 ~
                  differ in number."
                 src-types dst-types)
          (mv nil (jexpr-name "irrelevant") jvar-tmp-index))
         ((mv adapt-block
              expr
              jvar-tmp-index)
          (atj-adapt-expr-to-types body-expr src-types dst-types
                                   jvar-tmp-base jvar-tmp-index)))
      (mv (append let-block body-block adapt-block)
          expr
          jvar-tmp-index))
    ;; 2nd component is greater than 1
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count body) 2))

  (define atj-gen-shallow-mv-let ((term pseudo-termp)
                                  (jvar-tmp-base stringp)
                                  (jvar-tmp-index posp)
                                  (pkg-class-names string-string-alistp)
                                  (fn-method-names symbol-string-alistp)
                                  (curr-pkg stringp)
                                  (qpairs cons-pos-alistp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (successp booleanp)
                 (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 @(tsee mv-let)."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is the first thing we try on every term
       (see @(tsee atj-gen-shallow-term)):
       if the term is an @(tsee mv-let),
       we translate it to Java here and return a success value as first result,
       so that the caller can propagate the results;
       otherwise, the first result is @('nil'),
       the other results are irrelevant,
       and the caller will handle the term
       knowing that it is not an @(tsee mv-let).")
     (xdoc::p
      "First, we check whether the term
       is a marked and annotated @(tsee mv-let);
       see @(tsee atj-check-marked-annotated-mv-let-call).
       If it is, we proceed as follows.
       We recursively translate to Java
       the term assigned to the @('mv') variable;
       this must have multiple types.
       Then we translate the @(tsee let) binding itself to Java,
       obtaining a local variable declaration or assignment
       (depending on the new/old marking of the @('mv') variable)
       for the multiple value.
       Then we translate the @(tsee let) bindings for the components,
       and finally the body term."))
    (b* (((mv yes/no mv-var mv-term vars indices body-term)
          (atj-check-marked-annotated-mv-let-call term))
         ((unless yes/no) (mv nil nil (jexpr-name "dummy") jvar-tmp-index))
         ((mv mv-block
              mv-expr
              jvar-tmp-index)
          (atj-gen-shallow-term mv-term
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                guards$
                                wrld))
         (mv-block (atj-gen-shallow-let-bindings (list mv-var)
                                                 (list mv-block)
                                                 (list mv-expr)))
         (mv-expr (b* (((mv mv-var &) (atj-unmark-var mv-var))
                       ((mv mv-var &) (atj-type-unannotate-var mv-var)))
                    (jexpr-name (symbol-name mv-var))))
         (exprs (atj-gen-shallow-mv-let-aux mv-expr indices))
         (vars-block (atj-gen-shallow-let-bindings vars
                                                   (repeat (len vars) nil)
                                                   exprs))
         ((mv body-block
              body-expr
              jvar-tmp-index)
          (atj-gen-shallow-term body-term
                                jvar-tmp-base
                                jvar-tmp-index
                                pkg-class-names
                                fn-method-names
                                curr-pkg
                                qpairs
                                guards$
                                wrld)))
      (mv t
          (append mv-block vars-block body-block)
          body-expr
          jvar-tmp-index))
    :measure (two-nats-measure (acl2-count term) 0)

    :prepwork
    ((define atj-gen-shallow-mv-let-aux ((expr jexprp) (indices nat-listp))
       :returns (exprs jexpr-listp)
       (cond ((endp indices) nil)
             (t (cons (jexpr-get-field expr
                                       (atj-gen-shallow-mv-field-name
                                        (car indices)))
                      (atj-gen-shallow-mv-let-aux expr (cdr indices)))))
       ///
       (defret len-of-atj-gen-shallow-mv-let-aux
         (equal (len exprs)
                (len indices))))))

  (define atj-gen-shallow-term ((term pseudo-termp)
                                (jvar-tmp-base stringp)
                                (jvar-tmp-index posp)
                                (pkg-class-names string-string-alistp)
                                (fn-method-names symbol-string-alistp)
                                (curr-pkg stringp)
                                (qpairs cons-pos-alistp)
                                (guards$ booleanp)
                                (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
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
      "First we try to process the term as an @(tsee mv-let).
       If this succeeds, we just return.
       Otherwise,
       we process the term by cases (variable, quoted constants, etc.),
       knowing that it is not an @(tsee mv-let).")
     (xdoc::p
      "If the ACL2 term is a quoted constant,
       we represent it as its value.
       We wrap the resulting expression with a Java conversion, if needed."))
    (b* (((mv mv-let-p
              block
              expr
              jvar-tmp-index)
          (atj-gen-shallow-mv-let term
                                  jvar-tmp-base
                                  jvar-tmp-index
                                  pkg-class-names
                                  fn-method-names
                                  curr-pkg
                                  qpairs
                                  guards$
                                  wrld))
         ((when mv-let-p) (mv block expr jvar-tmp-index))
         ((mv term src-types dst-types) (atj-type-unwrap-term term))
         ((unless term) ; for termination proof
          (mv nil (jexpr-name "dummy") jvar-tmp-index))
         ((when (variablep term))
          (b* (((mv var &) (atj-unmark-var term))
               ((mv var &) (atj-type-unannotate-var var))
               (expr (jexpr-name (symbol-name var)))
               (expr
                (atj-adapt-expr-to-type expr
                                        (atj-type-list-to-type src-types)
                                        (atj-type-list-to-type dst-types))))
            (mv nil expr jvar-tmp-index)))
         ((when (fquotep term))
          (b* ((value (unquote-term term))
               (expr (atj-gen-shallow-value value
                                            qpairs
                                            pkg-class-names
                                            curr-pkg))
               (expr
                (atj-adapt-expr-to-type expr
                                        (atj-type-list-to-type src-types)
                                        (atj-type-list-to-type dst-types))))
            (mv nil expr jvar-tmp-index))))
      (atj-gen-shallow-fn-call (ffn-symb term)
                               (fargs term)
                               src-types
                               dst-types
                               jvar-tmp-base
                               jvar-tmp-index
                               pkg-class-names
                               fn-method-names
                               curr-pkg
                               qpairs
                               guards$
                               wrld))
    ;; 2nd component is non-0 so that
    ;; the call of ATJ-GEN-SHALLOW-MV-LET decreases:
    :measure (two-nats-measure (acl2-count term) 1))

  (define atj-gen-shallow-terms ((terms pseudo-term-listp)
                                 (jvar-tmp-base stringp)
                                 (jvar-tmp-index posp)
                                 (pkg-class-names string-string-alistp)
                                 (fn-method-names symbol-string-alistp)
                                 (curr-pkg stringp)
                                 (qpairs cons-pos-alistp)
                                 (guards$ booleanp)
                                 (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (blocks (and (jblock-listp blocks)
                              (equal (len blocks) (len terms))))
                 (exprs (and (jexpr-listp exprs)
                             (equal (len exprs) (len terms))))
                 (new-jvar-tmp-index posp :hyp (posp jvar-tmp-index)))
    :parents (atj-shallow-code-generation atj-gen-shallow-term-fns)
    :short "Lift @(tsee atj-gen-shallow-term) to lists."
    (if (endp terms)
        (mv nil nil jvar-tmp-index)
      (b* (((mv first-block
                first-expr
                jvar-tmp-index)
            (atj-gen-shallow-term (car terms)
                                  jvar-tmp-base
                                  jvar-tmp-index
                                  pkg-class-names
                                  fn-method-names
                                  curr-pkg
                                  qpairs
                                  guards$
                                  wrld))
           ((mv rest-blocks
                rest-exprs
                jvar-tmp-index)
            (atj-gen-shallow-terms (cdr terms)
                                   jvar-tmp-base
                                   jvar-tmp-index
                                   pkg-class-names
                                   fn-method-names
                                   curr-pkg
                                   qpairs
                                   guards$
                                   wrld)))
        (mv (cons first-block rest-blocks)
            (cons first-expr rest-exprs)
            jvar-tmp-index)))
    :measure (two-nats-measure (acl2-count terms) 0))

  :prepwork ((local (in-theory (disable posp
                                        member-equal
                                        acl2::member-of-cons))))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-gen-shallow-term
    :hints
    (("Goal"
      :in-theory
      (enable atj-type-unwrap-term
              acl2::member-of-cons
              unquote-term
              pseudo-termfnp
              pseudo-lambdap
              len-of-atj-check-marked-annotated-mv-let.vars/indices)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fnnative-method ((fn symbolp)
                                         (fn-type atj-function-type-p)
                                         (method-name stringp)
                                         (method-param-names string-listp)
                                         (method-body jblockp))
  :guard (aij-nativep fn)
  :returns (method jmethodp)
  :short "Generate a Java method with the given types
          for an ACL2 function that is natively implemented in AIJ."
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
     @('Acl2NativeFunction') also has overloaded Java methods
     that take argument objects of narrower types
     that correspond to the primary and (if present) secondary ATJ types
     associated to the ACL2 function via the macros
     @(tsee atj-main-function-type) and
     @(tsee atj-other-function-type).")
   (xdoc::p
    "We generate a wrapper method for each such overloaded method:
     the argument and return types of the wrapper method
     are the same as the ones of the wrapped method in @('Acl2NativeFunction').
     This function generates one of these methods,
     as determined by the function type supplied as input.
     The types are the only thing that varies across the wrapper methods:
     their names, bodies, and other attributes are all the same;
     thus, these are calculated once and passed as inputs to this function.
     Note that the bodies of the wrapper methods automatically call
     different methods in @('Acl2NativeFunction') based on the types;
     the called methods are resolved by the Java compiler."))
  (b* ((in-types (atj-function-type->inputs fn-type))
       (out-types (atj-function-type->outputs fn-type))
       ((unless (consp out-types))
        (raise "Internal error: ~
                the function ~x0 has no output types ~x1."
               fn out-types)
        (ec-call (jmethod-fix :irrelevant)))
       (out-jtype (atj-gen-shallow-jtype out-types))
       ((unless (= (len in-types) (len method-param-names)))
        (raise "Internal error: ~
                the number ~x0 of input types for ~x1 ~
                differs from the number ~x2 of calculated method arguments."
               (len in-types) fn (len method-param-names))
        (ec-call (jmethod-fix :irrelevant))))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type out-jtype)
                  :name method-name
                  :params (atj-gen-paramlist
                           method-param-names
                           (atj-type-list-to-jitype-list in-types))
                  :throws (list *aij-class-undef-pkg-exc*)
                  :body method-body))
  :prepwork ((local (include-book "std/lists/len" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fnnative-methods ((fn symbolp)
                                          (fn-types atj-function-type-listp)
                                          (method-name stringp)
                                          (method-param-names string-listp)
                                          (method-body jblockp))
  :guard (aij-nativep fn)
  :returns (methods jmethod-listp)
  :short "Lift @(tsee atj-gen-shallow-fnnative-method)
          to lists of function types."
  (cond ((endp fn-types) nil)
        (t (cons (atj-gen-shallow-fnnative-method fn
                                                  (car fn-types)
                                                  method-name
                                                  method-param-names
                                                  method-body)
                 (atj-gen-shallow-fnnative-methods fn
                                                   (cdr fn-types)
                                                   method-name
                                                   method-param-names
                                                   method-body)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fnnative-all-methods
  ((fn symbolp)
   (pkg-class-names string-string-alistp)
   (fn-method-names symbol-string-alistp)
   (guards$ booleanp)
   (verbose$ booleanp)
   (wrld plist-worldp))
  :guard (aij-nativep fn)
  :returns (methods jmethod-listp)
  :short "Generate all the overloaded Java methods
          for an ACL2 function that is natively implemented in AIJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee atj-gen-shallow-fnnative-method) first.
     Here we calculate, once, the data to pass to that function
     (via @(tsee atj-gen-shallow-fnnative-methods)).")
   (xdoc::p
    "We retrieve all the primary and secondary function types of @('fn'),
     and generate an overloaded method for each.
     Note that if @('guards$') is @('nil'),
     then the retrieved function types boil down to one
     that consists of all @(':value') types."))
  (b* ((curr-pkg (symbol-package-name fn))
       (method-name (atj-gen-shallow-fnname fn
                                            pkg-class-names
                                            fn-method-names
                                            curr-pkg))
       ((run-when verbose$)
        (cw "  ~s0 for ~x1~%" method-name fn))
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
          (nonnegative-integer-quotient (list "i" "j"))
          (string-append (list "str1" "str2"))
          (t (list "x"))))
       (fn-info (atj-get-function-type-info fn guards$ wrld))
       (main-fn-type (atj-function-type-info->main fn-info))
       (other-fn-types (atj-function-type-info->others fn-info))
       (all-fn-types (cons main-fn-type other-fn-types))
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
          (nonnegative-integer-quotient "execNonnegativeIntegerQuotient")
          (string-append "execStringAppend")
          (len "execLen")
          (t (impossible))))
       (jcall-arg-exprs (jexpr-name-list method-param-names))
       (jcall (jexpr-smethod *aij-type-native-fn*
                             jcall-method-name
                             jcall-arg-exprs))
       (method-body (jblock-return jcall)))
    (atj-gen-shallow-fnnative-methods fn
                                      all-fn-types
                                      method-name
                                      method-param-names
                                      method-body))
  :guard-hints (("Goal" :in-theory (enable aij-nativep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fndef-method ((fn symbolp)
                                      (fn-type atj-function-type-p)
                                      (formals symbol-listp)
                                      (body pseudo-termp)
                                      (method-name stringp)
                                      (qconsts atj-qconstants-p)
                                      (pkg-class-names string-string-alistp)
                                      (fn-method-names symbol-string-alistp)
                                      (curr-pkg stringp)
                                      (mv-typess atj-type-list-listp)
                                      (guards$ booleanp)
                                      (wrld plist-worldp))
  :guard (and (not (aij-nativep fn))
              (not (equal curr-pkg ""))
              (cons-listp mv-typess))
  :returns (mv (method jmethodp)
               (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts))
               (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                   (cons-listp new-mv-typess))))
  :short "Generate a Java method with the given types
          for an ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 function definition is turned into a Java method.
     This is a public static method
     with the same number of parameters as the ACL2 function.
     More precisely, we generate an overloaded method
     for each primary and secondary function type associated to the function
     via @(tsee atj-main-function-type)
     and @(tsee atj-other-function-type).")
   (xdoc::p
    "This function generates one such method,
     based on the (primary or secondary) function type passed as input.
     First, we pre-translate the function.
     Then, we translate the pre-translated function to a Java method.
     Finally, we post-translate the Java method.")
   (xdoc::p
    "We also collect all the quoted constants
     in the pre-translated function body,
     and add it to the collection that it threaded through.")
   (xdoc::p
    "The formals and body of the function, as well as the method name,
     are the same for all the overloaded methods,
     so they are calculated once and passed to this function.
     However, the generation of the Java method
     (pre-translation, translation, and post-translation)
     must be done afresh for each overloaded methods,
     because it is affected by the function types,
     which are turned into the method's argument and result types:
     with different types,
     there may be different type annotations,
     and in particular different type conversions.
     In fact, it is expected that, with narrower types,
     there will be fewer type conversions.
     The pre-translation steps before the type annotation step
     could be actually factored out and done once,
     but for greater implementation simplicity here we repeat them
     for every overloaded method.")
   (xdoc::p
    "We collect all the @(tsee mv) types in the body
     for which we will need to generate @(tsee mv) classes."))
  (b* ((in-types (atj-function-type->inputs fn-type))
       (out-types (atj-function-type->outputs fn-type))
       (out-arrays (atj-function-type->arrays fn-type))
       ((unless (= (len in-types) (len formals)))
        (raise "Internal error: ~
                the number ~x0 of parameters of ~x1 ~
                does not match the number ~x2 of input types of ~x1."
               (len formals) fn (len in-types))
        (mv (ec-call (jmethod-fix :irrelevant)) qconsts nil))
       ((unless (consp out-types))
        (raise "Internal error: no output types ~x0 for ~x1." out-types fn)
        (mv (ec-call (jmethod-fix :irrelevant)) qconsts nil))
       ((mv formals body mv-typess)
        (atj-pre-translate fn formals body
                           in-types out-types out-arrays
                           mv-typess nil guards$ wrld))
       (qconsts (atj-add-qconstants-in-term body qconsts))
       ((mv formals &) (atj-unmark-vars formals))
       (formals (atj-type-unannotate-vars formals))
       (method-params (atj-gen-paramlist
                       (symbol-name-lst formals)
                       (atj-type-list-to-jitype-list in-types)))
       ((mv body-block body-expr &)
        (atj-gen-shallow-term body
                              "$tmp" 1
                              pkg-class-names
                              fn-method-names
                              curr-pkg
                              (atj-qconstants->pairs qconsts)
                              guards$
                              wrld))
       (method-body (append body-block
                            (jblock-return body-expr)))
       (tailrecp (and (logicp fn wrld)
                      (= 1 (len (irecursivep fn wrld)))
                      (tail-recursive-p fn wrld)))
       (method-body (atj-post-translate method-name
                                        method-params
                                        method-body
                                        tailrecp))
       ((unless (consp out-types))
        (raise "Internal error: ~
                the function ~x0 has no output types ~x1."
               fn out-types)
        (mv (ec-call (jmethod-fix :irrelevant)) qconsts nil))
       (out-jtype (atj-gen-shallow-jtype out-types))
       (method (make-jmethod :access (jaccess-public)
                             :abstract? nil
                             :static? t
                             :final? nil
                             :synchronized? nil
                             :native? nil
                             :strictfp? nil
                             :result (jresult-type out-jtype)
                             :name method-name
                             :params method-params
                             :throws (list *aij-class-undef-pkg-exc*)
                             :body method-body)))
    (mv method qconsts mv-typess))
  :prepwork ((local (include-book "std/lists/len" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fndef-methods ((fn symbolp)
                                       (fn-types atj-function-type-listp)
                                       (formals symbol-listp)
                                       (body pseudo-termp)
                                       (method-name stringp)
                                       (qconsts atj-qconstants-p)
                                       (pkg-class-names string-string-alistp)
                                       (fn-method-names symbol-string-alistp)
                                       (curr-pkg stringp)
                                       (mv-typess atj-type-list-listp)
                                       (guards$ booleanp)
                                       (wrld plist-worldp))
  :guard (and (not (aij-nativep fn))
              (not (equal curr-pkg ""))
              (cons-listp mv-typess))
  :returns (mv (methods jmethod-listp)
               (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts))
               (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                   (cons-listp new-mv-typess))
                              :hyp (and (atj-type-list-listp mv-typess)
                                        (cons-listp mv-typess))))
  :short "Lift @(tsee atj-gen-shallow-fndef-method) to lists of function types."
  (b* (((when (endp fn-types)) (mv nil qconsts mv-typess))
       ((mv first-methods
            qconsts
            mv-typess)
        (atj-gen-shallow-fndef-method fn
                                      (car fn-types)
                                      formals
                                      body
                                      method-name
                                      qconsts
                                      pkg-class-names
                                      fn-method-names
                                      curr-pkg
                                      mv-typess
                                      guards$
                                      wrld))
       ((mv rest-methods
            qconsts
            mv-typess)
        (atj-gen-shallow-fndef-methods fn
                                       (cdr fn-types)
                                       formals
                                       body
                                       method-name
                                       qconsts
                                       pkg-class-names
                                       fn-method-names
                                       curr-pkg
                                       mv-typess
                                       guards$
                                       wrld)))
    (mv (cons first-methods rest-methods) qconsts mv-typess)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fndef-all-methods
  ((fn symbolp)
   (qconsts atj-qconstants-p)
   (pkg-class-names string-string-alistp)
   (fn-method-names symbol-string-alistp)
   (mv-typess atj-type-list-listp)
   (guards$ booleanp)
   (verbose$ booleanp)
   (wrld plist-worldp))
  :guard (and (not (aij-nativep fn))
              (cons-listp mv-typess))
  :returns (mv (methods jmethod-listp)
               (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts))
               (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                   (cons-listp new-mv-typess))
                              :hyp (and (atj-type-list-listp mv-typess)
                                        (cons-listp mv-typess))))
  :short "Generate all the overloaded Java methods
          for an ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee atj-gen-shallow-fndef-method) first.
     Here we calculate, once, the data to pass to that function
     (via @(tsee atj-gen-shallow-fndef-methods)).")
   (xdoc::p
    "We retrieve all the primary and secondary function types of @('fn'),
     and generate an overloaded method for each.
     Note that if @('guards$') is @('nil'),
     then the retrieved function types boil down to one
     that consists of all @(':value') types."))
  (b* ((curr-pkg (symbol-package-name fn))
       (formals (formals+ fn wrld))
       (body (atj-fn-body fn wrld))
       ((run-when (null body))
        (raise "Internal error: ~
                the function ~x0 has no unnormalized body."
               fn))
       (fn-info (atj-get-function-type-info fn guards$ wrld))
       (main-fn-type (atj-function-type-info->main fn-info))
       (other-fn-types (atj-function-type-info->others fn-info))
       (all-fn-types (cons main-fn-type other-fn-types))
       (method-name (atj-gen-shallow-fnname fn
                                            pkg-class-names
                                            fn-method-names
                                            curr-pkg))
       ((run-when verbose$)
        (cw "  ~s0 for ~x1~%" method-name fn)))
    (atj-gen-shallow-fndef-methods fn
                                   all-fn-types
                                   formals
                                   body
                                   method-name
                                   qconsts
                                   pkg-class-names
                                   fn-method-names
                                   curr-pkg
                                   mv-typess
                                   guards$
                                   wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fn-methods ((fn symbolp)
                                    (qconsts atj-qconstants-p)
                                    (pkg-class-names string-string-alistp)
                                    (fn-method-names symbol-string-alistp)
                                    (mv-typess atj-type-list-listp)
                                    (guards$ booleanp)
                                    (verbose$ booleanp)
                                    (wrld plist-worldp))
  :guard (cons-listp mv-typess)
  :returns (mv (methods jmethod-listp)
               (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts))
               (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                   (cons-listp new-mv-typess))
                              :hyp (and (atj-type-list-listp mv-typess)
                                        (cons-listp mv-typess))))
  :short "Generate all the overloaded Java methods
          for an ACL2 function natively implemented in AIJ
          or for an ACL2 function definition."
  :long
  (xdoc::topstring-p
   "We also add all the quoted constants to the collection.
    The collection does not change for native functions.")
  (if (aij-nativep fn)
      (mv (atj-gen-shallow-fnnative-all-methods fn
                                                pkg-class-names
                                                fn-method-names
                                                guards$
                                                verbose$
                                                wrld)
          qconsts
          mv-typess)
    (atj-gen-shallow-fndef-all-methods fn
                                       qconsts
                                       pkg-class-names
                                       fn-method-names
                                       mv-typess
                                       guards$
                                       verbose$
                                       wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-all-fn-methods ((fns symbol-listp)
                                        (qconsts atj-qconstants-p)
                                        (pkg-class-names string-string-alistp)
                                        (fn-method-names symbol-string-alistp)
                                        (mv-typess atj-type-list-listp)
                                        (guards$ booleanp)
                                        (verbose$ booleanp)
                                        (wrld plist-worldp))
  :guard (cons-listp mv-typess)
  :returns (mv (methods jmethod-listp)
               (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts))
               (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                   (cons-listp new-mv-typess))
                              :hyp (and (atj-type-list-listp mv-typess)
                                        (cons-listp mv-typess))))
  :short "Lift @(tsee atj-gen-shallow-fn-methods) to lists of functions."
  (b* (((when (endp fns)) (mv nil qconsts mv-typess))
       ((mv first-methods
            qconsts
            mv-typess)
        (atj-gen-shallow-fn-methods (car fns)
                                    qconsts
                                    pkg-class-names
                                    fn-method-names
                                    mv-typess
                                    guards$
                                    verbose$
                                    wrld))
       ((mv rest-methods
            qconsts
            mv-typess)
        (atj-gen-shallow-all-fn-methods (cdr fns)
                                        qconsts
                                        pkg-class-names
                                        fn-method-names
                                        mv-typess
                                        guards$
                                        verbose$
                                        wrld)))
    (mv (append first-methods rest-methods) qconsts mv-typess)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-synonym-method-params ((n natp))
  :returns (formals string-listp)
  :short "Generate shallowly embedded formal parameters for
          the function synonyms generated by
          @(tsee atj-gen-shallow-synonym-method)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The exact formal parameters are not important,
     so for now we just generate @('x1'), @('x2'), ..., @('xn'),
     where @('n') is the arity.
     These are valid Java parameter names."))
  (atj-gen-shallow-synonym-method-params-aux n nil)

  :prepwork
  ((define atj-gen-shallow-synonym-method-params-aux ((n natp)
                                                      (acc string-listp))
     :returns (formals string-listp :hyp (string-listp acc))
     (cond ((zp n) acc)
           (t (atj-gen-shallow-synonym-method-params-aux
               (1- n) (cons (str::cat "x" (str::natstr n)) acc)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-synonym-method ((fn symbolp)
                                        (fn-type atj-function-type-p)
                                        (pkg-class-names string-string-alistp)
                                        (fn-method-names symbol-string-alistp)
                                        (wrld plist-worldp))
  :returns (method jmethodp)
  :short "Generate a Java method with the given types
          for an ACL2 function synonym."
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
     In particular, in the @('\"ACL2\"') package
     it can be referenced as just @('cons'),
     which makes ACL2 code much more readable.")
   (xdoc::p
    "In the shallow embedding,
     we translate these two ACL2 packages to two different Java classes,
     and the method that corresponds to @(tsee cons)
     is declared in the class for @('\"COMMON-LISP\"'),
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
     e.g. @(tsee cons) in the example above.")
   (xdoc::p
    "We pass the @(tsee symbol-package-name) of @('fn')
     to @(tsee atj-gen-shallow-fnname)
     to ensure that the result is the simple name of the method,
     which goes into the generated method declaration.")
   (xdoc::p
    "Recall that, for each ACL2 function,
     we generate as many overloaded Java methods
     as the number of primary and secondary types of the function.
     Accordingly, we must generate
     the same number of overloaded methods for the function synonyms.
     This function generates the overloaded method
     for the function type passed as argument."))
  (b* ((in-types (atj-function-type->inputs fn-type))
       (out-types (atj-function-type->outputs fn-type))
       ((unless (consp out-types))
        (raise "Internal error: ~
                the function ~x0 has no output types ~x1."
               fn out-types)
        (ec-call (jmethod-fix :irrelevant)))
       (out-jtype (atj-gen-shallow-jtype out-types))
       (fn-pkg (symbol-package-name fn))
       (method-name (atj-gen-shallow-fnname fn
                                            pkg-class-names
                                            fn-method-names
                                            fn-pkg))
       (method-param-names (atj-gen-shallow-synonym-method-params
                            (arity+ fn wrld)))
       ((unless (= (len method-param-names) (len in-types)))
        (raise "Internal error: ~
                the number ~x0 of input types of ~x1 ~
                differs from the arity ~x2 of ~x1."
               (len in-types) fn (len method-param-names))
        (ec-call (jmethod-fix :irrelevant)))
       (method-params (atj-gen-paramlist
                       method-param-names
                       (atj-type-list-to-jitype-list in-types)))
       (class (atj-get-pkg-class-name fn-pkg pkg-class-names))
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
                  :result (jresult-type out-jtype)
                  :name method-name
                  :params method-params
                  :throws (list *aij-class-undef-pkg-exc*)
                  :body method-body))
  :prepwork ((local (include-book "std/lists/len" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-synonym-methods ((fn symbolp)
                                         (fn-types atj-function-type-listp)
                                         (pkg-class-names string-string-alistp)
                                         (fn-method-names symbol-string-alistp)
                                         (wrld plist-worldp))
  :returns (methods jmethod-listp)
  :short "Lift @(tsee atj-gen-shallow-synonym-method)
          to lists of function types."
  (cond ((endp fn-types) nil)
        (t (cons (atj-gen-shallow-synonym-method fn
                                                 (car fn-types)
                                                 pkg-class-names
                                                 fn-method-names
                                                 wrld)
                 (atj-gen-shallow-synonym-methods fn
                                                  (cdr fn-types)
                                                  pkg-class-names
                                                  fn-method-names
                                                  wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-synonym-all-methods
  ((fn symbolp)
   (pkg-class-names string-string-alistp)
   (fn-method-names symbol-string-alistp)
   (guards$ booleanp)
   (wrld plist-worldp))
  :returns (methods jmethod-listp)
  :short "Generate all the overloaded Java methods
          for an ACL2 function synonym."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee atj-gen-shallow-synonym-method) first.")
   (xdoc::p
    "We retrieve all the primary and secondary function types of @('fn'),
     and generate an overloaded method for each.
     Note that if @('guards$') is @('nil'),
     then the retrieved function types boil down to one
     that consists of all @(':value') types."))
  (b* ((fn-info (atj-get-function-type-info fn guards$ wrld))
       (main-fn-type (atj-function-type-info->main fn-info))
       (other-fn-types (atj-function-type-info->others fn-info))
       (all-fn-types (cons main-fn-type other-fn-types)))
    (atj-gen-shallow-synonym-methods fn
                                     all-fn-types
                                     pkg-class-names
                                     fn-method-names
                                     wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-all-synonym-methods
  ((fns symbol-listp)
   (pkg-class-names string-string-alistp)
   (fn-method-names symbol-string-alistp)
   (guards$ booleanp)
   (wrld plist-worldp))
  :returns (methods jmethod-listp)
  :short "Lift @(tsee atj-gen-shallow-synonym-all-methods)
          to lists of functions."
  (cond ((endp fns) nil)
        (t (append (atj-gen-shallow-synonym-all-methods (car fns)
                                                        pkg-class-names
                                                        fn-method-names
                                                        guards$
                                                        wrld)
                   (atj-gen-shallow-all-synonym-methods (cdr fns)
                                                        pkg-class-names
                                                        fn-method-names
                                                        guards$
                                                        wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-pkg-methods ((pkg stringp)
                                     (fns-by-pkg string-symbollist-alistp)
                                     (fns+natives symbol-listp)
                                     (qconsts atj-qconstants-p)
                                     (pkg-class-names string-string-alistp)
                                     (fn-method-names symbol-string-alistp)
                                     (mv-typess atj-type-list-listp)
                                     (guards$ booleanp)
                                     (verbose$ booleanp)
                                     (wrld plist-worldp))
  :guard (cons-listp mv-typess)
  :returns (mv (methods jmethod-listp)
               (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts))
               (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                   (cons-listp new-mv-typess))
                              :hyp (and (atj-type-list-listp mv-typess)
                                        (cons-listp mv-typess))))
  :short "Generate all the methods of the class for an ACL2 package."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate methods for the functions in @('fns-by-pkg')
     (i.e. the functions to translate to Java, including natives,
     organized by package)
     that are associated to @('pkg').")
   (xdoc::p
    "We also generate synonym methods for all the functions in @('fns+native')
     (i.e. the functions to translate to Java, including natives)
     that are in other ACL2 packages but that are imported by @('pkg');
     see @(tsee atj-gen-shallow-synonym-method) for motivation.")
   (xdoc::p
    "Recall that, for each ACL2 function or function synonym,
     we generate one overloaded method
     for each primary or secondary type of the function.")
   (xdoc::p
    "We sort all the methods.")
   (xdoc::p
    "We also collect all the quoted constants
     that occur in the functions in @('pkg') that are translated to Java."))
  (b* ((fns (cdr (assoc-equal pkg fns-by-pkg)))
       ((run-when (and verbose$
                       (consp fns)))
        (cw "~%Generate the Java methods ~
               for the ACL2 functions in package ~s0:~%" pkg))
       ((mv fn-methods
            qconsts
            mv-typess)
        (atj-gen-shallow-all-fn-methods fns
                                        qconsts
                                        pkg-class-names
                                        fn-method-names
                                        mv-typess
                                        guards$
                                        verbose$
                                        wrld))
       (imported-fns (intersection-eq fns+natives (pkg-imports pkg)))
       (imported-fns (sort-symbol-listp imported-fns))
       (synonym-methods (atj-gen-shallow-all-synonym-methods imported-fns
                                                             pkg-class-names
                                                             fn-method-names
                                                             guards$
                                                             wrld))
       (all-methods (append synonym-methods fn-methods)))
    (mv (mergesort-jmethods all-methods)
        qconsts
        mv-typess))
  :prepwork
  ((local (include-book "std/typed-lists/symbol-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist string-jmethodlist-alistp (x)
  :short "Alists from package names (strings) to true lists of Java methods."
  :key (stringp x)
  :val (jmethod-listp x)
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-all-pkg-methods ((pkgs string-listp)
                                         (fns-by-pkg string-symbollist-alistp)
                                         (fns+natives symbol-listp)
                                         (qconsts atj-qconstants-p)
                                         (pkg-class-names string-string-alistp)
                                         (fn-method-names symbol-string-alistp)
                                         (mv-typess atj-type-list-listp)
                                         (guards$ booleanp)
                                         (verbose$ booleanp)
                                         (wrld plist-worldp))
  :guard (cons-listp mv-typess)
  :returns (mv (methods-by-pkg string-jmethodlist-alistp
                               :hyp (string-listp pkgs))
               (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts))
               (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                   (cons-listp new-mv-typess))
                              :hyp (and (atj-type-list-listp mv-typess)
                                        (cons-listp mv-typess))))
  :verify-guards :after-returns
  :short "Generate all the methods of the classes for all the ACL2 packages."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through all the packages in @('pkgs')
     and construct an alist from the packages there
     to the corresponding method lists
     (i.e. the methods of the class that corresponds to the package).
     If there are no methods for a package,
     we do not add an entry for the package in the alist."))
  (b* (((when (endp pkgs)) (mv nil qconsts mv-typess))
       (pkg (car pkgs))
       ((mv first-methods
            qconsts
            mv-typess)
        (atj-gen-shallow-pkg-methods pkg
                                     fns-by-pkg
                                     fns+natives
                                     qconsts
                                     pkg-class-names
                                     fn-method-names
                                     mv-typess
                                     guards$
                                     verbose$
                                     wrld))
       ((mv rest-methods
            qconsts
            mv-typess)
        (atj-gen-shallow-all-pkg-methods (cdr pkgs)
                                         fns-by-pkg
                                         fns+natives
                                         qconsts
                                         pkg-class-names
                                         fn-method-names
                                         mv-typess
                                         guards$
                                         verbose$
                                         wrld)))
    (if (null first-methods)
        (mv rest-methods qconsts mv-typess)
      (mv (acons pkg first-methods rest-methods)
          qconsts
          mv-typess))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-pkg-fields ((pkg stringp)
                                    (quoted-symbols symbol-listp)
                                    (quoted-symbols-by-pkg
                                     string-symbollist-alistp))
  :returns (fields jfield-listp)
  :short "Generate all the fields of the class for an ACL2 package."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate fields for the symbols in @('quoted-symbols-by-pkg')
     (i.e. the quoted symbols that appear in the bodies of the ACL2 functions
     that are translated to Java,
     organized by package)
     that are associated to @('pkg').
     These are all symbols whose package name is @('pkg').")
   (xdoc::p
    "We also generate fields for the symbols in @('quoted-symbols')
     (i.e. all the symbols in @('quoted-symbols-by-pkg'), in a flat list)
     that are imported by @('pkg').
     This enables the unqualified reference to them in the lass for @('pkg');
     see @(tsee atj-gen-shallow-symbol).")
   (xdoc::p
    "We sort all the fields, so that they appear in that order."))
  (b* ((syms (cdr (assoc-equal pkg quoted-symbols-by-pkg)))
       (imported-syms (intersection-eq quoted-symbols (pkg-imports pkg)))
       (all-syms (append syms imported-syms))
       (all-fields (atj-gen-shallow-symbol-fields all-syms)))
    (mergesort-jfields all-fields)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist string-jfieldlist-alistp (x)
  :short "Alists from package names (strings) to true lists of Java fields."
  :key (stringp x)
  :val (jfield-listp x)
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-all-pkg-fields ((pkgs string-listp)
                                        (quoted-symbols symbol-listp)
                                        (quoted-symbols-by-pkg
                                         string-symbollist-alistp))
  :returns (fields-by-pkg string-jfieldlist-alistp :hyp (string-listp pkgs))
  :verify-guards :after-returns
  :short "Generate all the fields of the class for all the ACL2 packages."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through all the packages in @('pkgs')
     and construct an alist from the packages there
     to the corresponding fields lists
     (i.e. the fields of the class that corresponds to the package).
     If there are no fields for a package,
     we do not add an entry for the package in the alist."))
  (b* (((when (endp pkgs)) nil)
       (pkg (car pkgs))
       (first-fields (atj-gen-shallow-pkg-fields pkg
                                                 quoted-symbols
                                                 quoted-symbols-by-pkg))
       (rest-fields (atj-gen-shallow-all-pkg-fields (cdr pkgs)
                                                    quoted-symbols
                                                    quoted-symbols-by-pkg)))
    (if (null first-fields)
        rest-fields
      (acons pkg first-fields rest-fields))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-pkg-class ((pkg stringp)
                                   (fields-by-pkg string-jfieldlist-alistp)
                                   (methods-by-pkg string-jmethodlist-alistp)
                                   (pkg-class-names string-string-alistp)
                                   (verbose$ booleanp))
  :returns (class jclassp)
  :short "Generate the class for an ACL2 package."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     we generate a Java class for each ACL2 package.
     This is a public static Java class,
     nested into the main Java class that ATJ generates.")
   (xdoc::p
    "The fields are in the @('fields-by-pkg') alist,
     which is calculated (elsewhere)
     via @(tsee atj-gen-shallow-all-pkg-fields).")
   (xdoc::p
    "The methods are in the @('methods-by-pkg') alist,
     which is calculated (elsewhere)
     via @(tsee atj-gen-shallow-all-pkg-methods)."))
  (b* ((class-name (atj-get-pkg-class-name pkg pkg-class-names))
       ((run-when verbose$)
        (cw "  ~s0 for ~s1~%" class-name pkg))
       (fields (cdr (assoc-equal pkg fields-by-pkg)))
       (methods (cdr (assoc-equal pkg methods-by-pkg))))
    (make-jclass :access (jaccess-public)
                 :abstract? nil
                 :static? t
                 :final? nil
                 :strictfp? nil
                 :name class-name
                 :superclass? nil
                 :superinterfaces nil
                 :body (append (jfields-to-jcbody-elements fields)
                               (jmethods-to-jcbody-elements methods)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-pkg-classes ((pkgs string-listp)
                                     (fields-by-pkg string-jfieldlist-alistp)
                                     (methods-by-pkg string-jmethodlist-alistp)
                                     (pkg-class-names string-string-alistp)
                                     (verbose$ booleanp))
  :returns (classes jclass-listp)
  :short "Lift @(tsee atj-gen-shallow-pkg-class) to lists."
  :long
  (xdoc::topstring-p
   "If the class for a package has an empty body, we skip it.")
  (b* (((when (endp pkgs)) nil)
       (class (atj-gen-shallow-pkg-class (car pkgs)
                                         fields-by-pkg
                                         methods-by-pkg
                                         pkg-class-names
                                         verbose$))
       (classes (atj-gen-shallow-pkg-classes (cdr pkgs)
                                             fields-by-pkg
                                             methods-by-pkg
                                             pkg-class-names
                                             verbose$)))
    (if (null (jclass->body class))
        classes
      (cons class classes))))

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
     we build the Java representation of the ACL2 packages."))
  (make-jcinitializer :static? t
                      :code (atj-gen-pkgs pkgs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-mv-fields ((types atj-type-listp))
  :returns (fields jfield-listp)
  :short "Generate the fields of the @(tsee mv) class for the given types."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-gen-shallow-mv-class-name),
     we generate Java classes that represent @(tsee mv) values.
     Each of these classes has a public instance field
     for each component type.
     The field is not private so that it can be quickly accessed
     when we translate calls of @(tsee mv-nth) to Java;
     this translation is not supported yet,
     but we are in the process of building
     more direct support for @(tsee mv) values
     in the Java code generated by ATJ.
     The field is public
     for the reason explained in @(tsee atj-gen-shallow-mv-class)."))
  (atj-gen-shallow-mv-fields-aux types 0)

  :prepwork
  ((define atj-gen-shallow-mv-fields-aux ((types atj-type-listp) (index natp))
     :returns (fields jfield-listp)
     (b* (((when (endp types)) nil)
          (field (make-jfield :access (jaccess-public)
                              :static? nil
                              :final? nil
                              :transient? nil
                              :volatile? nil
                              :type (atj-type-to-jitype (car types))
                              :name (atj-gen-shallow-mv-field-name index)
                              :init? nil))
          (fields (atj-gen-shallow-mv-fields-aux (cdr types) (1+ index))))
       (cons field fields)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-mv-params ((types atj-type-listp))
  :returns (params jparam-listp)
  :short "Generate the parameters of the factory method
          of the @(tsee mv) class for the given types."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-gen-shallow-mv-class-name),
     we generate Java classes that represent @(tsee mv) values.
     Each such class has a static factory method
     that re-uses a singleton instance of the class.
     The names of this method's parameter are the same as
     the corresponding fields."))
  (atj-gen-shallow-mv-params-aux types 0)

  :prepwork
  ((define atj-gen-shallow-mv-params-aux ((types atj-type-listp) (index natp))
     :returns (params jparam-listp)
     (b* (((when (endp types)) nil)
          (type (car types))
          (param (make-jparam :final? nil
                              :type (atj-type-to-jitype type)
                              :name (atj-gen-shallow-mv-field-name index)))
          (params (atj-gen-shallow-mv-params-aux (cdr types) (1+ index))))
       (cons param params)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-mv-singleton-field-name*
  :short "Name of the private static field that stores
          the singleton instance of an @(tsee mv) class."
  :long
  (xdoc::topstring-p
   "All the @(tsee mv) classes use the same name for this field.")
  "singleton")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-mv-asgs ((types atj-type-listp))
  :returns (block jblockp)
  :short "Generate the assignments in the factory method
          of the @(tsee mv) class for the given types."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-gen-shallow-mv-class-name),
     we generate Java classes that represent @(tsee mv) values.
     Each such class has a static factory method
     that re-uses a singleton instance of the class.
     The body of this method assigns the parameters
     to the corresponding fields of the singleton instance,
     which is stored in a private static field."))
  (atj-gen-shallow-mv-asgs-aux types 0)

  :prepwork
  ((define atj-gen-shallow-mv-asgs-aux ((types atj-type-listp) (index natp))
     :returns (block jblockp)
     (b* (((when (endp types)) nil)
          (param-name (atj-gen-shallow-mv-field-name index))
          (field-var (jexpr-name (str::cat *atj-mv-singleton-field-name*
                                           "."
                                           param-name)))
          (asg (jstatem-expr (jexpr-binary (jbinop-asg)
                                           field-var
                                           (jexpr-name param-name))))
          (asgs (atj-gen-shallow-mv-asgs-aux (cdr types) (1+ index))))
       (cons asg asgs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-mv-class ((types atj-type-listp))
  :guard (>= (len types) 2)
  :returns (class jclassp)
  :short "Generate the @(tsee mv) class for the given types."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-gen-shallow-mv-class-name),
     we generate Java classes that represent @(tsee mv) values,
     a different class for each tuple of types of interest.
     This is a public static final class, nested in the main class.
     It has a public instance field for each component type,
     and a private static final field that stores a singleton instance
     created in this field's initializer.
     It also has a package-private static factory method
     that reuses the singleton instance
     by assigning the arguments to the fields
     and then returning the singleton instance.
     This way, we can build an @(tsee mv) value
     without creating a new Java object.")
   (xdoc::p
    "The class and its instance fields are public because
     external Java code that calls the generated Java code
     must be able to access the results of @(tsee mv) functions.
     The factory method is not meant to be called by external Java code,
     but only internally by the generated Java code;
     it cannot be private though, only package-private
     (ideally, it would be accessible only within the generated main class,
     but Java does not provide that access control option).")
   (xdoc::p
    "Ideally, we would like to generate
     one generic Java class with 2 type parameters for 2-tuples of MV values,
     one generic Java class with 3 type parameters for 3-tuples of MV values,
     and so on.
     However, Java's restriction on generic types prevent us from doing that:
     the factory method, being static, cannot reference type parameters."))
  (b* ((name (atj-gen-shallow-mv-class-name types))
       (instance-fields (atj-gen-shallow-mv-fields types))
       (static-field (make-jfield :access (jaccess-private)
                                  :static? t
                                  :final? t
                                  :transient? nil
                                  :volatile? nil
                                  :type (jtype-class name)
                                  :name *atj-mv-singleton-field-name*
                                  :init? (jexpr-newclass (jtype-class name)
                                                         nil)))
       (method-body (append (atj-gen-shallow-mv-asgs types)
                            (jblock-return
                             (jexpr-name *atj-mv-singleton-field-name*))))
       (method (make-jmethod :access (jaccess-default)
                             :abstract? nil
                             :static? t
                             :final? nil
                             :synchronized? nil
                             :native? nil
                             :strictfp? nil
                             :result (jresult-type (jtype-class name))
                             :name *atj-mv-factory-method-name*
                             :params (atj-gen-shallow-mv-params types)
                             :throws nil
                             :body method-body)))
    (make-jclass :access (jaccess-public)
                 :abstract? nil
                 :static? t
                 :final? t
                 :strictfp? nil
                 :name name
                 :superclass? nil
                 :superinterfaces nil
                 :body (append (jfields-to-jcbody-elements
                                (append instance-fields
                                        (list static-field)))
                               (jmethods-to-jcbody-elements
                                (list method))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-mv-classes ((typess atj-type-list-listp))
  :guard (atj-gen-shallow-mv-classes-guard typess)
  :returns (classes (and (jclass-listp classes)
                         (equal (len classes) (len typess))))
  :short "Lift @(tsee atj-gen-shallow-mv-class) to lists."
  (cond ((endp typess) nil)
        (t (cons (atj-gen-shallow-mv-class (car typess))
                 (atj-gen-shallow-mv-classes (cdr typess)))))
  :guard-hints (("Goal" :in-theory (enable atj-gen-shallow-mv-classes-guard)))
  :prepwork
  ((define atj-gen-shallow-mv-classes-guard ((typess atj-type-list-listp))
     :returns (yes/no booleanp)
     (or (endp typess)
         (and (>= (len (car typess)) 2)
              (atj-gen-shallow-mv-classes-guard (cdr typess)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-all-mv-output-types ((fns-to-translate symbol-listp)
                                 (guards$ booleanp)
                                 (wrld plist-worldp))
  :returns (mv-typess (and (atj-type-list-listp mv-typess)
                           (cons-listp mv-typess)))
  :short "Collect the output types of functions that return multiple values."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-gen-shallow-mv-class-name),
     we generate Java classes that represent @(tsee mv) values.
     We generate one such class for each distinct function output type list
     of length two or more.
     We go through all the ACL2 functions to translate to Java,
     and consider the output types of the function types
     associated to each such function that returns two or more results.
     For each such list of two or more output types,
     we generate a distinct class.
     Here we just return the types,
     which are then passed to @(tsee atj-pre-translate)
     where they are augmented with any additional @(tsee mv) type
     that is not any function's output type."))
  (b* (((when (endp fns-to-translate)) nil)
       (fn (car fns-to-translate))
       ((unless (>= (atj-number-of-results fn wrld) 2))
        (atj-all-mv-output-types (cdr fns-to-translate) guards$ wrld))
       (fn-info (atj-get-function-type-info fn guards$ wrld))
       (out-typess (atj-function-type-info->outputs fn-info))
       (out-typess (remove-duplicates-equal out-typess))
       ((unless (cons-listp out-typess))
        (raise "Internal error: ~
                output types ~x0 include an empty list."
               out-typess)))
    (union-equal out-typess
                 (atj-all-mv-output-types (cdr fns-to-translate) guards$
                                          wrld)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-main-class ((pkgs string-listp)
                                    (fns-to-translate symbol-listp)
                                    (guards$ booleanp)
                                    (java-class$ stringp)
                                    (verbose$ booleanp)
                                    (wrld plist-worldp))
  :guard (no-duplicatesp-equal pkgs)
  :returns (mv (class jclassp)
               (pkg-class-names string-string-alistp :hyp (string-listp pkgs))
               (fn-method-names symbol-string-alistp
                                :hyp (symbol-listp fns-to-translate)))
  :short "Generate the main (i.e. non-test) Java class declaration,
          in the shallow embedding approach."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a public class.
     [JLS:7.6] says that a Java implementation may require
     public classes to be in files with the same names (plus extension).
     The code that we generate satisfies this requirement.")
   (xdoc::p
    "The class contains the initialization method,
     the methods to build the ACL2 packages,
     the methods to write primitive array components,
     the classes that contain methods for the ACL2 functions,
     the @(tsee mv) classes,
     the fields for quoted constants (only numbers and characters for now),
     and the static initializer.")
   (xdoc::p
    "It is critical that the static initializer
     comes before the fields for the quoted constants,
     so that the ACL2 environment is initialized
     before the field initializers, which construct ACL2 values, are executed;
     [JLS:12.4.1] says that the class initialization code
     is executed in textual order.")
   (xdoc::p
    "We ensure that the ACL2 functions natively implemented in AIJ are included,
     we organize the resulting functions by packages,
     and we proceed to generate the Java nested classes,
     after the methods to build the packages.")
   (xdoc::p
    "We also return the alist from ACL2 package names to Java class names
     and the alist from ACL2 function symbols to Java method names,
     which must be eventually passed to the functions that generate
     the Java test class.")
   (xdoc::p
    "We initialize the symbols of the @(tsee atj-qconstants) structure
     with @('t') and @('nil'),
     because their Java representations are sometimes generated
     even when these two symbols are not used in any of the ACL2 functions
     that are translated to Java."))
  (b* (((run-when verbose$)
        (cw "~%Generate the Java methods to build the ACL2 packages:~%"))
       (pkg-methods (atj-gen-pkg-methods pkgs verbose$))
       (pkg-methods (mergesort-jmethods pkg-methods))
       (jprimarr-methods (append (atj-gen-shallow-primarray-write-methods)
                                 (atj-gen-shallow-jprimarr-conversion-methods)))
       (fns+natives (append fns-to-translate *aij-natives*))
       ((unless (no-duplicatesp-eq fns+natives))
        (raise "Internal error: ~
                the list ~x0 of function names has duplicates." fns+natives)
        (mv (ec-call (jclass-fix :irrelevant)) nil nil))
       (mv-typess (atj-all-mv-output-types fns-to-translate guards$ wrld))
       (pkg-class-names (atj-pkgs-to-classes pkgs java-class$))
       (fn-method-names (atj-fns-to-methods fns+natives))
       (fns-by-pkg (organize-symbols-by-pkg fns+natives))
       (qconsts (make-atj-qconstants :integers nil
                                     :rationals nil
                                     :numbers nil
                                     :chars nil
                                     :strings nil
                                     :symbols (list t nil)
                                     :pairs nil
                                     :next-index 1))
       ((mv methods-by-pkg qconsts mv-typess)
        (atj-gen-shallow-all-pkg-methods pkgs
                                         fns-by-pkg
                                         fns+natives
                                         qconsts
                                         pkg-class-names
                                         fn-method-names
                                         mv-typess
                                         guards$
                                         verbose$
                                         wrld))
       ((unless (atj-gen-shallow-mv-classes-guard mv-typess))
        (raise "Internal error: ~
                not all lists of types in ~x0 have length 2 or more."
               mv-typess)
        (mv (ec-call (jclass-fix :irrelevant)) nil nil))
       (mv-classes (atj-gen-shallow-mv-classes mv-typess))
       ((atj-qconstants qconsts) qconsts)
       (qsymbols qconsts.symbols)
       (qsymbols-by-pkg (organize-symbols-by-pkg qsymbols))
       (fields-by-pkg (atj-gen-shallow-all-pkg-fields pkgs
                                                      qsymbols
                                                      qsymbols-by-pkg))
       ((run-when verbose$)
        (cw "~%Generate the Java classes for the ACL2 packages:~%"))
       (pkg-classes (atj-gen-shallow-pkg-classes pkgs
                                                 fields-by-pkg
                                                 methods-by-pkg
                                                 pkg-class-names
                                                 verbose$))
       ((run-when verbose$)
        (cw "~%Generate the main Java class.~%"))
       (qinteger-fields (atj-gen-shallow-number-fields qconsts.integers))
       (qrational-fields (atj-gen-shallow-number-fields qconsts.rationals))
       (qnumber-fields (atj-gen-shallow-number-fields qconsts.numbers))
       (qchar-fields (atj-gen-shallow-char-fields qconsts.chars))
       (qstring-fields (atj-gen-shallow-string-fields qconsts.strings))
       (qcons-fields (atj-gen-shallow-cons-fields (strip-cars qconsts.pairs)
                                                  qconsts.pairs))
       (all-qconst-fields (append qinteger-fields
                                  qrational-fields
                                  qnumber-fields
                                  qchar-fields
                                  qstring-fields
                                  qcons-fields))
       (all-qconst-fields (mergesort-jfields all-qconst-fields))
       (static-init (atj-gen-shallow-static-initializer pkgs))
       (init-method (atj-gen-init-method))
       (body-class (append (list (jcbody-element-init static-init))
                           (jmethods-to-jcbody-elements pkg-methods)
                           (jmethods-to-jcbody-elements jprimarr-methods)
                           (jfields-to-jcbody-elements all-qconst-fields)
                           (jclasses-to-jcbody-elements mv-classes)
                           (jclasses-to-jcbody-elements pkg-classes)
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
        fn-method-names))

  :prepwork

  ((local (include-book "std/typed-lists/symbol-listp" :dir :system))

   (defrulel verify-guards-lemma
     (implies (cons-pos-alistp alist)
              (alistp (strip-cars alist))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-main-cunit ((guards$ booleanp)
                                    (java-package$ stringp)
                                    (java-class$ stringp)
                                    (pkgs string-listp)
                                    (fns-to-translate symbol-listp)
                                    (verbose$ booleanp)
                                    (wrld plist-worldp))
  :guard (no-duplicatesp-equal pkgs)
  :returns (mv (cunit jcunitp)
               (pkg-class-names string-string-alistp :hyp (string-listp pkgs))
               (fn-method-names symbol-string-alistp
                                :hyp (symbol-listp fns-to-translate)))
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
        (atj-gen-shallow-main-class
         pkgs fns-to-translate guards$ java-class$ verbose$ wrld))
       ((run-when verbose$)
        (cw "~%Generate the main Java compilation unit.~%"))
       (cunit
        (make-jcunit
         :package? java-package$
         :imports (list
                   (make-jimport :static? nil
                                 :target (str::cat *aij-package* ".*"))
                   ;; keep in sync with *ATJ-DISALLOWED-CLASS-NAMES*:
                   (make-jimport :static? nil :target "java.math.BigInteger")
                   (make-jimport :static? nil :target "java.util.ArrayList")
                   (make-jimport :static? nil :target "java.util.List"))
         :types (list class))))
    (mv cunit pkg-class-names fn-method-names)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-test-code ((test-function symbolp)
                                   (test-inputs atj-test-value-listp)
                                   (test-outputs atj-test-value-listp)
                                   (comp-var stringp)
                                   (guards$ booleanp)
                                   (java-class$ stringp)
                                   (pkg-class-names string-string-alistp)
                                   (fn-method-names symbol-string-alistp)
                                   (wrld plist-worldp))
  :guard (consp test-outputs)
  :returns (mv (arg-block jblockp)
               (ares-block jblockp)
               (call-block jblockp)
               (jres-block jblockp)
               (comp-block jblockp))
  :short "Generate the code of a test method
          that is specific to the shallow embedding approach."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee atj-gen-test-method),
     which generates a Java method
     to run one of the tests specified in the @(':tests') input to ATJ.
     Most of that method's code is the same for deep and shallow embedding.
     The only varying parts are the ones returned by this function,
     and by @(tsee atj-gen-deep-test-code) for the deep embedding.")
   (xdoc::p
    "The first block returned by this function
     builds the input values of the test,
     and assigns them to separate variables.
     We store them into variables,
     instead of passing their expressions
     directly to the method being tested,
     is to accurately measure just the time of each call
     (see @(tsee atj-gen-test-method) for details),
     without the time needed to compute the expressions.
     The variables' names are @('argument1'), @('argument2'), etc.")
   (xdoc::p
    "The second block returned by this function
     builds the output values of the test and assigns them to variables.
     If there is just one output value,
     it is assigned to a variable @('acl2Result').
     Otherwise, they are assigned to @('acl2Result0'), @('acl2Result1'), etc.,
     consistently with the zero-based index passed to @(tsee mv-nth).")
   (xdoc::p
    "The third block returned by this function
     calls the Java method that represents the ACL2 function being tested
     on the local variables that store the arguments.
     Since this code is in a class that is different from
     any of the generated Java classes that correspond to ACL2 packages,
     the Java method to call must be always preceded by the class name:
     thus, we use @('\"KEYWORD\"') as current package name,
     which never contains any functions.
     The method's result is stored into a variable @('javaResult').
     The type of the variable is determined from
     the output types of the function that correspond to the arguments,
     but if it is an @(tsee mv) class we need to qualify its name
     with the name of the main Java class generated
     (the code to do this is not very elegant and should be improved).")
   (xdoc::p
    "The fourth block is empty
     if the ACL2 function corresponding to the method being tested
     is single-valued.
     If instead it is multi-valued,
     this block assigns the field of @('javaResult'),
     which is an instance of an @(tsee mv) class,
     to @('javaResult0'), @('javaResult1'), etc.")
   (xdoc::p
    "The fourth block returned by this function
     compares the test outputs with the call outputs for equality,
     assigning the boolean result to a variable.
     The name of this variable is passed as argument to this function,
     since it is also used in @(tsee atj-gen-test-method),
     thus preventing this and that function to go out of sync
     in regard to this shared variable name."))
  (b* (((mv arg-val-block
            arg-exprs
            arg-types
            jvar-value-index)
        (atj-gen-test-values test-inputs "value" 1))
       ((mv arg-asg-block
            arg-vars)
        (atj-gen-shallow-test-code-asgs arg-exprs arg-types "argument" 1))
       (arg-block (append arg-val-block arg-asg-block))
       (singletonp (= (len test-outputs) 1))
       ((mv ares-val-block
            ares-exprs
            &
            &)
        (atj-gen-test-values test-outputs "value" jvar-value-index))
       (fn-info (atj-get-function-type-info test-function guards$ wrld))
       (main-fn-type (atj-function-type-info->main fn-info))
       (other-fn-types (atj-function-type-info->others fn-info))
       (all-fn-types (cons main-fn-type other-fn-types))
       (fn-type? (atj-function-type-of-min-input-types arg-types all-fn-types))
       ((unless fn-type?)
        (raise "Internal error: ~
                the argument types ~x0 ~
                do not have a corresponding Java overloaded method."
               arg-types)
        (mv nil nil nil nil nil))
       (out-types (atj-function-type->outputs fn-type?))
       ((unless (= (len out-types) (len test-outputs)))
        (raise "Internal error: ~
                the number of output types ~x0 of function ~x1 ~
                does not match the number of test outputs ~x2."
               out-types test-function test-outputs)
        (mv nil nil nil nil nil))
       ((mv ares-asg-block
            ares-vars)
        (if singletonp
            (mv (jblock-locvar (atj-type-to-jitype (car out-types))
                               "acl2Result"
                               (car ares-exprs))
                (list "acl2Result"))
          (atj-gen-shallow-test-code-asgs ares-exprs
                                          out-types
                                          "acl2Result" 0)))
       (ares-block (append ares-val-block ares-asg-block))
       (call-expr (jexpr-smethod (jtype-class java-class$)
                                 (atj-gen-shallow-fnname test-function
                                                         pkg-class-names
                                                         fn-method-names
                                                         "KEYWORD")
                                 (jexpr-name-list arg-vars)))
       (call-jtype (atj-gen-shallow-jtype out-types))
       (call-jtype (if (jtype-case call-jtype :class)
                       (b* ((name (jtype-class->name call-jtype)))
                         (if (and (>= (length name) 3)
                                  (eql (char name 0) #\M)
                                  (eql (char name 1) #\V)
                                  (eql (char name 2) #\_))
                             (jtype-class (str::cat java-class$ "." name))
                           call-jtype))
                     call-jtype))
       (call-block (jblock-locvar call-jtype "javaResult" call-expr))
       ((mv jres-block
            jres-vars)
        (if singletonp
            (mv nil (list "javaResult"))
          (atj-gen-shallow-test-code-mv-asgs (jexpr-name "javaResult")
                                             out-types
                                             "javaResult" 0)))
       (comp-block (append (jblock-locvar (jtype-boolean)
                                          comp-var
                                          (jexpr-literal-true))
                           (atj-gen-shallow-test-code-comps ares-vars
                                                            jres-vars
                                                            out-types
                                                            comp-var))))
    (mv arg-block
        ares-block
        call-block
        jres-block
        comp-block))

  :prepwork

  ((define atj-gen-shallow-test-code-asgs ((exprs jexpr-listp)
                                           (types atj-type-listp)
                                           (var-base stringp)
                                           (index natp))
     :guard (= (len exprs) (len types))
     :returns (mv (block jblockp)
                  (vars string-listp))
     (cond ((endp exprs) (mv nil nil))
           (t (b* ((first-var (str::cat var-base (str::natstr index)))
                   (first-type (car types))
                   (first-jtype (atj-type-to-jitype first-type))
                   (first-expr (jexpr-cast (atj-type-to-jitype first-type)
                                           (car exprs)))
                   (first-block (jblock-locvar first-jtype
                                               first-var
                                               first-expr))
                   ((mv rest-block rest-vars)
                    (atj-gen-shallow-test-code-asgs (cdr exprs)
                                                    (cdr types)
                                                    var-base
                                                    (1+ index))))
                (mv (append first-block rest-block)
                    (cons first-var rest-vars)))))
     ///
     (defret len-of-atj-gen-shallow-test-code-asgs.vars
       (equal (len vars) (len exprs))))

   (define atj-gen-shallow-test-code-mv-asgs ((expr jexprp)
                                              (types atj-type-listp)
                                              (var-base stringp)
                                              (index natp))
     :returns (mv (block jblockp)
                  (vars string-listp))
     (cond ((endp types) (mv nil nil))
           (t (b* ((first-var (str::cat var-base (str::natstr index)))
                   (first-type (car types))
                   (first-jtype (atj-type-to-jitype first-type))
                   (first-expr (jexpr-get-field expr
                                                (atj-gen-shallow-mv-field-name
                                                 index)))
                   (first-block (jblock-locvar first-jtype
                                               first-var
                                               first-expr))
                   ((mv rest-block rest-vars)
                    (atj-gen-shallow-test-code-mv-asgs expr
                                                       (cdr types)
                                                       var-base
                                                       (1+ index))))
                (mv (append first-block rest-block)
                    (cons first-var rest-vars)))))
     ///
     (defret len-of-atj-gen-shallow-test-code-mv-asgs.vars
       (equal (len vars)
              (len types))))

   (define atj-gen-shallow-test-code-comps ((ares-vars string-listp)
                                            (jres-vars string-listp)
                                            (types atj-type-listp)
                                            (comp-var stringp))
     :guard (and (= (len jres-vars) (len ares-vars))
                 (= (len types) (len ares-vars)))
     :returns (block jblockp)
     (cond ((endp ares-vars) nil)
           (t (b* ((ares-var (car ares-vars))
                   (jres-var (car jres-vars))
                   (type (car types))
                   (comp-expr (atj-type-case
                               type
                               :jprim
                                (jexpr-binary (jbinop-eq)
                                              (jexpr-name ares-var)
                                              (jexpr-name jres-var))
                               :jprimarr
                                (jexpr-smethod (jtype-class "Arrays")
                                               "equals"
                                               (list (jexpr-name ares-var)
                                                     (jexpr-name jres-var)))
                                :acl2
                                (jexpr-method (str::cat ares-var ".equals")
                                              (list (jexpr-name jres-var)))))
                   (comp-block (jblock-expr
                                (jexpr-binary (jbinop-asg-and)
                                              (jexpr-name comp-var)
                                              comp-expr)))
                   (rest-block (atj-gen-shallow-test-code-comps (cdr ares-vars)
                                                                (cdr jres-vars)
                                                                (cdr types)
                                                                comp-var)))
                (append comp-block rest-block)))))

   (defrulel verify-guards-lemma
     (implies (and (equal (len x) (len y))
                   (consp x))
              (consp y)))))
