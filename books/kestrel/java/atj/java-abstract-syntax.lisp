; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "../language/primitive-types")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/std/util/deffixer" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

; this is to have FTY::DEFLIST generate more theorems:
(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-java-abstract-syntax
  :parents (atj-implementation)
  :short "An abstract syntax of Java for ATJ's implementation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is not meant as a complete formalization
     of an abstract syntax for Java.
     It is just part of the implementation of ATJ,
     and it suffices for that purpose,
     namely that ATJ generates this abstract syntax
     and then pretty-prints it to files.
     This is why this abstract syntax is under @('[books]/kestrel/java/atj'),
     not under @('[books]/kestrel/java/language').")
   (xdoc::p
    "This abstract syntax may be eventually superseded
     by a complete formalization under @('[books]/kestrel/java/language').")
   (xdoc::p
    "The following remarks apply to this abstract syntax in general,
     and so they are stated here instead of being repeated in several places:")
   (xdoc::ul
    (xdoc::li
     "We do not capture annotations.")
    (xdoc::li
     "We do not explicitly capture parameterized types, type variables, etc.
      However, since we use arbitrary ACL2 strings for types,
      @('<') and @('>') may be included as part of these strings.")
    (xdoc::li
     "We use ACL2 strings and characters to capture Java strings and characters,
      which is more restrictive because ACL2 characters are 8-bit,
      while Java characters are 16-bit.
      However, 8-bit characters suffice for ATJ's purposes,
      which only generates ASCII Java code.")
    (xdoc::li
     "We use ACL2 strings to capture
      Java identifiers and dot-separated sequenced thereof.
      On one hand, this is more restrictive
      because of the 8-bit vs. 16-bit character issue;
      on the other hand, it is more permissive
      because it allows characters that are invalid for Java identifiers.
      However, 8-bit characters suffice for ATJ's purposes,
      which only generates ASCII Java code.
      Furthermore, ATJ always does produce ACL2 strings
      that are valid Java identifiers, or dot-separated sequences thereof.")))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Library extensions.

(defsection string-list
  :short "Fixtype of true lists of ACL2 strings,
          i.e. values recognized by @(tsee string-listp)."
  :long
  (xdoc::topstring-p
   "This is not specific to Java,
    and it should be moved to a more general library eventually.")

  (std::deffixer string-list-fix
    :pred string-listp
    :body-fix nil
    :parents (string-list)
    :short "Fixer for @(tsee string-list).")

  (fty::deffixtype string-list
    :pred string-listp
    :fix string-list-fix
    :equiv string-list-equiv
    :define t
    :forward t))

(defsection maybe-string
  :short "Fixtype of ACL2 strings and @('nil'),
          i.e. values recognized by @(tsee maybe-stringp)."
  :long
  (xdoc::topstring-p
   "This is not specific to Java,
    and it should be moved to a more general library eventually.")

  (std::deffixer maybe-string-fix
    :pred maybe-stringp
    :body-fix nil
    :parents (maybe-string)
    :short "Fixer for @(tsee maybe-string).")

  (fty::deffixtype maybe-string
    :pred maybe-stringp
    :fix maybe-string-fix
    :equiv maybe-string-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum jintbase
  :short "Java bases for integer literals [JLS:3.10.1]."
  (:decimal ())
  (:hexadecimal ())
  (:octal ())
  (:binary ())
  :pred jintbasep)

(fty::deftagsum jliteral
  :short "Java literals [JLS:3.10]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For an integer literal, we capture its value (a natural number)
     and whether there is an integer type suffix (@('l') or @('L')) or not,
     i.e. if the literal has type @('long').
     We do not restrict the natural number
     to the range of type @('int') or @('long'),
     but ATJ always produces correct integer literals.")
   (xdoc::p
    "We only support a very limited form of floating-point literals for now,
     whose value is actually just a natural number."))
  (:integer ((value acl2::nat) (long? bool) (base jintbase)))
  (:floating ((value acl2::nat)))
  (:boolean ((value bool)))
  (:character ((value character)))
  (:string ((value string)))
  (:null ())
  :pred jliteralp)

(fty::deflist jliteral-list
  :short "True lists of Java literals."
  :elt-type jliteral
  :true-listp t
  :elementp-of-nil nil
  :pred jliteral-listp)

(fty::deftagsum jtype
  :short "Java types [JLS:4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We capture all eight primitive types.")
   (xdoc::p
    "We use ACL2 strings to capture not only single type identifiers,
     but also dot-separated sequences with package names and type identifiers:
     the latter have dots in the ACL2 strings.
     This also accommodates types with type arguments,
     by using @('<') and @('>') in the ACL2 strings.
     Since the Java grammar defines @('InterfaceType') as @('ClassType'),
     we use @(':class') for both class and interface types;
     this is consistent with similar terminology in Java
     (e.g.\ a `class file' may define an interface.)")
   (xdoc::p
    "We capture array types via a natural recursive structure,
     by wrapping the component type."))
  (:prim ((type primitive-type)))
  (:class ((name string)))
  (:array ((comp jtype)))
  :pred jtypep)

(define jtype-boolean ()
  :returns (type jtypep)
  :short "Build the Java primitive type @('boolean')."
  (jtype-prim (primitive-type-boolean)))

(define jtype-char ()
  :returns (type jtypep)
  :short "Build the Java primitive type @('char')."
  (jtype-prim (primitive-type-char)))

(define jtype-byte ()
  :returns (type jtypep)
  :short "Build the Java primitive type @('byte')."
  (jtype-prim (primitive-type-byte)))

(define jtype-short ()
  :returns (type jtypep)
  :short "Build the Java primitive type @('short')."
  (jtype-prim (primitive-type-short)))

(define jtype-int ()
  :returns (type jtypep)
  :short "Build the Java primitive type @('int')."
  (jtype-prim (primitive-type-int)))

(define jtype-long ()
  :returns (type jtypep)
  :short "Build the Java primitive type @('long')."
  (jtype-prim (primitive-type-long)))

(define jtype-float ()
  :returns (type jtypep)
  :short "Build the Java primitive type @('float')."
  (jtype-prim (primitive-type-float)))

(define jtype-double ()
  :returns (type jtypep)
  :short "Build the Java primitive type @('double')."
  (jtype-prim (primitive-type-double)))

(fty::deflist jtype-list
  :short "True lists of Java types."
  :elt-type jtype
  :true-listp t
  :elementp-of-nil nil
  :pred jtype-listp)

(fty::deftagsum junop
  :short "Java unary operators [JLS:15.15]."
  (:preinc ()) ; ++
  (:predec ()) ; --
  (:uplus ()) ; +
  (:uminus ()) ; -
  (:bitcompl ()) ; ~
  (:logcompl ()) ; !
  :pred junopp)

(fty::deftagsum jbinop
  :short "Java binary operators [JLS:15.17-26]."
  :long
  (xdoc::topstring-p
   "We do not include @('instanceof') here because
    it does not operate on two expressions, just one:
    its right-hand side is a reference type, not an expression.")
  (:mul ()) ; *
  (:div ()) ; /
  (:rem ()) ; %
  (:add ()) ; +
  (:sub ()) ; -
  (:shl ()) ; <<
  (:sshr ()) ; >>
  (:ushr ()) ; >>>
  (:lt ()) ; <
  (:gt ()) ; >
  (:le ()) ; <=
  (:ge ()) ; >=
  (:eq ()) ; ==
  (:ne ()) ; !=
  (:and ()) ; &
  (:xor ()) ; ^
  (:ior ()) ; |
  (:condand ()) ; &&
  (:condor ()) ; ||
  (:asg ()) ; =
  (:asg-mul ()) ; *=
  (:asg-div ()) ; /=
  (:asg-rem ()) ; %=
  (:asg-add ()) ; +=
  (:asg-sub ()) ; -=
  (:asg-shl ()) ; <<=
  (:asg-sshr ()) ; >>=
  (:asg-ushr ()) ; >>>=
  (:asg-and ()) ; &=
  (:asg-xor ()) ; ^=
  (:asg-ior ()) ; |=
  :pred jbinopp)

(fty::deftypes jexprs
  :short "Java expressions [JLS:15]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not capture
     lambda expressions,
     class literals, and
     method references.")
   (xdoc::p
    "For expression names [JLS:6.5], we use ACL2 strings,
     which allow dot-separated identifiers,
     as well as @('this') and @('super').")
   (xdoc::p
    "We only capture monodimensional array creation expressions
     with either an explicit size that is an expression
     or an array initializer that is a sequence of expressions.
     The type field is the primitive or class/interface element type,
     not the array type, which is implicitly the one
     whose element type if the one in the type field.")
   (xdoc::p
    "In an array access expression,
     we allow any expression as the first one.")
   (xdoc::p
    "We only capture class instance creation expressions
     that consist of @('new'), a class name, and contructor arguments.")
   (xdoc::p
    "In a field access expression,
     we allow any expression as the first one.")
   (xdoc::p
    "We capture method invocations of three kinds:
     static (which start with a type),
     instance (which start with an expression),
     and generic (which start with the method name).
     The generic ones may be static or instance,
     depending on how the Java compiler resolves them.
     This is a rough model of Java method invocation expressions,
     but it suffices for ATJ's purposes.")
   (xdoc::p
    "We also include parenthesized expressions,
     which normally do not belong to an abstract syntax
     because the tree structure of the abstract syntax
     provides the intended grouping of the nested expressions.
     However, having explicit parenthesized expressions in the abstract syntax
     provides more flexibility,
     e.g. to capture parentheses that would not be needed for corectness
     but could perhaps improve clarity and readability.")
   (xdoc::p
    "The abstract syntax allows any type, not just reference types,
     as the right-hand side of @('instanceof').
     This may be improved in the future."))

  (fty::deftagsum jexpr
    (:literal ((get jliteral)))
    (:name ((get string)))
    (:newarray ((type jtype) (size jexpr)))
    (:newarray-init ((type jtype) (init jexpr-list)))
    (:array ((array jexpr) (index jexpr)))
    (:newclass ((type jtype) (args jexpr-list)))
    (:field ((target jexpr) (name string)))
    (:method ((name string) (args jexpr-list)))
    (:smethod ((type jtype) (name string) (args jexpr-list)))
    (:imethod ((target jexpr) (name string) (args jexpr-list)))
    (:postinc ((arg jexpr))) ; ++
    (:postdec ((arg jexpr))) ; --
    (:cast ((type jtype) (arg jexpr)))
    (:unary ((op junop) (arg jexpr)))
    (:binary ((op jbinop) (left jexpr) (right jexpr)))
    (:instanceof ((left jexpr) (right jtype)))
    (:cond ((test jexpr) (then jexpr) (else jexpr)))
    (:paren ((get jexpr)))
    :pred jexprp)

  (fty::deflist jexpr-list
    :elt-type jexpr
    :true-listp t
    :elementp-of-nil nil
    :pred jexpr-listp))

(define jexpr-name-list ((names string-listp))
  :returns (exprs jexpr-listp)
  :short "Lift @(tsee jexpr-name) to lists."
  (cond ((endp names) nil)
        (t (cons (jexpr-name (car names))
                 (jexpr-name-list (cdr names))))))

(fty::defoption maybe-jexpr
  jexpr
  :short "Java expressions or @('nil')."
  :pred maybe-jexprp)

(define jexpr-literal-integer-decimal ((value natp))
  :returns (expr jexprp)
  :short "Build a Java expression consisting of an integer literal
          in base 10 without integer type prefix (i.e. of type @('int')."
  (jexpr-literal
   (make-jliteral-integer :value value :long? nil :base (jintbase-decimal))))

(define jexpr-literal-integer-long-decimal ((value natp))
  :returns (expr jexprp)
  :short "Build a Java expression consisting of an integer literal
          in base 10 with integer type prefix (i.e. of type @('long')."
  (jexpr-literal
   (make-jliteral-integer :value value :long? t :base (jintbase-decimal))))

(define jexpr-literal-0 ()
  :returns (expr jexprp)
  :short "Build a Java expression consisting of the integer literal 0."
  (jexpr-literal-integer-decimal 0))

(define jexpr-literal-1 ()
  :returns (expr jexprp)
  :short "Build a Java expression consisting of the integer literal 1."
  (jexpr-literal-integer-decimal 1))

(define jexpr-literal-floating ((value natp))
  :returns (expr jexprp)
  :short "Build a Java expression consisting of a floating-point literal."
  (jexpr-literal (jliteral-floating value)))

(define jexpr-literal-true ()
  :returns (expr jexprp)
  :short "Build a Java expression consisting of
          the boolean literal @('true')."
  (jexpr-literal (jliteral-boolean t)))

(define jexpr-literal-false ()
  :returns (expr jexprp)
  :short "Build a Java expression consisting of
          the boolean literal @('false')."
  (jexpr-literal (jliteral-boolean nil)))

(define jexpr-literal-character ((char characterp))
  :returns (expr jexprp)
  :short "Build a Java expression consisting of a character literal."
  (jexpr-literal (jliteral-character char)))

(define jexpr-literal-string ((string stringp))
  :returns (expr jexprp)
  :short "Build a Java expression consisting of a string literal."
  (jexpr-literal (jliteral-string string)))

(define jexpr-literal-null ()
  :returns (expr jexprp)
  :short "Build a Java expression consisting of the null literal."
  (jexpr-literal (jliteral-null)))

(define jexpr-get-field ((expr jexprp) (name stringp))
  :returns (get-field-expr jexprp)
  :short "Build a Java expression to access a field."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the Java grammar,
     not all expressions that access fields
     can be derived from @('field-access').
     When the target object is an expression name,
     the field access expression is also an expression name."))
  (if (jexpr-case expr :name)
      (jexpr-name (str::cat (jexpr-name->get expr) "." name))
    (jexpr-field expr name)))

(fty::defprod jlocvar
  :short "Local variable declarations [JLS:14.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only capture declarations of single local variables
     without array square brackets after the name
     (i.e. all the array square brackets are in the type).
     The declarations have an optional initializer.")
   (xdoc::p
    "We do not capture @('var')."))
  ((final? bool)
   (type jtype)
   (name string)
   (init? maybe-jexpr))
  :pred jlocvarp)

(fty::deftypes jstatems+jblocks
  :short "Java statements and blocks [JLS:14]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unlike [JLS:14.2],
     we do not distinguish between statements and block statements:
     we just have block statements, and call them statements.")
   (xdoc::p
    "We do not capture
     class declarations,
     the empty statement,
     labeled statements,
     @('synchronized'), and
     @('try').")
   (xdoc::p
    "We only capture @('if') statements
     whose @('then') (and @('else'), if present) parts are blocks.
     (This is not a significant limitation.)")
   (xdoc::p
    "We only capture @('for') statements
     with single initialization and update expressions,
     and whose bodies are block.
     (The latter is not a significant limitation.)")
   (xdoc::p
    "We only capture @('do') statements whose bodies are block.
     (This is not a significant limitation.)")
   (xdoc::p
    "We only capture @('continue') and @('break') statements
     without labels."))

  (fty::deftagsum jstatem
    (:locvar ((get jlocvar)))
    (:expr ((get jexpr)))
    (:return ((expr? maybe-jexpr)))
    (:throw ((expr jexpr)))
    (:break ())
    (:continue ())
    (:if ((test jexpr) (then jblock)))
    (:ifelse ((test jexpr) (then jblock) (else jblock)))
    (:while ((test jexpr) (body jblock)))
    (:do ((body jblock) (test jexpr)))
    (:for ((init jexpr) (test jexpr) (update jexpr) (body jblock)))
    :pred jstatemp)

  (fty::deflist jblock
    :elt-type jstatem
    :true-listp t
    :elementp-of-nil nil
    :pred jblockp)

  ///

  (defrule jblock-count-of-butlast-upper-bound
    (<= (jblock-count (butlast block n))
        (jblock-count block))
    :rule-classes :linear
    :enable jblock-count
    :prep-books ((include-book "std/lists/butlast" :dir :system)))

  (defrule jblock-count-of-append
    (equal (jblock-count (append block1 block2))
           (+ (jblock-count block1)
              (jblock-count block2)
              -1))
    :enable (jblock-count append)))

(define jblock-locvar ((type jtypep) (name stringp) (init? maybe-jexprp))
  :returns (block jblockp)
  :short "Build a block consisting of
          a single (non-final) local variable declaration statement."
  (list (jstatem-locvar
         (make-jlocvar :final? nil :type type :name name :init? init?))))

(define jblock-locvar-final ((type jtypep) (name stringp) (init? maybe-jexprp))
  :returns (block jblockp)
  :short "Build a block consisting of
          a single final local variable declaration statement."
  (list (jstatem-locvar
         (make-jlocvar :final? t :type type :name name :init? init?))))

(define jblock-expr ((expr jexprp))
  :returns (block jblockp)
  :short "Build a block consisting of a single Java expression
          (as an expression statement."
  (list (jstatem-expr expr)))

(define jblock-method ((name stringp) (args jexpr-listp))
  :returns (block jblockp)
  :short "Build a block consisting of a single Java method call."
  (jblock-expr (jexpr-method name args)))

(define jblock-smethod ((type jtypep) (name stringp) (args jexpr-listp))
  :returns (block jblockp)
  :short "Build a block consisting of a single Java static method call."
  (jblock-expr (jexpr-smethod type name args)))

(define jblock-imethod ((target jexprp) (name stringp) (args jexpr-listp))
  :returns (block jblockp)
  :short "Build a block consisting of a single Java instance method call."
  (jblock-expr (jexpr-imethod target name args)))

(define jblock-asg ((left jexprp) (right jexprp))
  :returns (block jblockp)
  :short "Build a block consisting of a single Java assignment."
  (jblock-expr (jexpr-binary (jbinop-asg) left right)))

(define jblock-asg-name ((left stringp) (right jexprp))
  :returns (block jblockp)
  :short "Build a block consisting of a single Java assignment
          where the left-hand side is a named expression."
  (jblock-expr (jexpr-binary (jbinop-asg) (jexpr-name left) right)))

(define jblock-return ((expr? maybe-jexprp))
  :returns (block jblockp)
  :short "Build a block consisting of a single Java @('return') statement."
  (list (jstatem-return expr?)))

(define jblock-throw ((expr jexprp))
  :returns (block jblockp)
  :short "Build a block consisting of a single Java @('throw') statement."
  (list (jstatem-throw expr)))

(define jblock-break ()
  :returns (block jblockp)
  :short "Build a block consisting of a single Java @('break') statement."
  (list (jstatem-break)))

(define jblock-continue ()
  :returns (block jblockp)
  :short "Build a block consisting of a single Java @('continue') statement."
  (list (jstatem-continue)))

(define jblock-if ((test jexprp) (then jblockp))
  :returns (block jblockp)
  :short "Build a block consisting of a single Java @('if') statement."
  (list (jstatem-if test then)))

(define jblock-ifelse ((test jexprp) (then jblockp) (else jblockp))
  :returns (block jblockp)
  :short "Build a block consisting of a single Java @('if-else') statement."
  (list (jstatem-ifelse test then else)))

(define jblock-while ((test jexprp) (body jblockp))
  :returns (block jblockp)
  :short "Build a block consisting of a single Java @('while') statement."
  (list (jstatem-while test body)))

(define jblock-do ((body jblockp) (test jexprp))
  :returns (block jblockp)
  :short "Build a block consisting of a single Java @('do') statement."
  (list (jstatem-do body test)))

(define jblock-for ((init jexprp) (test jexprp) (update jexprp) (body jblockp))
  :returns (block jblockp)
  :short "Bulid a block consisting of a single Java @('for') statement."
  (list (jstatem-for init test update body)))

(fty::deflist jblock-list
  :short "True lists of Java blocks."
  :elt-type jblock
  :true-listp t
  :elementp-of-nil t
  :pred jblock-listp
  ///

  (defrule jblockp-of-flatten-when-jblock-listp
    (implies (jblock-listp blocks)
             (jblockp (flatten blocks)))
    :enable flatten))

(fty::deftagsum jaccess
  :short "Java access modifiers [JLS:8.1.1] [JLS:8.3.1] [JLS:8.4.3]."
  (:public ())
  (:protected ())
  (:private ())
  (:default ())
  :pred jaccessp)

(fty::defprod jfield
  :short "Java field declarations [JLS:8.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only capture declarations of single fields,
     with or without an initializer,
     and without array square brackets after the name
     (i.e. all the array square brackets are in the type)."))
  ((access jaccess)
   (static? bool)
   (final? bool)
   (transient? bool)
   (volatile? bool)
   (type jtype)
   (name string)
   (init? maybe-jexpr))
  :pred jfieldp)

(fty::deflist jfield-list
  :short "True lists of Java field declarations."
  :elt-type jfield
  :true-listp t
  :elementp-of-nil nil
  :pred jfield-listp)

(fty::deftagsum jresult
  :short "Result of a Java method [JLS:8.4.5]."
  (:type ((get jtype)))
  (:void ())
  :pred jresultp)

(fty::defprod jparam
  :short "Java formal parameter [JLS:8.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not capture variable arity parameters.")
   (xdoc::p
    "We only capture parameters without array square brackets after the name
     (i.e. all the array square brackets are in the type)."))
  ((final? bool)
   (type jtype)
   (name string))
  :pred jparamp)

(fty::deflist jparam-list
  :short "True lists of Java formal parameters."
  :elt-type jparam
  :true-listp t
  :elementp-of-nil nil
  :pred jparam-listp)

(define jparam-list->names ((params jparam-listp))
  :returns (names string-listp)
  :short "Lift @(tsee jparam->name) to lists."
  (cond ((endp params) nil)
        (t (cons (jparam->name (car params))
                 (jparam-list->names (cdr params)))))
  ///
  (defrule len-of-jparam-list->names
    (equal (len (jparam-list->names params))
           (len params))
    :rule-classes :linear))

(define jparam-list->types ((params jparam-listp))
  :returns (types jtype-listp)
  :short "Lift @(tsee jparam->type) to lists."
  (cond ((endp params) nil)
        (t (cons (jparam->type (car params))
                 (jparam-list->types (cdr params)))))
  ///
  (defrule len-of-jparam-list->types
    (equal (len (jparam-list->types params))
           (len params))
    :rule-classes :linear))

(fty::defprod jmethod
  :short "Java method declarations [JLS:8.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not capture receiver parameters.")
   (xdoc::p
    "We do not capture array square brackets after the parameter list
     (i.e. all the array square brackets are in the type).")
   (xdoc::p
    "We do not capture the case of a method without body."))
  ((access jaccess)
   (abstract? bool)
   (static? bool)
   (final? bool)
   (synchronized? bool)
   (native? bool)
   (strictfp? bool)
   (result jresult)
   (name string)
   (params jparam-list)
   (throws string-list)
   (body jblock))
  :pred jmethodp)

(fty::deflist jmethod-list
  :short "True lists of Java method declarations."
  :elt-type jmethod
  :true-listp t
  :elementp-of-nil nil
  :pred jmethod-listp)

(fty::defprod jcinitializer
  :short "Java class initializer [JLS:8.6] [JLS:8.7]."
  :long
  (xdoc::topstring-p
   "This captures both static and instance intializers.")
  ((static? bool)
   (code jblock))
  :pred jcinitializerp)

(fty::deftypes jclasses+jcmembers

  (fty::deftagsum jcmember
    :short "Java class member declarations [JLS:8.1.6]."
    :long
    (xdoc::topstring
     (xdoc::p
      "We do not capture interface declarations."))
    (:field ((get jfield)))
    (:method ((get jmethod)))
    (:class ((get jclass)))
    :pred jcmemberp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deftagsum jcbody-element
    :short "Java class body declarations [JLS:8.1.6]."
    :long
    (xdoc::topstring
     (xdoc::p
      "We do not capture constructor declarations."))
    (:member ((get jcmember)))
    (:init ((get jcinitializer)))
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deflist jcbody-element-list
    :short "True lists of Java class body declarations."
    :elt-type jcbody-element
    :true-listp t
    :elementp-of-nil nil
    :pred jcbody-element-listp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::defprod jclass
    :short "Java class declarations [JLS:8.1]."
    :long
    (xdoc::topstring
     (xdoc::p
      "We only capture normal class declarations, not enum ones.")
     (xdoc::p
      "We do not capture instance initializers,
       static initializers,
       and constructor declarations."))
    ((access jaccess)
     (abstract? bool)
     (static? bool)
     (final? bool)
     (strictfp? bool)
     (name string)
     (superclass? maybe-string)
     (superinterfaces string-list)
     (body jcbody-element-list))
    :pred jclassp
    ;; 2nd component of measure is non-0 so that field BODY,
    ;; whose measure's 2nd component is 0, always decreases:
    :measure (two-nats-measure (acl2-count x) 1)))

(fty::deflist jclass-list
  :short "True lists of Java class declarations."
  :elt-type jclass
  :true-listp t
  :elementp-of-nil nil
  :pred jclass-listp)

(define jfields-to-jcbody-elements ((fields jfield-listp))
  :returns (cbody-elements jcbody-element-listp)
  :short "Lift the composition of @(tsee jcmember-field)
          followed by @(tsee jcbody-element-member) to lists."
  (cond ((endp fields) nil)
        (t (cons (jcbody-element-member (jcmember-field (car fields)))
                 (jfields-to-jcbody-elements (cdr fields))))))

(define jmethods-to-jcbody-elements ((methods jmethod-listp))
  :returns (cbody-elements jcbody-element-listp)
  :short "Lift the composition of @(tsee jcmember-method)
          followed by @(tsee jcbody-element-member) to lists."
  (cond ((endp methods) nil)
        (t (cons (jcbody-element-member (jcmember-method (car methods)))
                 (jmethods-to-jcbody-elements (cdr methods))))))

(define jclasses-to-jcbody-elements ((classes jclass-listp))
  :returns (cbody-elements jcbody-element-listp)
  :short "Lift the composition of @(tsee jcmember-class)
          followed by @(tsee jcbody-element-member) to lists."
  (cond ((endp classes) nil)
        (t (cons (jcbody-element-member (jcmember-class (car classes)))
                 (jclasses-to-jcbody-elements (cdr classes))))))

(fty::defprod jimport
  :short "Java import declarations [JLS:7.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We capture import declarations via
     a flag saying whether the import is static or not
     and a string for the name of the imported entity.
     The string may end with a dot and a star,
     in which case it captures an on-demand import."))
  ((static? bool)
   (target stringp))
  :pred jimportp)

(fty::deflist jimport-list
  :short "True lists of Java import declarations."
  :elt-type jimport
  :true-listp t
  :elementp-of-nil nil
  :pred jimport-listp)

(fty::defprod jcunit
  :short "Java compilation units [JLS:7.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only capture ordinary compilation units, not modular ones.
     Thus, we do not capture module declarations either.")
   (xdoc::p
    "We capture the package declaration [JLS:7.4]
     as an ACL2 string for the name.
     This declaration is optional.")
   (xdoc::p
    "We do not capture interfaces, so a type declaration [JLS:7.6]
     is always a class declaration."))
  ((package? maybe-string)
   (imports jimport-list)
   (types jclass-list))
  :pred jcunitp)
