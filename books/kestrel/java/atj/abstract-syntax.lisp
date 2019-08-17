; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-abstract-syntax
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
     "We use ACL2 strings to capture Java strings,
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

(define string-list-fix ((x string-listp))
  :returns (fixed-x string-listp)
  :short "Fixer for @(tsee string-listp)."
  :long
  (xdoc::topstring-p
   "This is not specific to Java,
    and it should be moved to a more general library eventually.")
  (mbe :logic (if (string-listp x) x nil)
       :exec x)
  ///
  (defrule string-list-fix-when-string-listp
    (implies (string-listp x)
             (equal (string-list-fix x)
                    x))))

(defsection string-list
  :short "Fixtype of true lists of ACL2 strings."
  :long
  (xdoc::topstring-p
   "This is not specific to Java,
    and it should be moved to a more general library eventually.")
  (fty::deffixtype string-list
    :pred string-listp
    :fix string-list-fix
    :equiv string-list-equiv
    :define t
    :forward t))

(defsection maybe-string
  :short "ACL2 strings and @('nil')."
  :long
  (xdoc::topstring-p
   "This is not specific to Java,
    and it should be moved to a more general library eventually.")

  (define maybe-string-fix ((x maybe-stringp))
    :returns (fixed-x maybe-stringp)
    (mbe :logic (if (maybe-stringp x) x nil)
         :exec x)
    ///
    (defrule maybe-string-fix-when-maybe-stringp
      (implies (maybe-stringp x)
               (equal (maybe-string-fix x)
                      x))))

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
    "We only need integer, boolean, string, and null literals for now,
     as well as a limited form of floating-point literals (see below).
     We do not need character literals yet.")
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
  (:string ((value string)))
  (:null ())
  :pred jliteralp)

(fty::deflist jliteral-list
  :elt-type jliteral
  :true-listp t
  :elementp-of-nil nil
  :pred jliteral-listp)

(fty::deftagsum jtype
  :short "Java types [JLS:4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We capture all eight primitive types because it is easy to do that,
     even though for now we only need some of them.")
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
  (:boolean ())
  (:char ())
  (:byte ())
  (:short ())
  (:int ())
  (:long ())
  (:float ())
  (:double ())
  (:class ((name string)))
  (:array ((comp jtype)))
  :pred jtypep)

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
  (:instanceof ())
  (:eq ()) ; ==
  (:ne ()) ; !=
  (:bitand ()) ; &
  (:bitxor ()) ; ^
  (:bitior ()) ; |
  (:logand ()) ; &&
  (:logor ()) ; ||
  (:asg ()) ; =
  (:asg-mul ()) ; *=
  (:asg-div ()) ; /=
  (:asg-rem ()) ; %=
  (:asg-add ()) ; +=
  (:asg-sub ()) ; -=
  (:asg-shl ()) ; <<=
  (:asg-sshr ()) ; >>=
  (:asg-ushr ()) ; >>>=
  (:asg-bitand ()) ; &=
  (:asg-bitxor ()) ; ^=
  (:asg-bitior ()) ; |=
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
    "For name expressions [JLS:6.5], we use ACL2 strings,
     which allow dot-separated identifiers,
     as well as @('this') and @('super').")
   (xdoc::p
    "We only capture array creation expressions
     with one (implicit) dimension
     and whith an array initializer that is a sequence of expressions.
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
     However, having parenthesized expressions in the abstract syntax
     makes the implementation of the pretty-printer easier
     while allowing to maintain the generated code more readable.
     Parenthesized expressions may be removed from the abstract syntax
     if the pretty-printer is improved
     to generate just the minimum amount of parentheses
     based on Java operator precedence rules."))

  (fty::deftagsum jexpr
    (:literal ((get jliteral)))
    (:name ((get string)))
    (:newarray ((type jtype) (init jexpr-list)))
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

(fty::defprod jlocvar
  :short "Local variable declarations [JLS:14.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only capture declarations of single local variables,
     with an initializer,
     and without array square brackets after the name
     (i.e. all the array square brackets are in the type).")
   (xdoc::p
    "We do not capture @('var')."))
  ((final? bool)
   (type jtype)
   (name string)
   (init jexpr))
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
     @('break'),
     @('continue'),
     @('while'),
     @('do'),
     @('synchronized'), and
     @('try').")
   (xdoc::p
    "We only capture @('if')
     whose @('then') (and @('else'), if present) parts are blocks."))

  (fty::deftagsum jstatem
    (:locvar ((get jlocvar)))
    (:expr ((get jexpr)))
    (:return ((expr? maybe-jexpr)))
    (:throw ((expr jexpr)))
    (:if ((test jexpr) (then jblock)))
    (:ifelse ((test jexpr) (then jblock) (else jblock)))
    :pred jstatemp)

  (fty::deflist jblock
    :elt-type jstatem
    :true-listp t
    :elementp-of-nil nil
    :pred jblockp))

(define jblock-locvar ((type jtypep) (name stringp) (init jexprp))
  :returns (jblock jblockp)
  :short "Build a block consisting of
          a single (non-final) local variable declaration statement."
  (list (jstatem-locvar
         (make-jlocvar :final? nil :type type :name name :init init))))

(define jblock-locvar-final ((type jtypep) (name stringp) (init jexprp))
  :returns (jblock jblockp)
  :short "Build a block consisting of
          a single final local variable declaration statement."
  (list (jstatem-locvar
         (make-jlocvar :final? t :type type :name name :init init))))

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
     with a literal as initializer,
     and without array square brackets after the name
     (i.e. all the array square brackets are in the type)."))
  ((access jaccess)
   (static? bool)
   (final? bool)
   (transient? bool)
   (volatile? bool)
   (type jtype)
   (name string)
   (init jliteral))
  :pred jfieldp)

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
  :elt-type jparam
  :true-listp t
  :elementp-of-nil nil
  :pred jparam-listp)

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

  (fty::deflist jcmember-list
    :elt-type jcmember
    :true-listp t
    :elementp-of-nil nil
    :pred jcmember-listp
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
     (body jcmember-list))
    :pred jclassp
    :measure (two-nats-measure (acl2-count x) 1)))

(fty::deflist jclass-list
  :elt-type jclass
  :true-listp t
  :elementp-of-nil nil
  :pred jclass-listp)

(define jmethods-to-jcmembers ((jmethods jmethod-listp))
  :returns (jcmembers jcmember-listp)
  :short "Lift @(tsee jcmember-method) to lists."
  (cond ((endp jmethods) nil)
        (t (cons (jcmember-method (car jmethods))
                 (jmethods-to-jcmembers (cdr jmethods))))))

(define jclasses-to-jcmembers ((jclasses jclass-listp))
  :returns (jcmembers jcmember-listp)
  :short "Lift @(tsee jcmember-class) to lists."
  (cond ((endp jclasses) nil)
        (t (cons (jcmember-class (car jclasses))
                 (jclasses-to-jcmembers (cdr jclasses))))))

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
    "We capture the import declarations [JLS:7.5]
     as a list of ACL2 strings for the names of the imported entities,
     possibly including the on-demand notation
     (in the latter case, the string ends with dot and star).
     We do not capture static import declarations.")
   (xdoc::p
    "We do not capture interfaces, so a type declaration [JLS:7.6]
     is always a class declaration."))
  ((package? maybe-string)
   (imports string-list)
   (types jclass-list))
  :pred jcunitp)
