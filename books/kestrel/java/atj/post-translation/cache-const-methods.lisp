; Java Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "../java-syntax-operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-post-translation-cache-const-methods
  :parents (atj-post-translation)
  :short "Post-translation step:
          cache constant methods in static final fields."
  :long
  (xdoc::topstring
   (xdoc::p
    "If a generated Java method is nullary (i.e. it has no parameters),
     it always returns the same value.
     Recall that the Java method represents an ACL2 function,
     and that we translate ACL2 functions to methods with the same arity.
     (This may no longer be the case in the future,
     if we introduce a way to generate Java code
     that accesses non-constant fields,
     but for now that is not supported.)
     Thus, we can improve efficiency by
     caching that value into a static final field that the method returns.
     If the method is never called, this actually decreases efficiency,
     because the value has to be calculated at class initialization time.
     However, if the method is called once,
     then the performance should be about the same,
     while if the method is called multiple times,
     the performance should be better.
     Note also that a JIT would presumably inline the method call.")
   (xdoc::p
    "We achieve this optimization
     (it generally is an optimization, but see above for a discussion)
     as a post-translation step that operates as follows.
     For a nullary method whose body cosists of
     just a return statement whose expression has no method calls,
     we add a static final field initialized with the return expression,
     and we replace the return expression in the method
     with a reference to the new static final field.
     Java allows a field and a method to have the same name [JLS:8.2],
     but discourages that as a matter of style;
     since our Java code is generated,
     it seems acceptable to violate that stylistic guide in favor of simplicity,
     but we may revisit this decision in the future.")
   (xdoc::p
    "The restriction that the body of the method is a single return expression
     makes it possible to move that expression into the field declaration,
     which needs an expression as an initializer, and cannot take a block.
     (This restriction could be lifted via a more complex code transformation,
     which is a possible future extension.)")
   (xdoc::p
    "The restriction that the return expression calls no method
     avoids class initialization issues.
     According to [JLS:12.4.1], a class's
     static initializer(s) (if any) and static final fields (if any)
     are initialized (i.e. executed) in textual order.
     If the initializer of a static final field contained a method call,
     that method call could require the initialization of
     a static final field that comes later in a class,
     causing a compilation error.
     (This restriction could be lifted via a more complex code transformation,
     which is a possible future extension.)")
   (xdoc::p
    "While other post-translation steps operate on individual method bodies,
     this post-translation step operates on a class level.
     It is applied to all the nested classes in the main Java class:
     it is the nested classes that contain the methods to be optimized."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-cache-const-methods ((elems jcbody-element-listp))
  :returns (new-elems jcbody-element-listp)
  :short "Cache constant methods in static final fields,
          in a list of Java class body declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "We leave member fields, member classes, and static initializers unchanged.
     If a member method satisfies the conditions
     described in @(see atj-post-translation-cache-const-methods),
     we replace it with a field and a modified method as also explained there.
     Otherwise, we leave the method unchanged."))
  (b* (((when (endp elems)) nil)
       (elem (car elems))
       ((when (jcbody-element-case elem :init))
        (cons (jcbody-element-fix elem)
              (atj-cache-const-methods (cdr elems))))
       (memb (jcbody-element-member->get elem))
       ((when (or (jcmember-case memb :field)
                  (jcmember-case memb :class)))
        (cons (jcbody-element-fix elem)
              (atj-cache-const-methods (cdr elems))))
       (meth (jcmember-method->get memb))
       ((when (consp (jmethod->params meth)))
        (cons (jcbody-element-fix elem)
              (atj-cache-const-methods (cdr elems))))
       (body (jmethod->body meth))
       ((unless (= (len body) 1))
        (cons (jcbody-element-fix elem)
              (atj-cache-const-methods (cdr elems))))
       (stmt (car body))
       ((unless (jstatem-case stmt :return))
        (cons (jcbody-element-fix elem)
              (atj-cache-const-methods (cdr elems))))
       (expr (jstatem-return->expr? stmt))
       ((unless expr)
        (raise "Internal error: method ~x0 returns nothing." meth))
       ((when (consp (jexpr-methods expr)))
        (cons (jcbody-element-fix elem)
              (atj-cache-const-methods (cdr elems))))
       (result (jmethod->result meth))
       ((when (jresult-case result :void))
        (raise "Internal error: method ~x0 returns void." meth))
       (type (jresult-type->get result))
       (name (jmethod->name meth))
       (fld (make-jfield :access (jaccess-private)
                         :static? t
                         :final? t
                         :transient? nil
                         :volatile? nil
                         :type type
                         :name name
                         :init? expr))
       (meth (change-jmethod
              meth
              :body (list (jstatem-return (jexpr-name name))))))
    (list* (jcbody-element-member (jcmember-field fld))
           (jcbody-element-member (jcmember-method meth))
           (atj-cache-const-methods (cdr elems)))))
