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
(include-book "../array-write-method-names")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-post-translation-remove-array-write-calls
  :parents (atj-post-translation)
  :short "Post-translation step:
          remove calls of the array writing methods."
  :long
  (xdoc::topstring
   (xdoc::p
    "ATJ's ACL2-to-Java translation
     turns calls of the ACL2 functions that model array writes
     into calls of corresponding Java methods that make destructive writes.
     This keeps the translation simple,
     also because the array writing methods return the (modified) array,
     thus maintaining a functional programming style.")
   (xdoc::p
    "However, in idiomatic Java, an array write should be an assignment,
     whose returned value is normally discarded
     by turning the assignment into a statement via an ending semicolon.
     The goal of this post-translation step is to suitably replace
     calls of the array writing methods (along with some surrounding code)
     into assignment expression statements.
     This is essentially ``inlining'' these method calls.")
   (xdoc::p
    "For now we make the following transformations
    in this post-translation step:")
   (xdoc::ul
    (xdoc::li
     (xdoc::p
      "We turn assignment expression statements of the form")
     (xdoc::codeblock
      "a = <array-write-method>(a, i, x);")
     (xdoc::p
      "into assignment expressions statements of the form")
     (xdoc::codeblock
      "a[i] = x;")
     (xdoc::p
      "ATJ's ACL2-to-Java translation produces statements of the first kind,
       when translating terms of the form")
     (xdoc::codeblock
      "(let (... (a (<array-write-function> a i x)) ...) ...)")
     (xdoc::p
      "Since the array writing method makes the assignment,
       the second kind of assignment is equivalent to the first one.
       The first one just ends up assigning (the modified) a to itself.
       Here `modified' refers to the content of the array,
       not the immutable reference that is actually in @('a').")
     (xdoc::p
      "Because of the single-threaded array analysis,
       the Java variable @('a') on the left-hand side
       should be the same as the first argument of the method call
       (when this is a variable at all),
       because the single-threadedness should ensure that
       array variables can be reused."))
    (xdoc::li
     (xdoc::p
      "We turn return statements of the form")
     (xdoc::codeblock
      "return <array-write-method>(a, i, x);")
     (xdoc::p
      "(where @('a') is a variable) into two-statement blocks of the form")
     (xdoc::codeblock
      "a[i] = x;"
      "return a;")
     (xdoc::p
      "ATJ's ACL2-to-Java translation produces statements of the first kind,
       when a function ends its execution
       with a call of the form @('(<array-write-function> a i x)').
       The array write method destructively updates the array and returns it.
       Thus, we can ``inline'' the method call here.")))
   (xdoc::p
    "The two cases above are not
     the only kind of occurrences of the array writing methods
     in the Java code produced by ATJ's ACL2-to-Java translation.
     Other kinds of occurrences will be handled in the future."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-primarray-write-method-names*
  :short "List of names of the methods to write to Java primitive arrays."
  (list (atj-primarray-write-method-name (primitive-type-boolean))
        (atj-primarray-write-method-name (primitive-type-char))
        (atj-primarray-write-method-name (primitive-type-byte))
        (atj-primarray-write-method-name (primitive-type-short))
        (atj-primarray-write-method-name (primitive-type-int))
        (atj-primarray-write-method-name (primitive-type-long))
        (atj-primarray-write-method-name (primitive-type-float))
        (atj-primarray-write-method-name (primitive-type-double))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-remove-array-write-call-in-asg ((expr jexprp))
  :returns (new-expr jexprp)
  :short "Replace an assignment of an array write method call
          with the corresponding assignment to the array component."
  :long
  (xdoc::topstring
   (xdoc::p
    "This performs the first transformation described in
     @(see atj-post-translation-remove-array-write-calls).")
   (xdoc::p
    "This is called on the top-level expression of an expression statement,
     i.e. an expression that is terminated by a semicolon.
     If the expression fits the pattern to transform, we transform it.
     Otherwise, we leave it unchanged.")
   (xdoc::p
    "The expression must be a simple assignment,
     whose left-hand-side is an expression name
     and whose right-hand side is a call of one of the array write methods.
     Furthermore, the first argument of the method call
     must be the same as the left-hand side expression.
     In Java code produced by ATJ's ACL2-to-Java translation,
     the expression name should always be an identifier,
     of a method parameter or of a local variable.")
   (xdoc::p
    "Note that we use the @(':method') case of expressions,
     which matches the one generated by
     @(tsee atj-gen-shallow-jprimarr-write-call)."))
  (b* (((unless (jexpr-case expr :binary)) (jexpr-fix expr))
       (op (jexpr-binary->op expr))
       ((unless (jbinop-case op :asg)) (jexpr-fix expr))
       (left (jexpr-binary->left expr))
       ((unless (jexpr-case left :name)) (jexpr-fix expr))
       (right (jexpr-binary->right expr))
       ((unless (jexpr-case right :method)) (jexpr-fix expr))
       (method-name (jexpr-method->name right))
       ((unless (member-equal method-name *atj-primarray-write-method-names*))
        (jexpr-fix expr))
       (args (jexpr-method->args right))
       ((unless (= (len args) 3))
        (prog2$ (raise "Internal error: ~
                        the call ~x0 of an array write method ~
                        has the wrong number of arguments."
                       right)
                (ec-call (jexpr-fix :irrelevant))))
       (array (first args))
       ((unless (equal array left))
        (prog2$ (raise "Internal error: ~
                        the assignment ~x0 uses different arrays."
                       expr)
                (ec-call (jexpr-fix :irrelevant))))
       (index (second args))
       (component (third args)))
    (jexpr-binary (jbinop-asg)
                  (jexpr-array array index)
                  component))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-remove-array-write-call-asgs-in-jstatems+jblocks
  :short "Replace assignments of array write method calls
          with the corresponding assignments to the array components."
  :long
  (xdoc::topstring
   (xdoc::p
    "We apply @(tsee atj-remove-array-write-call-in-asg)
     to all the top-level expressions in expression statements."))

  (define atj-remove-array-write-call-asgs-in-jstatem ((statem jstatemp))
    :returns (new-statem jstatemp)
    (jstatem-case
     statem
     :locvar (jstatem-fix statem)
     :expr (jstatem-expr (atj-remove-array-write-call-in-asg statem.get))
     :return (jstatem-fix statem)
     :throw (jstatem-fix statem)
     :break (jstatem-fix statem)
     :continue (jstatem-fix statem)
     :if (jstatem-if statem.test
                     (atj-remove-array-write-call-asgs-in-jblock statem.then))
     :ifelse (jstatem-ifelse
              statem.test
              (atj-remove-array-write-call-asgs-in-jblock statem.then)
              (atj-remove-array-write-call-asgs-in-jblock statem.else))
     :while (jstatem-while statem.test
                           (atj-remove-array-write-call-asgs-in-jblock
                            statem.body))
     :do (jstatem-do (atj-remove-array-write-call-asgs-in-jblock statem.body)
                     statem.test)
     :for (jstatem-for statem.init
                       statem.test
                       statem.update
                       (atj-remove-array-write-call-asgs-in-jblock
                        statem.body)))
    :measure (jstatem-count statem))

  (define atj-remove-array-write-call-asgs-in-jblock ((block jblockp))
    :returns (new-block jblockp)
    (cond ((endp block) nil)
          (t (cons (atj-remove-array-write-call-asgs-in-jstatem (car block))
                   (atj-remove-array-write-call-asgs-in-jblock (cdr block)))))
    :measure (jblock-count block))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-remove-array-write-call-asgs-in-jstatem)

  (fty::deffixequiv-mutual
    atj-remove-array-write-call-asgs-in-jstatems+jblocks))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-remove-array-write-call-return ((statem jstatemp))
  :returns (block jblockp)
  :short "Replace a return statement of an array write method call
          with an assignment to the array component
          followed by a return statement of the updated array."
  :long
  (xdoc::topstring
   (xdoc::p
    "This performs the second transformation described in
     @(see atj-post-translation-remove-array-write-calls).")
   (xdoc::p
    "This function turns a single statement
     into a block of one or two statements.
     If there is no actual transformation,
     the output block is a singleton containing the input statement.
     If there is a transformation,
     the output block consists of two statements."))
  (b* ((no-change (list (jstatem-fix statem)))
       ((unless (jstatem-case statem :return)) no-change)
       (expr? (jstatem-return->expr? statem))
       ((unless expr?) no-change)
       (expr expr?)
       ((unless (jexpr-case expr :method)) no-change)
       (method-name (jexpr-method->name expr))
       ((unless (member-equal method-name *atj-primarray-write-method-names*))
        no-change)
       (args (jexpr-method->args expr))
       ((unless (= (len args) 3))
        (prog2$ (raise "Internal error: ~
                        the call ~x0 of an array write method ~
                        has the wrong number of arguments."
                       expr)
                no-change))
       (array (first args))
       ((unless (jexpr-case array :name)) no-change)
       (index (second args))
       (component (third args)))
    (list (jstatem-expr (jexpr-binary (jbinop-asg)
                                      (jexpr-array array index)
                                      component))
          (jstatem-return array)))
  :hooks (:fix)
  ///

  (more-returns
   (block consp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-remove-array-write-call-returns-in-jstatems+jblocks
  :short "Replace return statements of array write method calls
          with assignments to the array components
          and return statements of the updated arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a block is empty, we return the empty block unchanged.
     When a block is a singleton,
     we use @(tsee atj-remove-array-write-call-return)
     on the (only) statement in the block and return the resulting block,
     which is either the initial block or a two-statement block
     (see @(tsee atj-remove-array-write-call-return)).
     In the first case, we recursively process the (singleton) block,
     because the statement may be an @('if'), for example.
     When a block is not a singleton,
     we recursively process its first statement and its tail block.")
   (xdoc::p
    "Processing a statement means processing the blocks inside it.
     Note that the return statements that return array write method calls
     are replaced as part of block processing (see above)."))

  (define atj-remove-array-write-call-returns-in-jstatem ((statem jstatemp))
    :returns (new-statem jstatemp)
    (jstatem-case
     statem
     :locvar (jstatem-fix statem)
     :expr (jstatem-fix statem)
     :return (jstatem-fix statem)
     :throw (jstatem-fix statem)
     :break (jstatem-fix statem)
     :continue (jstatem-fix statem)
     :if (jstatem-if statem.test
                     (atj-remove-array-write-call-returns-in-jblock
                      statem.then))
     :ifelse (jstatem-ifelse statem.test
                             (atj-remove-array-write-call-returns-in-jblock
                              statem.then)
                             (atj-remove-array-write-call-returns-in-jblock
                              statem.else))
     :while (jstatem-while statem.test
                           (atj-remove-array-write-call-returns-in-jblock
                            statem.body))
     :do (jstatem-do (atj-remove-array-write-call-returns-in-jblock
                      statem.body)
                     statem.test)
     :for (jstatem-for statem.init
                       statem.test
                       statem.update
                       (atj-remove-array-write-call-returns-in-jblock
                        statem.body)))
    :measure (jstatem-count statem))

  (define atj-remove-array-write-call-returns-in-jblock ((block jblockp))
    :returns (new-block jblockp)
    (b* (((when (endp block)) nil)
         ((when (endp (cdr block)))
          (b* ((statem (car block))
               (new-block (atj-remove-array-write-call-return statem)))
            (if (consp (cdr new-block))
                new-block
              (list (atj-remove-array-write-call-returns-in-jstatem statem))))))
      (cons (atj-remove-array-write-call-returns-in-jstatem (car block))
            (atj-remove-array-write-call-returns-in-jblock (cdr block))))
    :measure (jblock-count block))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-remove-array-write-call-returns-in-jstatem)

  (fty::deffixequiv-mutual
    atj-remove-array-write-call-returns-in-jstatems+jblocks))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-ensure-no-array-write-calls ((block jblockp))
  :returns (yes/no booleanp)
  :short "Ensure that there are no calls of array write methods in a block."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two transformations described in
     @(see atj-post-translation-remove-array-write-calls)
     should remove all the calls of array write methods.
     Since this has not been formally proved,
     we check whether this is the case, via this predicate."))
  (not (intersectp-equal (jblock-methods block)
                         *atj-primarray-write-method-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-remove-array-write-calls ((block jblockp))
  :returns (new-block jblockp)
  :short "Remove array write method calls from a block."
  :long
  (xdoc::topstring
   (xdoc::p
    "This puts together the two transformations described in
     @(see atj-post-translation-remove-array-write-calls).")
   (xdoc::p
    "We also ensure that, after the transformations,
     no more array write method calls remain."))
  (b* ((block (atj-remove-array-write-call-asgs-in-jblock block))
       (block (atj-remove-array-write-call-returns-in-jblock block))
       ((unless (atj-ensure-no-array-write-calls block))
        (raise "Internal error: ~
                the block ~x0 contains array write method calls."
               block)))
    block)
  :hooks (:fix))
