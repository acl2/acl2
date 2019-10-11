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

(include-book "kestrel/std/system/pseudo-termfnp" :dir :system)
(include-book "kestrel/std/system/ubody" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-deep-code-generation
  :parents (atj-code-generation)
  :short "Code generation that is specific to the deep embedding approach."
  :order-subtopics t
  :default-parent t)

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

  :hints (("Goal" :in-theory (enable len))) ; for termination

  :prepwork ((local (in-theory (disable posp len)))) ; for :RETURNS

  :verify-guards nil ; done below
  ///
  (verify-guards atj-gen-deep-term
    :hints (("Goal" :in-theory (enable pseudo-termfnp acl2::pseudo-lambdap)))))

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
