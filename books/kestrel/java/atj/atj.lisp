; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "input-processing")
(include-book "code-generation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-implementation
  :parents (atj)
  :short "Implementation of @(tsee atj)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The implementation functions have formal parameters
     consistently named as follows:")
   (xdoc::ul
    (xdoc::li
     "@('state') is the ACL2 @(see state).")
    (xdoc::li
     "@('ctx') is the context used for errors.")
    (xdoc::li
     "@('args') is the list of all the inputs to @(tsee atj),
      before being processed.
      The type of this formal parameter is just @(tsee true-listp)
      because its elements may be any values.")
    (xdoc::li
     "@('targets') is the list @('(fn1 ... fnp)') of inputs to @(tsee atj),
      before being processed.
      The type of this formal parameter is just @(tsee true-listp)
      because its elements may be any values.")
    (xdoc::li
     "@('targets$') is the result of processing @('targets').
      It is identical to @('targets'),
      but has a type implied by its successful validation,
      performed when it is processed.")
    (xdoc::li
     "@('deep'),
      @('guards'),
      @('java-package'),
      @('java-class'),
      @('output-dir'),
      @('tests'), and
      @('verbose')
      are the homonymous inputs to @(tsee atj),
      before being processed.
      These formal parameters have no types because they may be any values.")
    (xdoc::li
     "@('deep$'),
      @('guards$'),
      @('java-package$'),
      @('java-class$'),
      @('tests$'), and
      @('verbose$')
      are the results of processing
      the homonymous inputs (without the @('$')) to @(tsee atj).
      Some are identical to the corresponding inputs,
      but they have types implied by their successful validation,
      performed when they are processed.")
    (xdoc::li
     "@('output-file$') and @('output-file-test$')
      are the results of processing @('output-dir').")
    (xdoc::li
     "@('test$') is an element of @('tests$').")
    (xdoc::li
     "@('pkgs') is the list of names of all the currently known ACL2 packages,
      in chronological order.")
    (xdoc::li
     "@('fns-to-translate') is the list of ACL2 functions
      to be translated to Java.")
    (xdoc::li
     "@('fns-by-pkg') consists of @('fns-to-translate'),
      plus all the ACL2 functions natively implemented in AIJ
      (which currently are the ACL2 primitive functions)
      organized as an alist from ACL2 package names to
      the non-empty lists of the functions in the respective packages.
      See @(tsee atj-code-generation).")
    (xdoc::li
     "@('avars-by-name') consists of all the free and bound variables
      that appear in the ACL2 function definition
      for which code is being generated.
      These variables are organized as an alist from symbol names
      to the variables with the respective names.
      See @(tsee atj-code-generation).")
    (xdoc::li
     "@('jvar-value-base'),
      @('jvar-term-base'), and
      @('jvar-lambda-base')
      are the base names of the Java local variables to use
      to construct ACL2 values,
      deeply embedded ACL2 terms,
      and deeply embedded ACL2 lambda expressions.
      See @(tsee atj-code-generation).")
    (xdoc::li
     "@('jvar-result-base') is the base name of the Java local variable to use
      to store the results of arguments of non-strict ACL2 functions.")
    (xdoc::li
     "@('jvar-value-index'),
      @('jvar-term-index'), and
      @('jvar-lambda-index')
      are the indices of the next Java local variables to use
      to construct ACL2 values,
      deeply embedded ACL2 terms,
      and deeply embedded ACL2 lambda expressions.
      See @(tsee atj-code-generation).")
    (xdoc::li
     "@('jvar-result-index') is the index of the next Java local variable to use
      to store the results of arguments of non-strict ACL2 functions.")
    (xdoc::li
     "@('indices') is an alist from symbols to positive integers,
      which associates to each ACL2 variable the next index to use
      to disambiguate a new instance of that variable from previous instances.
      This is used when renaming ACL2 variables to their Java names,
      in the shallow embedding approach.
      See @(tsee atj-code-generation).")
    (xdoc::li
     "@('renaming-new') and @('renaming-old')
      are alists from symbols to symbols,
      which associate to each ACL2 variable its Java name
      (i.e. the name of the Java variable generated from this ACL2 variable).
      The former is used for the variables marked as `new',
      while the latter is used for the variables marked as `old'.
      This is used when renaming ACL2 variables to their Java names,
      in the shallow embedding approach.
      See @(tsee atj-code-generation).")
    (xdoc::li
     "@('pkg-class-names') is an alist from strings to strings,
      which associates to each package name in the keys of @('fns-by-pkg')
      the name of the corresponding Java class name.
      This is used in the shallow embedding approach.
      See @(tsee atj-code-generation).")
    (xdoc::li
     "@('fn-method-names') is an alist from strings to strings,
      which associates to each function name in @('fns-to-translate')
      the name of the corresponding Java method name.
      This is used in the shallow embedding approach.
      See @(tsee atj-code-generation).")
    (xdoc::li
     "@('mv-class-names') is a list of strings consisting of
      the names of all the generated @(tsee mv) classes.
      This is used in the shallow embedding approach.
      See @(tsee atj-code-generation).")
    (xdoc::li
     "@('curr-pkg') is the name of the ACL2 package of the ACL2 function
      for which Java code is being generated."))
   (xdoc::p
    "The parameters of implementation functions that are not listed above
     are described in, or clear from, those functions' documentation."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-fn ((args true-listp) ctx state)
  :returns (mv erp
               (result "Always @('(value-triple :invisible)').")
               state)
  :mode :program ; because of ATJ-PROCESS-INPUTS and ATJ-GEN-EVERYTHING
  :parents (atj-implementation)
  :short "Process the inputs and generate the Java file(s)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the result of this function is passed to @(tsee make-event),
     this function must return an event form.
     By returning @('(value-triple :invisible)'),
     no return value is printed on the screen.
     A message of successful completion is printed,
     regardless of @(':verbose')."))
  (b* (((er (list fns-to-translate
                  call-graph
                  pkgs
                  deep$
                  guards$
                  java-package$
                  java-class
                  output-file$
                  output-file-env$
                  output-file-test$
                  tests$
                  verbose$))
        (atj-process-inputs args ctx state))
       ((er &) (atj-gen-everything deep$
                                   guards$
                                   java-package$
                                   java-class
                                   output-file$
                                   output-file-env$
                                   output-file-test$
                                   tests$
                                   pkgs
                                   fns-to-translate
                                   call-graph
                                   verbose$
                                   state))
       (- (if output-file-test$
              (cw "~%Generated Java files:~% ~s0~% ~s1~% ~s2~%"
                  output-file$ output-file-env$ output-file-test$)
            (cw "~%Generated Java files:~% ~s0~% ~s1~%"
                output-file$ output-file-env$))))
    (value '(value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atj-macro-definition
  :parents (atj-implementation)
  :short "Definition of the @(tsee atj) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "We suppress the extra output produced by @(tsee make-event)
     via @(tsee with-output) and @('(:on-behalf-of :quiet)').")
   (xdoc::@def "atj"))
  (defmacro atj (&rest args)
    `(with-output :off :all :on error
       (make-event
        (atj-fn ',args 'atj state)
        :on-behalf-of :quiet))))
