; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

; Avoid failure for atj-gen-number in ACL2(r):
; cert_param: non-acl2r

(include-book "aij-notions")
(include-book "test-structures")
(include-book "java-pretty-printer")
(include-book "pre-translation")
(include-book "post-translation")
(include-book "name-translation")
(include-book "deep-code-generation")
(include-book "shallow-code-generation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-code-generation
  :parents (atj-implementation)
  :short "Code generation performed by ATJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate Java abstract syntax,
     which we then pretty-print to files.")
   (xdoc::p
    "We translate ACL2 values, terms, and lambda expressions
     to Java expressions ``preceded by'' Java blocks.
     By this we mean that the relevant code generation functions
     generally return a Java block and a Java expression,
     such that the block must be executed before the expression.
     That is, the Java block provides the necessary code
     to ``prepare'' the evaluation of the Java expression.
     The Java block may include Java expressions and blocks
     that are recursively generated.")
   (xdoc::p
    "To illustrate this concept,
     consider the generation of a Java expression to build
     the Java representation of an ACL2 @(tsee cons) pair.
     In some circumstances,
     since the pair may be a large binary tree,
     we prefer not to generate a large Java expression.
     Instead, we generate
     a Java block that sets a local variable to the @(tsee car),
     a Java block that sets another local variable to the @(tsee cdr),
     and then a Java expression that builds the pair
     from those two variables.
     The two blocks are concatenated,
     resulting in a block and an expression
     for the @(tsee cons) pair in question.
     But the expressions assigned to the two local variables
     may in turn need to be built that way, recursively.
     This recursion ends when an atom value is reached.
     A similar strategy is used to build
     Java representations of ACL2 terms and lambda expressions,
     which have a recursive structure analogously to @(tsee cons) pairs.")
   (xdoc::p
    "As special cases, some of these code generation functions
     may return just Java expressions and no blocks,
     since they would always return empty blocks.")
   (xdoc::p
    "These code generation functions keep track
     of the next local variables to use
     via numeric indices that are threaded through the functions.
     The indices are appended to the base names for the local variables
     in order to guarantee the uniqueness of the local variables.")
   (xdoc::p
    "The @('atj-gen-deep-...') functions are used
     for the deep embedding approach.
     The @('atj-gen-shallow-...') functions are used
     for the shallow embedding approach.
     The other functions are generally used for both approaches.")
   (xdoc::p
    "The code generation process consists of "
    (xdoc::seetopic "atj-pre-translation"
                    "a pre-translation from ACL2 to ACL2")
    ", followed by a translation from ACL2 to Java,
     followed by "
    (xdoc::seetopic "atj-post-translation"
                    "a post-translation from Java to Java")
    ". The pre-translation turns the ACL2 code into a form
     that is closer to the target Java code,
     thus making the translation simpler.
     The correctness of the pre-translation can be formally proved within ACL2,
     without involving (the semantics of) Java.
     The post-translation makes some improvements directly on the Java code."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-method ((test$ atj-testp)
                             (deep$ booleanp)
                             (guards$ booleanp)
                             (java-class$ stringp)
                             (verbose$ booleanp)
                             (pkg-class-names string-string-alistp)
                             (fn-method-names symbol-string-alistp)
                             (wrld plist-worldp))
  :returns (method jmethodp)
  :short "Generate a Java method to run one of the specified tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "This is a private static method
     that prints the name of the test,
     builds the input values (zero or more) of the test,
     builds the output value(s) of the test,
     calls (the Java representation of) the function on the inupt values,
     compares the obtained result value(s) with the output value(s) of the test,
     and prints a message of success or failure.
     It also sets the failures field to true if the test fails.")
   (xdoc::p
    "This method also measures the time of the Java call,
     by taking the current time just before and just after the call,
     and subtracting them.
     It does that for the number of repetitions
     specified by the integer argument of the method.
     It stores the times of each call in an array,
     and calculates the minimum, maximum, and sum of all the times.
     At the end, it prints all the times,
     along with minimum, maximum, and average
     (where the average is obtained from the sum).
     To prevent unwanted JIT optimizations,
     a boolean flag is used to cumulatively check that
     all the repeated calls succeed
     (in the sense of computing the same result as ACL2);
     since the code is deterministic,
     we expect that either they will all succeed or they will all fail.")
   (xdoc::p
    "As a special case, if the integer parameter of the method is 0,
     times are not collected,
     no minimum/maximum/sum is calculated,
     and no time information is printed.
     We use a @('do') loop to ensure that at least one call is made,
     even when the parameter is 0.
     The two values are subtracted, and the time printed.
     The reason for storing the argument values into local variables
     in the shallow embedding approach,
     as opposed to passing the expressions directly to the method call,
     is to accurately measure just the time of the call,
     without the time needed to compute the argument expressions.")
   (xdoc::p
    "The code is slightly different based on whether
     we are using the deep or shallow embedding approach.
     The differences are factored into the functions
     @(tsee atj-gen-deep-test-code) and @(tsee atj-gen-shallow-test-code).")
   (xdoc::p
    "Examining any generated instance of this method
     should make the above documentation,
     and the implementation of this code generation function,
     much clearer."))
  (b* (((atj-test test) test$)
       ((unless (consp test.outputs))
        (prog2$ (raise "Internal error: the test ~x0 has no outputs." test$)
                (ec-call (jmethod-fix :irrelevant))))
       ((run-when verbose$)
        (cw "  ~s0~%" test.name))
       (method-name (atj-gen-test-method-name test.name))
       (comp-var "resultsMatch")
       ((mv arg-block
            ares-block
            call-block
            jres-block
            comp-block)
        (if deep$
            (atj-gen-deep-test-code test.function
                                    test.inputs
                                    test.outputs
                                    comp-var
                                    java-class$)
          (atj-gen-shallow-test-code test.function
                                     test.inputs
                                     test.outputs
                                     comp-var
                                     guards$
                                     java-class$
                                     pkg-class-names
                                     fn-method-names
                                     wrld)))
       (current-time-expr (jexpr-smethod (jtype-class "System")
                                         "currentTimeMillis"
                                         nil))
       (n!=0-expr (jexpr-binary (jbinop-ne)
                                (jexpr-name "n")
                                (jexpr-literal-0)))
       (method-body
        (append
         (jblock-imethod (jexpr-name "System.out")
                         "print"
                         (list (atj-gen-jstring
                                (str::cat "Testing '" test.name "'..."))))
         arg-block
         ares-block
         (jblock-locvar (jtype-boolean) "pass" (jexpr-literal-true))
         (jblock-locvar (jtype-array (jtype-long))
                        "times"
                        (jexpr-cond n!=0-expr
                                    (jexpr-newarray (jtype-long)
                                                    (jexpr-name "n"))
                                    (jexpr-literal-null)))
         (jblock-locvar (jtype-long) "minTime" (jexpr-literal-0))
         (jblock-locvar (jtype-long) "maxTime" (jexpr-literal-0))
         (jblock-locvar (jtype-long) "sumTime" (jexpr-literal-0))
         (jblock-locvar (jtype-int) "i" (jexpr-literal-0))
         (jblock-do
          ;; body of do loop:
          (append
           (jblock-locvar (jtype-long) "startTime" current-time-expr)
           call-block
           (jblock-locvar (jtype-long) "endTime" current-time-expr)
           jres-block
           comp-block
           (jblock-asg (jexpr-name "pass")
                       (jexpr-binary (jbinop-condand)
                                     (jexpr-name "pass")
                                     (jexpr-name comp-var)))
           (jblock-if n!=0-expr
                      (append
                       (jblock-locvar (jtype-long)
                                      "time"
                                      (jexpr-binary (jbinop-sub)
                                                    (jexpr-name "endTime")
                                                    (jexpr-name "startTime")))
                       (jblock-asg (jexpr-array (jexpr-name "times")
                                                (jexpr-name "i"))
                                   (jexpr-name "time"))
                       (jblock-asg (jexpr-name "sumTime")
                                   (jexpr-binary (jbinop-add)
                                                 (jexpr-name "sumTime")
                                                 (jexpr-name "time")))
                       (jblock-if (jexpr-binary (jbinop-condor)
                                                (jexpr-binary (jbinop-eq)
                                                              (jexpr-name "i")
                                                              (jexpr-literal-0))
                                                (jexpr-binary (jbinop-lt)
                                                              (jexpr-name
                                                               "time")
                                                              (jexpr-name
                                                               "minTime")))
                                  (jblock-asg (jexpr-name "minTime")
                                              (jexpr-name "time")))
                       (jblock-if (jexpr-binary (jbinop-gt)
                                                (jexpr-name "time")
                                                (jexpr-name "maxTime"))
                                  (jblock-asg (jexpr-name "maxTime")
                                              (jexpr-name "time")))))
           (jblock-expr (jexpr-unary (junop-preinc) (jexpr-name "i"))))
          ;; test of do loop:
          (jexpr-binary (jbinop-lt) (jexpr-name "i") (jexpr-name "n")))
         (jblock-ifelse (jexpr-name "pass")
                        (jblock-imethod (jexpr-name "System.out")
                                        "println"
                                        (list (atj-gen-jstring " PASS")))
                        (append
                         (jblock-imethod (jexpr-name "System.out")
                                         "println"
                                         (list (atj-gen-jstring " FAIL")))
                         (jblock-asg-name "failures"
                                          (jexpr-literal-true))))
         (jblock-if n!=0-expr
                    (append
                     (jblock-imethod (jexpr-name "System.out")
                                     "println"
                                     (list (jexpr-literal-string "  Times:")))
                     (jblock-for (jexpr-binary (jbinop-asg)
                                               (jexpr-name "i")
                                               (jexpr-literal-0))
                                 (jexpr-binary (jbinop-lt)
                                               (jexpr-name "i")
                                               (jexpr-name "n"))
                                 (jexpr-unary (junop-preinc)
                                              (jexpr-name "i"))
                                 (jblock-imethod
                                  (jexpr-name "System.out")
                                  "format"
                                  (list (jexpr-literal-string "    %.3f%n")
                                        (jexpr-binary (jbinop-div)
                                                      (jexpr-array
                                                       (jexpr-name "times")
                                                       (jexpr-name "i"))
                                                      (jexpr-literal-floating
                                                       1000)))))
                     (jblock-imethod
                      (jexpr-name "System.out")
                      "format"
                      (list (jexpr-literal-string "  Minimum: %.3f%n")
                            (jexpr-binary (jbinop-div)
                                          (jexpr-name "minTime")
                                          (jexpr-literal-floating 1000))))
                     (jblock-imethod
                      (jexpr-name "System.out")
                      "format"
                      (list (jexpr-literal-string "  Average: %.3f%n")
                            (jexpr-binary (jbinop-div)
                                          (jexpr-binary (jbinop-div)
                                                        (jexpr-name "sumTime")
                                                        (jexpr-literal-floating
                                                         1000))
                                          (jexpr-name "n"))))
                     (jblock-imethod
                      (jexpr-name "System.out")
                      "format"
                      (list (jexpr-literal-string "  Maximum: %.3f%n")
                            (jexpr-binary (jbinop-div)
                                          (jexpr-name "maxTime")
                                          (jexpr-literal-floating 1000))))
                     (jblock-imethod (jexpr-name "System.out")
                                     "println"
                                     nil))))))
    (make-jmethod :access (jaccess-private)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-void)
                  :name method-name
                  :params (list (make-jparam :final? nil
                                             :type (jtype-int)
                                             :name "n"))
                  :throws (list *aij-class-undef-pkg-exc*)
                  :body method-body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-methods ((tests$ atj-test-listp)
                              (deep$ booleanp)
                              (guards$ booleanp)
                              (java-class$ stringp)
                              (verbose$ booleanp)
                              (pkg-class-names string-string-alistp)
                              (fn-method-names symbol-string-alistp)
                              (wrld plist-worldp))
  :returns (methods jmethod-listp)
  :short "Generate all the Java methods to run the specified tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are generated only if the @(':tests') input is not @('nil')."))
  (if (endp tests$)
      nil
    (b* ((first-method
          (atj-gen-test-method (car tests$)
                               deep$
                               guards$
                               java-class$
                               verbose$
                               pkg-class-names
                               fn-method-names
                               wrld))
         (rest-methods
          (atj-gen-test-methods (cdr tests$)
                                deep$
                                guards$
                                java-class$
                                verbose$
                                pkg-class-names
                                fn-method-names
                                wrld)))
      (cons first-method rest-methods))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-class ((tests$ atj-test-listp)
                            (deep$ booleanp)
                            (guards$ booleanp)
                            (java-class$ stringp)
                            (verbose$ booleanp)
                            (pkg-class-names string-string-alistp)
                            (fn-method-names symbol-string-alistp)
                            (wrld plist-worldp))
  :returns (class jclassp)
  :short "Generate the test Java class declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "This is a public class that contains all the generated methods.
    [JLS:7.6] says that a Java implementation may require
    public classes to be in files with the same names (plus extension).
    The code that we generate satisfies this requirement."))
  (b* (((run-when verbose$)
        (cw "~%Generate the Java methods to run the tests:~%"))
       (test-methods (atj-gen-test-methods tests$
                                           deep$
                                           guards$
                                           java-class$
                                           verbose$
                                           pkg-class-names
                                           fn-method-names
                                           wrld))
       ((run-when verbose$)
        (cw "~%Generate the test Java class.~%"))
       (failures-field (atj-gen-test-failures-field))
       (main-method (atj-gen-test-main-method tests$ java-class$))
       (body-class (append (list (jcbody-element-member
                                  (jcmember-field failures-field)))
                           (jmethods-to-jcbody-elements test-methods)
                           (list (jcbody-element-member
                                  (jcmember-method main-method))))))
    (make-jclass :access (jaccess-public)
                 :abstract? nil
                 :static? nil
                 :final? nil
                 :strictfp? nil
                 :name (str::cat java-class$ "Tests")
                 :superclass? nil
                 :superinterfaces nil
                 :body body-class)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-cunit ((deep$ booleanp)
                            (guards$ booleanp)
                            (java-package$ maybe-stringp)
                            (java-class$ stringp)
                            (tests$ atj-test-listp)
                            (verbose$ booleanp)
                            (pkg-class-names string-string-alistp)
                            (fn-method-names symbol-string-alistp)
                            (wrld plist-worldp))
  :returns (cunit jcunitp)
  :short "Generate the test Java compilation unit."
  (b* ((class (atj-gen-test-class tests$
                                  deep$
                                  guards$
                                  java-class$
                                  verbose$
                                  pkg-class-names
                                  fn-method-names
                                  wrld))
       ((run-when verbose$)
        (cw "~%Generate the test Java compilation unit.~%")))
    (make-jcunit :package? java-package$
                 :imports (list (jimport nil (str::cat *aij-package* ".*"))
                                (jimport nil "java.math.BigInteger")
                                (jimport nil "java.util.Arrays"))
                 :types (list class))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-file ((deep$ booleanp)
                           (guards$ booleanp)
                           (java-package$ maybe-stringp)
                           (java-class$ stringp)
                           (output-file-test$ stringp)
                           (tests$ atj-test-listp)
                           (verbose$ booleanp)
                           (pkg-class-names string-string-alistp)
                           (fn-method-names symbol-string-alistp)
                           state)
  :returns state
  :mode :program ; because of PRINT-TO-JFILE
  :short "Generate the test Java file."
  (b* ((cunit (atj-gen-test-cunit deep$
                                  guards$
                                  java-package$
                                  java-class$
                                  tests$
                                  verbose$
                                  pkg-class-names
                                  fn-method-names
                                  (w state)))
       ((unless (jcunitp cunit))
        (raise "Internal error: generated an invalid compilation unit.")
        state)
       ((run-when verbose$)
        (cw "~%Generate the test Java file.~%")))
    (print-to-jfile (print-jcunit cunit)
                    output-file-test$
                    state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-main-file ((deep$ booleanp)
                           (guards$ booleanp)
                           (java-package$ maybe-stringp)
                           (java-class$ stringp)
                           (output-file$ stringp)
                           (pkgs string-listp)
                           (fns-to-translate symbol-listp)
                           (verbose$ booleanp)
                           state)
  :returns (mv (pkg-class-names "A @(tsee string-string-alistp).")
               (fn-method-names "A @(tsee symbol-string-alistp).")
               state)
  :mode :program ; because of PRINT-TO-JFILE
  :short "Generate the main Java file."
  :long
  (xdoc::topstring
   (xdoc::p
    "We also return the alist from ACL2 package names to Java class names
     and the alist from ACL2 function symbols to Java method names,
     which must be eventually passed to the functions that generate
     the Java test class.
     These are @('nil') in the deep embedding approach;
     they are only used in the shallow embedding approach."))
  (b* ((wrld (w state))
       ((mv cunit
            pkg-class-names
            fn-method-names) (if deep$
                                 (mv (atj-gen-deep-main-cunit guards$
                                                              java-package$
                                                              java-class$
                                                              pkgs
                                                              fns-to-translate
                                                              verbose$
                                                              wrld)
                                     nil
                                     nil)
                               (atj-gen-shallow-main-cunit guards$
                                                           java-package$
                                                           java-class$
                                                           pkgs
                                                           fns-to-translate
                                                           verbose$
                                                           wrld)))
       ((unless (jcunitp cunit))
        (raise "Internal error: generated an invalid compilation unit.")
        (mv nil nil state))
       ((run-when verbose$)
        (cw "~%Generate the main Java file.~%"))
       (state (print-to-jfile (print-jcunit cunit)
                              output-file$
                              state)))
    (mv pkg-class-names fn-method-names state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-everything ((deep$ booleanp)
                            (guards$ booleanp)
                            (java-package$ maybe-stringp)
                            (java-class$ stringp)
                            (output-file$ stringp)
                            (output-file-test$ maybe-stringp)
                            (tests$ atj-test-listp)
                            (pkgs string-listp)
                            (fns-to-translate symbol-listp)
                            (verbose$ booleanp)
                            state)
  :returns (mv erp val state)
  :mode :program ; because of ATJ-GEN-MAIN/TEST-FILE
  :short "Generate the main Java file, and optionally the Java test file."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the soft and hard right margins to very large values
     to avoid line breaks in virtually all cases.
     Setting these margins to ``infinity'' is not supported.")
   (xdoc::p
    "We always generate the main Java file.
     We generate the test Java file only if @(':tests') is not @('nil').")
   (xdoc::p
    "We pass the alist from ACL2 package names to Java class names
     from one file generation function to the other.
     This is @('nil') in the deep embedding approach."))
  (state-global-let*
   ((fmt-soft-right-margin 1000000 set-fmt-soft-right-margin)
    (fmt-hard-right-margin 1000000 set-fmt-hard-right-margin))
   (b* (((mv pkg-class-names
             fn-method-names
             state) (atj-gen-main-file deep$
                                       guards$
                                       java-package$
                                       java-class$
                                       output-file$
                                       pkgs
                                       fns-to-translate
                                       verbose$
                                       state))
        (state (if tests$
                   (atj-gen-test-file deep$
                                      guards$
                                      java-package$
                                      java-class$
                                      output-file-test$
                                      tests$
                                      verbose$
                                      pkg-class-names
                                      fn-method-names
                                      state)
                 state)))
     (value nil))))
