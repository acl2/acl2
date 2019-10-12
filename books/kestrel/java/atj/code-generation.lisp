; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

; Avoid failure for atj-gen-number in ACL2(r):
; cert_param: non-acl2r

(include-book "aij-notions")
(include-book "types")
(include-book "test-structures")
(include-book "pretty-printer")
(include-book "pre-translation")
(include-book "post-translation")
(include-book "primitives")
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
     The pair may be a large binary tree,
     so we prefer not to generate a large Java expression.
     Instead, we generate
     a Java block that sets a local variable to the @(tsee car),
     a Java block that sets another local variable to the @(tsee cdr),
     and then a Java expression that builds the pair
     from those two variables.
     The two blocks are concatenated to result in a block and an expression
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
     since they would return always empty blocks.")
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
    (xdoc::seetopic "atj-pre-translation" "a pre-translation from ACL2 to ACL2")
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

(define atj-gen-test-jmethod ((test$ atj-testp)
                              (deep$ booleanp)
                              (guards$ booleanp)
                              (java-class$ stringp)
                              (verbose$ booleanp)
                              (pkg-class-names string-string-alistp)
                              (fn-method-names symbol-string-alistp)
                              (wrld plist-worldp))
  :returns (jmethod jmethodp)
  :verify-guards nil
  :short "Generate a Java method to run one of the specified tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "This is a private static method
     that prints the name of the test,
     builds the argument values of the test using AIJ,
     builds the result value of the test using AIJ,
     calls (the Java representation of) the function on them,
     compares the obtained result value with the test's result value,
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
     we expect that either they will all succeed or they will all fail.
     We note that
     the reason for storing the argument values into local variables
     in the shallow embedding approach,
     as opposed to passing the expressions directly to the method call,
     is to accurately measure just the time of each call,
     without the time needed to compute the argument expressions.")
   (xdoc::p
    "As a special case, if the integer parameter of the method is 0,
     times are not collected, and no minimum/maximum/sum is calculated,
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
     we are using the deep or shallow embedding approach:")
   (xdoc::ul
    (xdoc::li
     "For the deep embedding,
      we build the name of the function to call,
      we put the argument values into an array,
      and we produce the Java result
      via the @('call') method generated by ATJ
      (which uses the AIJ interpreter).")
    (xdoc::li
     "For the shallow embedding,
      we put the argument values into local variables,
      and we just call the Java method that represents the ACL2 function
      on those local variables.
      Since this code is in a class that is different from
      any of the generated Java classes that correspond to ACL2 packages,
      the Java method to call must be always preceded by the class name:
      thus, we use @('\"KEYWORD\"') as current package name,
      which never contains any functions."))
   (xdoc::p
    "Examining any generated instance of this method
     should make the above documentation,
     and the implementation of this code generation function,
     much clearer."))
  (b* (((atj-test test) test$)
       ((run-when verbose$)
        (cw "  ~s0~%" test.name))
       (jmethod-name (atj-gen-test-jmethod-name test.name))
       ((mv args-jblock
            args-jexprs
            jvar-value-index) (atj-gen-values test.arguments "value" 1))
       ((mv ares-jblock
            ares-jexpr
            &) (atj-gen-value test.result "value" jvar-value-index))
       (current-time-jexpr (jexpr-smethod (jtype-class "System")
                                          "currentTimeMillis"
                                          nil))
       (fn-type (atj-get-function-type test.function guards$ wrld))
       (in-types (atj-function-type->inputs fn-type))
       ((mv shallow-arg-jblock shallow-arg-jvars)
        (if deep$
            (mv nil nil)
          (atj-gen-test-jmethod-aux args-jexprs in-types 1)))
       (n!=0-jexpr (jexpr-binary (jbinop-ne)
                                 (jexpr-name "n")
                                 (jexpr-literal-0)))
       (jmethod-body
        (append
         (jblock-imethod (jexpr-name "System.out")
                         "print"
                         (list (atj-gen-jstring
                                (str::cat "Testing '" test.name "'..."))))
         args-jblock ; build test.arguments
         (if deep$
             (jblock-locvar (jtype-array *atj-jtype-value*)
                            "functionArguments"
                            (jexpr-newarray-init *atj-jtype-value*
                                                 args-jexprs))
           shallow-arg-jblock) ; assign to argument1, argument2, ...
         ares-jblock ; build test.result
         (jblock-locvar *atj-jtype-value* "resultAcl2" ares-jexpr)
         (and deep$
              (jblock-locvar *atj-jtype-symbol*
                             "functionName"
                             (atj-gen-symbol test.function)))
         (jblock-locvar (jtype-boolean) "pass" (jexpr-literal-true))
         (jblock-locvar (jtype-array (jtype-long))
                        "times"
                        (jexpr-cond n!=0-jexpr
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
           (jblock-locvar (jtype-long) "startTime" current-time-jexpr)
           (jblock-locvar *atj-jtype-value*
                          "resultJava"
                          (if deep$
                              (jexpr-smethod (jtype-class java-class$)
                                             "call"
                                             (list
                                              (jexpr-name "functionName")
                                              (jexpr-name "functionArguments")))
                            (jexpr-smethod (jtype-class java-class$)
                                           (atj-gen-shallow-fnname
                                            test.function
                                            pkg-class-names
                                            fn-method-names
                                            "KEYWORD")
                                           (jexpr-name-list
                                            shallow-arg-jvars))))
           (jblock-locvar (jtype-long) "endTime" current-time-jexpr)
           (jblock-asg (jexpr-name "pass")
                       (jexpr-binary (jbinop-logand)
                                     (jexpr-name "pass")
                                     (jexpr-imethod (jexpr-name "resultAcl2")
                                                    "equals"
                                                    (list (jexpr-name
                                                           "resultJava")))))
           (jblock-if n!=0-jexpr
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
                       (jblock-if (jexpr-binary (jbinop-logor)
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
         (jblock-if n!=0-jexpr
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
                  :name jmethod-name
                  :params (list (make-jparam :final? nil
                                             :type (jtype-int)
                                             :name "n"))
                  :throws (list *atj-jclass-eval-exc*)
                  :body jmethod-body))

  :prepwork
  ((define atj-gen-test-jmethod-aux ((args-jexprs jexpr-listp)
                                     (types atj-type-listp)
                                     (index posp))
     :guard (= (len args-jexprs) (len types))
     :returns (mv (jblock jblockp)
                  (jvars string-listp))
     (cond ((endp args-jexprs) (mv nil nil))
           (t (b* ((first-jvar (str::cat "argument" (str::natstr index)))
                   (first-type (car types))
                   (first-jtype (atj-type-to-jtype first-type))
                   (first-jexpr (jexpr-cast (atj-type-to-jtype first-type)
                                            (car args-jexprs)))
                   (first-jblock (jblock-locvar first-jtype
                                                first-jvar
                                                first-jexpr))
                   ((mv rest-jblock rest-jvars)
                    (atj-gen-test-jmethod-aux (cdr args-jexprs)
                                              (cdr types)
                                              (1+ index))))
                (mv (append first-jblock rest-jblock)
                    (cons first-jvar rest-jvars))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-jmethods ((tests$ atj-test-listp)
                               (deep$ booleanp)
                               (guards$ booleanp)
                               (java-class$ stringp)
                               (verbose$ booleanp)
                               (pkg-class-names string-string-alistp)
                               (fn-method-names symbol-string-alistp)
                               (wrld plist-worldp))
  :returns (jmethods jmethod-listp)
  :verify-guards nil
  :short "Generate all the Java methods to run the specified tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are generated only if the @(':tests') input is not @('nil')."))
  (if (endp tests$)
      nil
    (b* ((first-jmethod
          (atj-gen-test-jmethod (car tests$)
                                deep$
                                guards$
                                java-class$
                                verbose$
                                pkg-class-names
                                fn-method-names
                                wrld))
         (rest-jmethods
          (atj-gen-test-jmethods (cdr tests$)
                                 deep$
                                 guards$
                                 java-class$
                                 verbose$
                                 pkg-class-names
                                 fn-method-names
                                 wrld)))
      (cons first-jmethod rest-jmethods))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-jclass ((tests$ atj-test-listp)
                             (deep$ booleanp)
                             (guards$ booleanp)
                             (java-class$ stringp)
                             (verbose$ booleanp)
                             (pkg-class-names string-string-alistp)
                             (fn-method-names symbol-string-alistp)
                             (wrld plist-worldp))
  :returns (jclass jclassp)
  :verify-guards nil
  :short "Generate the test Java class declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "This is a public class that contains all the generated methods.
    [JLS] says that a Java implementation may require
    public classes to be in files with the same names (plus extension).
    The code that we generate satisfies this requirement."))
  (b* (((run-when verbose$)
        (cw "~%Generating Java code for the tests:~%"))
       (failures-jfield (atj-gen-test-failures-jfield))
       (test-jmethods (atj-gen-test-jmethods tests$
                                             deep$
                                             guards$
                                             java-class$
                                             verbose$
                                             pkg-class-names
                                             fn-method-names
                                             wrld))
       (main-jmethod (atj-gen-test-main-jmethod tests$ java-class$))
       (body-jclass (append (list (jcmember-field failures-jfield))
                            (jmethods-to-jcmembers test-jmethods)
                            (list (jcmember-method main-jmethod)))))
    (make-jclass :access (jaccess-public)
                 :abstract? nil
                 :static? nil
                 :final? nil
                 :strictfp? nil
                 :name (str::cat java-class$ "Tests")
                 :superclass? nil
                 :superinterfaces nil
                 :body body-jclass)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-jcunit ((deep$ booleanp)
                             (guards$ booleanp)
                             (java-package$ maybe-stringp)
                             (java-class$ stringp)
                             (tests$ atj-test-listp)
                             (verbose$ booleanp)
                             (pkg-class-names string-string-alistp)
                             (fn-method-names symbol-string-alistp)
                             (wrld plist-worldp))
  :returns (jcunit jcunitp)
  :verify-guards nil
  :short "Generate the test Java compilation unit."
  (make-jcunit :package? java-package$
               :imports (list (jimport nil (str::cat *atj-aij-jpackage* ".*"))
                              (jimport nil "java.math.BigInteger"))
               :types (list (atj-gen-test-jclass tests$
                                                 deep$
                                                 guards$
                                                 java-class$
                                                 verbose$
                                                 pkg-class-names
                                                 fn-method-names
                                                 wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-jfile ((deep$ booleanp)
                       (guards$ booleanp)
                       (java-package$ maybe-stringp)
                       (java-class$ maybe-stringp)
                       (output-file$ stringp)
                       (pkgs string-listp)
                       (fns symbol-listp)
                       (verbose$ booleanp)
                       state)
  :returns (mv (pkg-class-names "A @(tsee string-string-alistp).")
               (fn-method-names "A @(tsee symbol-string-alistp).")
               state)
  :mode :program
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
  (b* (((mv cunit
            pkg-class-names
            fn-method-names) (if deep$
                                 (mv (atj-gen-deep-jcunit guards$
                                                          java-package$
                                                          java-class$
                                                          pkgs
                                                          fns
                                                          verbose$
                                                          state)
                                     nil
                                     nil)
                               (atj-gen-shallow-jcunit guards$
                                                       java-package$
                                                       java-class$
                                                       pkgs
                                                       fns
                                                       verbose$
                                                       state)))
       (state (print-to-jfile (print-jcunit cunit)
                              output-file$
                              state)))
    (mv pkg-class-names fn-method-names state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-test-jfile ((deep$ booleanp)
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
  :mode :program
  :short "Generate the test Java file."
  (print-to-jfile (print-jcunit (atj-gen-test-jcunit deep$
                                                     guards$
                                                     java-package$
                                                     java-class$
                                                     tests$
                                                     verbose$
                                                     pkg-class-names
                                                     fn-method-names
                                                     (w state)))
                  output-file-test$
                  state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-everything ((deep$ booleanp)
                            (guards$ booleanp)
                            (java-package$ maybe-stringp)
                            (java-class$ maybe-stringp)
                            (output-file$ stringp)
                            (output-file-test$ maybe-stringp)
                            (tests$ atj-test-listp)
                            (pkgs string-listp)
                            (fns symbol-listp)
                            (verbose$ booleanp)
                            state)
  :returns (mv erp val state)
  :mode :program
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
   ((fmt-soft-right-margin 100000 set-fmt-soft-right-margin)
    (fmt-hard-right-margin 100000 set-fmt-hard-right-margin))
   (b* (((mv pkg-class-names
             fn-method-names
             state) (atj-gen-jfile deep$
                                   guards$
                                   java-package$
                                   java-class$
                                   output-file$
                                   pkgs
                                   fns
                                   verbose$
                                   state))
        (state (if tests$
                   (atj-gen-test-jfile deep$
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
