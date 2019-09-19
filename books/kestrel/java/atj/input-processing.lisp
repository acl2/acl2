; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "aij-notions")
(include-book "primitives")
(include-book "test-structures")

(include-book "kestrel/std/system/unquote-term" :dir :system)
(include-book "kestrel/utilities/doublets" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/event-macros/xdoc-constructors" :dir :system)
(include-book "oslib/top" :dir :system)
(include-book "std/util/defaggregate" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing atj)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-process-targets ((targets true-listp) deep guards ctx state)
  :returns (mv erp
               (result "Always @('nil').")
               state)
  :verify-guards nil
  :short "Process the @('fn1'), ..., @('fnp') inputs."
  (b* (((er &) (case (len targets)
                 (0 (er-soft+ ctx t nil
                              "At least one target function must be supplied."))
                 (1 (ensure-function-name$ (car targets)
                                           (msg "The ~x0 input" (car targets))
                                           t nil))
                 (t (ensure-list-functions$ targets
                                            (msg "The ~&0 inputs" targets)
                                            t nil))))
       ((er &) (ensure-list-no-duplicates$ targets
                                           (msg "The target functions ~&0"
                                                targets)
                                           t nil))
       ((unless (or (eq deep nil)
                    (eq guards t))) (value nil))
       (target-prims (intersection-eq targets *atj-primitive-fns*))
       ((when (null target-prims)) (value nil)))
    (er-soft+ t nil
              "Since the :DEEP input is (perhaps by default) NIL ~
               and the :GUARDS input is T, ~
               ~@0."
              (if (= (len target-prims) 1)
                  (msg "the function ~x0 cannot be specified as target"
                       (car target-prims))
                (msg "the functions ~&0 cannot be specified as targets")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-process-java-package ((java-package) ctx state)
  :returns (mv erp
               (nothing "Always @('nil').")
               state)
  :verify-guards nil
  :short "Process the @(':java-package') input."
  (b* (((er &) (ensure-string-or-nil$ java-package
                                      "The :JAVA-PACKAGE input"
                                      t nil))
       ((unless (or (null java-package)
                    (atj-string-ascii-java-package-name-p java-package)))
        (er-soft+ ctx t nil
                  "The :JAVA-PACKAGE input ~x0 is not ~
                   NIL or a valid Java package name ~
                   consisting of only ASCII characters."
                  java-package))
       ((when (equal java-package *atj-aij-jpackage*))
        (er-soft+ ctx t nil
                  "The :JAVA-PACKAGE input ~x0 must differ from ~
                   the name of the Java package of AIJ ~x1."
                  java-package *atj-aij-jpackage*)))
    (value nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-default-java-class*
  :short "Default Java class name to use if @(':java-class') is @('nil')."
  "ACL2Code"
  ///
  (assert-event (stringp *atj-default-java-class*)))

(define atj-process-java-class (java-class ctx state)
  :returns (mv erp
               (java-class$ "A @(tsee stringp).")
               state)
  :verify-guards nil
  :short "Process the @(':java-class') input."
  (b* (((er &) (ensure-string-or-nil$ java-class
                                      "The :JAVA-CLASS input"
                                      t nil))
       ((unless (or (null java-class)
                    (atj-string-ascii-java-identifier-p java-class)))
        (er-soft+ ctx t nil
                  "The :JAVA-CLASS input ~x0 is not ~
                   NIL or a valid Java class name ~
                   consisting of only ASCII characters."
                  java-class))
       (name (or java-class *atj-default-java-class*)))
    (value name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-ensure-terms-quoted-constants
  ((qcs pseudo-term-listp "@('qc1'), @('qc2'), etc.")
   (fn symbolp "The @('fn') in @('(fn qc1 qc2 ...)'); just for error messages.")
   (term "One of the test terms @('termj'); just for error messages.")
   ctx
   state)
  :returns (mv erp (nothing null) state)
  :short "Cause an error if
          any argument of the call @('(fn qc1 qc2 ...)')
          to which a test term translates
          is not a quoted constant."
  (b* (((when (endp qcs)) (value nil))
       (qc (car qcs))
       ((unless (quotep qc))
        (er-soft+ ctx t nil
                  "The term ~x0 that is an argument of ~
                   the function call (~x1 ...) that translates ~
                   the test term ~x2 in the :TESTS input, ~
                   must be a quoted constant."
                  qc fn term)))
    (atj-ensure-terms-quoted-constants (cdr qcs) fn term ctx state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-process-tests (tests (targets$ symbol-listp) ctx state)
  :returns (mv erp
               (tests$ "An @(tsee atj-test-listp).")
               state)
  :mode :program
  :short "Process the @(':tests') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "After evaluating @(':tests')
     and ensuring that the result is a list of doublets,
     we convert it into an alist and we ensure that the keys are unique.
     Then we process each pair in the alist.")
   (xdoc::p
    "For each pair in the alist,
     we first ensure that the name is a non-empty string
     consisting only of letters and digits.
     Then we translate the term (ensuring that the translation succeeds),
     and we ensure that it has the form @('(fn qc1 qc2 ...)'),
     where @('fn') is one of the target functions
     and @('qc1'), @('qc2'), etc. are quoted constants.
     (Note that these checks imply that the term is ground,
     so this condition does not need to be checked explicitly.)
     We unquote @('qc1'), @('qc2'), etc., obtaining a list of argument values.
     We evaluate the call @('(fn qc1 qc2 ...)'), obtaining a result value.
     We create an @(tsee atj-test) aggregate for each test."))
  (b* (((er (cons & tests)) (trans-eval tests ctx state nil))
       (description "The :TESTS input")
       ((er &) (ensure-doublet-list$ tests description t nil))
       (alist (doublets-to-alist tests))
       (names (strip-cars alist))
       (description (msg
                     "The list ~x0 of names of the tests in the :TESTS input"
                     names))
       ((er &) (ensure-list-no-duplicates$ names description t nil)))
    (atj-process-tests-aux alist targets$ ctx state))

  :prepwork
  ((define atj-process-tests-aux ((tests-alist alistp)
                                  (targets$ symbol-listp)
                                  ctx
                                  state)
     :returns (mv erp
                  tests$ ; ATJ-TEST-LISTP
                  state)
     :mode :program
     :parents nil
     (b* (((when (endp tests-alist)) (value nil))
          ((cons (cons name term) tests-alist) tests-alist)
          ((er &) (ensure-string$ name
                                  (msg "The test name ~x0 in the :TESTS input"
                                       name)
                                  t nil))
          ((when (equal name ""))
           (er-soft+ ctx t nil "The test name ~x0 in the :TESTS input ~
                                cannot be the empty string." name))
          ((unless (chars-in-charset-p (explode name) (alpha/digit-chars)))
           (er-soft+ ctx t nil "The test name ~x0 in the :TESTS input ~
                                must contain only letters and digits." name))
          ((er (list term$ &))
           (ensure-term$ term
                         (msg "The test term ~x0 in the :TESTS input" term)
                         t nil))
          ((when (or (variablep term$)
                     (fquotep term$)
                     (flambda-applicationp term$)))
           (er-soft+ ctx t nil
                     "The test term ~x0 in the :TESTS input ~
                      must translate to ~
                      the application of a named function." term))
          (fn (ffn-symb term$))
          ((er &) (ensure-member-of-list$
                   fn
                   targets$
                   (msg "among the target functions ~&0." targets$)
                   (msg "The function ~x0 called by ~
                         the test term ~x1 in the :TESTS input"
                        fn term)
                   t nil))
          (qcs (fargs term$))
          ((er &) (atj-ensure-terms-quoted-constants qcs fn term ctx state))
          (args (unquote-term-list qcs))
          ((er (cons & res)) (trans-eval term$ ctx state nil))
          (agg (atj-test name fn args res))
          ((er aggs) (atj-process-tests-aux tests-alist targets$ ctx state)))
       (value (cons agg aggs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-process-output-dir (output-dir
                                (java-class$ stringp)
                                (tests$ atj-test-listp)
                                ctx
                                state)
  :returns (mv erp
               (result "A tuple @('(output-file$ output-file-test$)')
                        satisfying
                        @('(typed-tuplep stringp maybe-stringp)'),
                        where @('output-file$') is the path
                        of the generated main Java file,
                        and @('output-file-test$') is
                        @('nil') if the @(':tests') input is @('nil'),
                        otherwise it is the path
                        of the generated test Java file.")
               state)
  :mode :program
  :short "Process the @(':output-dir') input."
  (b* (((er &) (ensure-string$ output-dir "The :OUTPUT-DIR input" t nil))
       ((mv err/msg kind state) (oslib::file-kind output-dir))
       ((when (or err/msg
                  (not (eq kind :directory))))
        (er-soft+ ctx t nil
                  "The output directory ~x0 is invalid."
                  output-dir))
       (file (oslib::catpath output-dir
                             (concatenate 'string java-class$ ".java")))
       ((er &) (b* (((mv err/msg exists state) (oslib::path-exists-p file))
                    ((when err/msg)
                     (er-soft+ ctx t nil
                               "The existence of the output path ~x0 ~
                                cannot be tested." file))
                    ((when (not exists)) (value :this-is-irrelevant))
                    ((mv err/msg kind state) (oslib::file-kind file))
                    ((when err/msg)
                     (er-soft+ ctx t nil
                               "The kind of the output path ~x0 ~
                                cannot be tested." file))
                    ((when (not (eq kind :regular-file)))
                     (er-soft+ ctx t nil
                               "The output path ~x0 ~
                                exists but is not a regular file." file)))
                 (value :this-is-irrelevant)))
       (file-test (if tests$
                      (oslib::catpath output-dir
                                      (concatenate 'string
                                                   java-class$
                                                   "Tests.java"))
                    nil))
       ((er &) (b* (((when (null file-test)) (value :this-is-irrelevant))
                    ((mv err/msg exists state) (oslib::path-exists-p file-test))
                    ((when err/msg)
                     (er-soft+ ctx t nil
                               "The existence of the output path ~x0 ~
                                cannot be tested." file-test))
                    ((when (not exists)) (value :this-is-irrelevant))
                    ((mv err/msg kind state) (oslib::file-kind file-test))
                    ((when err/msg)
                     (er-soft+ ctx t nil
                               "The kind of the output path ~x0 ~
                                cannot be tested." file-test))
                    ((when (not (eq kind :regular-file)))
                     (er-soft+ ctx t nil
                               "The output path ~x0 ~
                                exists but is not a regular file." file-test)))
                 (value :this-is-irrelevant))))
    (value (list file file-test))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-allowed-options*
  :short "Keyword options accepted by @(tsee atj)."
  (list :deep
        :guards
        :java-package
        :java-class
        :output-dir
        :tests
        :verbose)
  ///
  (assert-event (symbol-listp *atj-allowed-options*))
  (assert-event (no-duplicatesp-eq *atj-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-process-inputs ((args true-listp) ctx state)
  :returns (mv erp
               (result "A tuple @('((fn1 ... fnp)
                                    deep$
                                    guards$
                                    java-package$
                                    java-class$
                                    output-file$
                                    output-file-test$
                                    tests$
                                    verbose$)')
                        satisfying
                        @('(typed-tuplep symbol-listp
                                         booleanp
                                         booleanp
                                         maybe-stringp
                                         stringp
                                         stringp
                                         maybe-stringp
                                         atj-test-listp
                                         booleanp
                                         result)'),
                        where @('fn1'), ..., @('fnp') are
                        the names of the target functions,
                        @('deep$') is the @(':deep') input,
                        @('guards$') is the @(':guards') input,
                        @('java-package$') is the @(':java-package') input,
                        @('java-class$) is the result of
                        @(tsee atj-process-java-class),
                        @('output-file$') and @('output-file-test$')
                        are the result of (tsee atj-process-output-dir),
                        @('tests$') is the result of
                        @(tsee atj-process-tests), and
                        @('verbose$') is the @(':verbose') input.")
               state)
  :mode :program
  :short "Ensure that the inputs to @(tsee atj) are valid."
  :long
  (xdoc::topstring-p
   "We process the inputs in order,
    except that @(':output-dir') is processed after @(':tests')
    because the result of processing the latter
    is used in processing the former.")
  (b* (((mv erp targets options) (partition-rest-and-keyword-args
                                  args *atj-allowed-options*))
       ((when erp) (er-soft+ ctx t nil
                             "The inputs must be the names of ~
                              one or more target functions ~
                              followed by the options ~&0."
                             *atj-allowed-options*))
       (deep (cdr (assoc-eq :deep options)))
       (guards (cdr (assoc-eq :guards options)))
       (java-package (cdr (assoc-eq :java-package options)))
       (java-class (cdr (assoc-eq :java-class options)))
       (output-dir (or (cdr (assoc-eq :output-dir options)) "."))
       (tests (cdr (assoc-eq :tests options)))
       (verbose (cdr (assoc-eq :verbose options)))
       ((er &) (atj-process-targets targets deep guards ctx state))
       ((er &) (ensure-boolean$ deep "The :DEEP intput" t nil))
       ((er &) (ensure-boolean$ guards "The :GUARDS intput" t nil))
       ((er &) (atj-process-java-package java-package ctx state))
       ((er java-class$) (atj-process-java-class java-class ctx state))
       ((er tests$) (atj-process-tests tests targets ctx state))
       ((er (list output-file$
                  output-file-test$)) (atj-process-output-dir
                                       output-dir java-class$ tests$ ctx state))
       ((er &) (ensure-boolean$ verbose "The :VERBOSE input" t nil)))
    (value (list targets
                 deep
                 guards
                 java-package
                 java-class$
                 output-file$
                 output-file-test$
                 tests$
                 verbose))))
