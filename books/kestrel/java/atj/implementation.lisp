; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

; Avoid failure for atj-gen-number-value in ACL2(r):
; cert_param: non-acl2r

(include-book "kestrel/utilities/doublets" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/strings/hexstrings" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)
(include-book "oslib/top" :dir :system)
(include-book "std/strings/charset" :dir :system)
(include-book "std/util/defaggregate" :dir :system)

(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

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
     "@('java-package'),
      @('java-class'),
      @('output-dir'), and
      @('tests')
      are the homonymous inputs to @(tsee atj),
      before being processed.
      These formal parameters have no types because they may be any values.")
    (xdoc::li
     "@('java-package$'),
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
     "@('pkg-witness') is the name of the symbol
      returned by @(tsee pkg-witness).")
    (xdoc::li
     "@('fns-to-translate') is the list of names
      of all the non-primitive functions to be translated to Java.")
    (xdoc::li
     "@('channel') is the output channel of the generated Java file(s).")
    (xdoc::li
     "@('value-next-var'),
      @('term-next-var'), and
      @('lambda-next-var')
      are the indices of the next local variables to use
      to construct values, terms, and lambda expressions.
      See @(tsee atj-code-generation)."))
   (xdoc::p
    "The parameters of implementation functions that are not listed above
     are described in, or clear from, those functions' documentation."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-library-extensions
  :parents (atj-implementation)
  :short "Library extensions for @(tsee atj)."
  :long
  (xdoc::topstring-p
   "These will be moved to appropriate libraries eventually.")
  :default-parent t)

(defines atj-remove-mbe-exec-from-term
  :short "Turn every call @('(mbe :logic a :exec b)') in a term
          into just its @(':logic') part @('a')."
  :long
  (xdoc::topstring-p
   "In translated terms,
    these have the form @('(return-last 'acl2::mbe1-raw b a)').")

  (define atj-remove-mbe-exec-from-term ((term pseudo-termp))
    :returns (new-term "A @(tsee pseudo-termp).")
    (b* (((when (variablep term)) term)
         ((when (fquotep term)) term)
         (fn (ffn-symb term))
         (args (fargs term))
         ((when (and (eq fn 'return-last)
                     (equal (first args) '(quote acl2::mbe1-raw))))
          (atj-remove-mbe-exec-from-term (third args)))
         (new-fn (if (symbolp fn)
                     fn
                   (make-lambda (lambda-formals fn)
                                (atj-remove-mbe-exec-from-term
                                 (lambda-body fn)))))
         (new-args (atj-remove-mbe-exec-from-terms args)))
      (fcons-term new-fn new-args)))

  (define atj-remove-mbe-exec-from-terms ((terms pseudo-term-listp))
    :returns (new-terms "A @(tsee pseudo-term-listp).")
    (b* (((when (endp terms)) nil)
         ((cons term terms) terms)
         (new-term (atj-remove-mbe-exec-from-term term))
         (new-terms (atj-remove-mbe-exec-from-terms terms)))
      (cons new-term new-terms))))

(define atj-unquote-lst ((list quote-listp))
  :returns (new-list true-listp)
  :verify-guards nil
  :short "Unquote all the elements of a list."
  (cond ((endp list) nil)
        (t (cons (unquote (car list))
                 (atj-unquote-lst (cdr list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-input-processing
  :parents (atj-implementation)
  :short "Input processing performed by @(tsee atj)."
  :long
  (xdoc::topstring-p
   "This involves validating the inputs.
    When validation fails, <see topic='@(url er)'>soft errors</see> occur.
    Thus, generally the input processing functions return
    <see topic='@(url acl2::error-triple)'>error triples</see>.")
  :order-subtopics t
  :default-parent t)

(define atj-process-targets ((targets true-listp) ctx state)
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
                                           t nil)))
    (value nil)))

(defval *atj-java-keywords*
  :short "The keywords of the Java language, as ACL2 strings."
  (list "abstract"
        "assert"
        "boolean"
        "break"
        "byte"
        "case"
        "catch"
        "char"
        "class"
        "const"
        "continue"
        "default"
        "do"
        "double"
        "else"
        "enum"
        "extends"
        "final"
        "finally"
        "float"
        "for"
        "if"
        "goto"
        "implements"
        "import"
        "instanceof"
        "int"
        "interface"
        "long"
        "native"
        "new"
        "package"
        "private"
        "protected"
        "public"
        "return"
        "short"
        "static"
        "strictfp"
        "super"
        "switch"
        "synchronized"
        "this"
        "throw"
        "throws"
        "transient"
        "try"
        "void"
        "volatile"
        "while")
  ///
  (assert-event (string-listp *atj-java-keywords*))
  (assert-event (no-duplicatesp-equal *atj-java-keywords*)))

(defval *atj-java-boolean-literals*
  :short "The boolean literals of the Java language, as ACL2 strings."
  (list "true" "false"))

(defval *atj-java-null-literal*
  :short "The null literal of the Java language, as an ACL2 string."
  "null")

(define atj-string-ascii-java-identifier-p ((string stringp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 string is a valid Java identifier, all in ASCII."
  :long
  (xdoc::topstring-p
   "The string must be non-empty,
    start with a letter or underscore or dollar sign,
    and continue with zero or more
    letters, digits, underscores, and dollar signs.
    It must also be different
    from Java keywords and from the boolean and null literals.")
  (and (not (member-equal string *atj-java-keywords*))
       (not (member-equal string *atj-java-boolean-literals*))
       (not (equal string *atj-java-null-literal*))
       (b* ((chars (explode string)))
         (and (consp chars)
              (alpha/uscore/dollar-char-p (car chars))
              (alpha/digit/uscore/dollar-charlist-p (cdr chars))))))

(std::deflist atj-string-ascii-java-identifier-listp (x)
  (atj-string-ascii-java-identifier-p x)
  :guard (string-listp x)
  :short "Check if a list of ACL2 strings includes only ASCII Java identifiers."
  :true-listp t
  :elementp-of-nil nil)

(define atj-decompose-at-dots ((string stringp))
  :returns (substrings string-listp)
  :verify-guards nil
  :short "Decompose an ACL2 string
          into its substrings delimited by dot characters,
          including empty substrings."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the string has no dots, a singleton list with the string is returned.
     Otherwise, we return a list consisting of
     the substring from the start of the string to the first dot,
     the substrings between two consecutive dots (in order),
     and the substring from the last dot to the end of the string.
     The substrings include no dots, and may be empty.")
   (xdoc::p
    "For example:")
   (xdoc::ul
    (xdoc::li
     "@('\"ab.c.def\"') is decomposed into @('(\"ab\" \"c\" \"def\")').")
    (xdoc::li
     "@('\"xyz\"') is decomposed into @('(\"xyz\")').")
    (xdoc::li
     "@('\".abc..de.\"') is decomposed into
      @('(\"\" \"abc\" \"\" \"de\" \"\")').")))
  (atj-decompose-at-dots-aux (explode string) nil)

  :prepwork
  ((define atj-decompose-at-dots-aux ((chars character-listp)
                                      (rev-current-substrings string-listp))
     :returns (final-substrings string-listp
                                :hyp (string-listp rev-current-substrings))
     :verify-guards nil
     :parents nil
     (if (endp chars)
         (rev rev-current-substrings)
       (b* ((pos (position #\. chars)))
         (if pos
             (b* ((substring (implode (take pos chars)))
                  (chars (nthcdr (1+ pos) chars))
                  (rev-current-substrings (cons substring
                                                rev-current-substrings)))
               (atj-decompose-at-dots-aux chars rev-current-substrings))
           (b* ((substring (implode chars))
                (rev-final-substrings (cons substring rev-current-substrings)))
             (rev rev-final-substrings)))))
     :measure (len chars))))

(define atj-string-ascii-java-package-name-p ((string stringp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Check if an ACL2 string is a valid Java package name, all in ASCII."
  :long
  (xdoc::topstring-p
   "The string must consist of one or more ASCII Java identifiers
    separated by dots.")
  (b* ((identifiers (atj-decompose-at-dots string)))
    (and (consp identifiers)
         (atj-string-ascii-java-identifier-listp identifiers))))

(defval *atj-aij-package*
  :short "Name of the Java package of AIJ."
  "edu.kestrel.acl2.aij"
  ///
  (assert-event (atj-string-ascii-java-package-name-p *atj-aij-package*)))

(define atj-process-java-package ((java-package) ctx state)
  :returns (mv erp
               (result "Always @('nil').")
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
                   a valid Java package name ~
                   consisting of only ASCII characters."
                  java-package))
       ((when (equal java-package *atj-aij-package*))
        (er-soft+ ctx t nil
                  "The :JAVA-PACKAGE input ~x0 must differ from ~
                   the name of the Java package of AIJ ~x1."
                  java-package *atj-aij-package*)))
    (value nil)))

(define atj-process-java-class (java-class ctx state)
  :returns (mv erp
               (java-class "A @(tsee stringp) to use as
                            the name of the class to generate.")
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
                   a valid Java class name ~
                   consisting of only ASCII characters."
                  java-class))
       (name (or java-class "ACL2")))
    (value name)))

(std::defaggregate atj-test
  :short "Recognize a processed test specified by the @(':tests') input."
  :long
  "<p>
   Each test specified by the @(':tests') input
   must the form @('(namej termj)'),
   where @('termj') must translate to @('(fn qc1 qc2 ...)'),
   as explained in the documentation.
   As the @(':tests') input is processed,
   the information about each test is stored
   into an aggregate of this type.
   This aggregate stores
   @('namej'),
   @('fn'),
   The list of values of the quoted constants @('qc1'), @('qc2'), etc.,
   and the result of the ground call @('(fn qc1 qc2 ...)').
   </p>"
  ((name "This is @('namej')." stringp)
   (function "This is @('fn')." symbolp)
   (arguments "This is the list of values of @('qc1'), @('qc2'), etc."
              true-listp)
   (result "This is the result of @('(fn qc1 qc2 ...)')."))
  :pred atj-testp)

(std::deflist atj-test-listp (x)
  (atj-testp x)
  :short "Recognize true lists of processed tests
          specified by the @(':tests') input.")

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
          (args (atj-unquote-lst qcs))
          ((er (cons & res)) (trans-eval term$ ctx state nil))
          (agg (atj-test name fn args res))
          ((er aggs) (atj-process-tests-aux tests-alist targets$ ctx state)))
       (value (cons agg aggs))))))

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
                                                   "Test.java"))
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

(defval *atj-allowed-options*
  :short "Keyword options accepted by @(tsee atj)."
  (list :java-package
        :java-class
        :output-dir
        :tests
        :verbose)
  ///
  (assert-event (symbol-listp *atj-allowed-options*))
  (assert-event (no-duplicatesp-eq *atj-allowed-options*)))

(define atj-process-inputs ((args true-listp) ctx state)
  :returns (mv erp
               (result "A tuple @('((fn1 ... fnp)
                                    java-package$
                                    java-class$
                                    output-file$
                                    output-file-test$
                                    tests$
                                    verbose$)')
                        satisfying
                        @('(typed-tuplep symbol-listp
                                         maybe-stringp
                                         stringp
                                         stringp
                                         maybe-stringp
                                         atj-test-listp
                                         booleanp
                                         result)'),
                        where @('fn1'), ..., @('fnp') are
                        the names of the target functions,
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
  :short "Ensure that the inputs to the macro are valid."
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
       (java-package (cdr (assoc-eq :java-package options)))
       (java-class (cdr (assoc-eq :java-class options)))
       (output-dir (or (cdr (assoc-eq :output-dir options)) "."))
       (tests (cdr (assoc-eq :tests options)))
       (verbose (cdr (assoc-eq :verbose options)))
       ((er &) (atj-process-targets targets ctx state))
       ((er &) (atj-process-java-package java-package ctx state))
       ((er java-class$) (atj-process-java-class java-class ctx state))
       ((er tests$) (atj-process-tests tests targets ctx state))
       ((er (list output-file$
                  output-file-test$)) (atj-process-output-dir
                                       output-dir java-class$ tests$ ctx state))
       ((er &) (ensure-boolean$ verbose "The :VERBOSE input" t nil)))
    (value (list targets
                 java-package
                 java-class$
                 output-file$
                 output-file-test$
                 tests$
                 verbose))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-information-gathering
  :parents (atj-implementation)
  :short "Information gathering performed by @(tsee atj)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This code gathers the following information:")
   (xdoc::ul
    (xdoc::li
     "The names of all the currently known ACL2 packages.
      These are used to initialize
      the Java representation of the ACL2 environment.")
    (xdoc::li
     "The name of the symbol returned by @(tsee pkg-witness).
      This is also used to initialize
      the Java representation of the ACL2 environment.")
    (xdoc::li
     "The names of all the non-primitive functions to be translated to Java,
      as determined by @('fn1'), ..., @('fnp').")))
  :order-subtopics t
  :default-parent t)

(defval *atj-allowed-raws*
  :short "ACL2 functions with raw Lisp code that are accepted by ATJ."
  :long
  "<p>
   This is the whitelist mentioned in the documentation.
   </p>
   <p>
   The functions in this list have no side effects
   and their execution is functionally equivalent to
   their @('unnormalized-body') property.
   </p>
   <p>
   @(tsee return-last) is not explicitly included in this list,
   because it is only partially whitelisted, as explained in the documentation.
   Calls of @(tsee return-last) are handled specially in the code.
   </p>
   <p>
   This whitelist will be extended as needed.
   </p>"
  '(=
    /=
    abs
    acons
    alpha-char-p
    assoc-equal
    atom
    ash
    butlast
    ceiling
    char
    char-downcase
    char-equal
    char-upcase
    char<
    char>
    char<=
    char>=
    conjugate
    endp
    eq
    eql
    evenp
    expt
    floor
    identity
    integer-length
    hons
    hons-equal
    hons-get
    keywordp
    last
    len
    length
    listp
    logandc1
    logandc2
    logbitp
    logcount
    lognand
    lognor
    lognot
    logorc1
    logorc2
    logtest
    max
    member-equal
    min
    minusp
    mod
    nonnegative-integer-quotient
    not
    nth
    nthcdr
    null
    oddp
    plusp
    position-equal
    rassoc-equal
    rem
    remove-equal
    revappend
    reverse
    round
    signum
    standard-char-p
    string
    string-downcase
    string-equal
    string-upcase
    string<
    string>
    string<=
    string>=
    sublis
    subseq
    subsetp-equal
    subst
    substitute
    take
    truncate
    zerop
    zip
    zp)
  ///
  (assert-event (symbol-listp *atj-allowed-raws*))
  (assert-event (no-duplicatesp-eq *atj-allowed-raws*)))

(define atj-fns-to-translate ((targets$ symbol-listp)
                              (verbose$ booleanp)
                              ctx
                              state)
  :returns (mv erp
               (fns-to-translate "A @(tsee symbol-listp).")
               state)
  :mode :program
  :short "Collect the names of all the ACL2 functions to be translated to Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a worklist algorithm, which starts with @('(fn1 ... fnp)').")
   (xdoc::p
    "The iteration ends successfully when the worklist is empty;
     it ends with an error if the next function in the worklist
     either (1) has raw Lisp code and is not in the whitelist,
     or (2) has no @('unnormalized-body') property and is not primitive,
     or (3) has input or output stobjs.
     When the next function in the worklist is primitive,
     it is just removed from the worklist
     (primitive functions have no input or output stobjs).
     When the next function in the worklist is not primitive
     but it has an @('unnormalized-body') property and no raw Lisp code
     (or is in the whitelist),
     and has no input or output stobjs,
     it is added to the accumulator (unless it is already there),
     and all the functions it calls are added to the worklist,
     except for those already in the accumulator or worklist.")
   (xdoc::p
    "Before collecting the functions
     called by the next function in the worklist,
     all the calls of @(tsee mbe) in the function's unnormalized body
     are replaced with their @(':logic') parts.
     Thus, their @(':exec') parts are ignored,
     and calls to @(tsee return-last) that result from @(tsee mbe)s
     are accepted.")
   (xdoc::p
    "The returned list of function names should have no duplicates,
     but we double-check that for robustness.
     The list is in no particular order."))
  (b* (((run-when verbose$)
        (cw "~%ACL2 functions to translate to Java:~%"))
       ((er fns) (atj-fns-to-translate-aux targets$ nil verbose$ ctx state))
       ((unless (no-duplicatesp-eq fns))
        (value (raise "Internal error: ~
                       the list ~x0 of collected function names ~
                       has duplicates."
                      fns))))
    (value fns))

  :prepwork
  ((define atj-fns-to-translate-aux ((worklist symbol-listp)
                                     (current-fns symbol-listp)
                                     (verbose$ booleanp)
                                     ctx
                                     state)
     :returns (mv erp ; BOOLEANP
                  final-fns ; SYMBOL-LISTP
                  state)
     :mode :program
     :parents nil
     (b* (((when (endp worklist)) (value current-fns))
          ((cons fn worklist) worklist)
          ((when (primitivep fn))
           (atj-fns-to-translate-aux worklist current-fns verbose$ ctx state))
          ((when (and (or (member-eq fn (@ acl2::program-fns-with-raw-code))
                          (member-eq fn (@ acl2::logic-fns-with-raw-code)))
                      (not (member-eq fn *atj-allowed-raws*))))
           (er-soft+ ctx t nil "The function ~x0 has raw Lisp code ~
                                and is not in the whitelist; ~
                                therefore, code generation cannot proceed." fn))
          (body (getpropc fn 'acl2::unnormalized-body))
          ((unless body)
           (er-soft+ ctx t nil
                     "The function ~x0 has no UNNORMALIZED-BODY property ~
                      and is not an ACL2 primitive function; ~
                      therefore, code generation cannot proceed." fn))
          ((unless (no-stobjs-p fn (w state)))
           (er-soft+ ctx t nil
                     "The function ~x0 has input or output stobjs; ~
                      therefore, code generation cannot proceed." fn))
          ((run-when verbose$)
           (cw "  ~x0~%" fn))
          (current-fns (add-to-set-eq fn current-fns))
          (called-fns (all-ffn-symbs (atj-remove-mbe-exec-from-term body) nil))
          (fns-to-add-to-worklist (set-difference-eq called-fns current-fns))
          (worklist (union-eq fns-to-add-to-worklist worklist)))
       (atj-fns-to-translate-aux worklist current-fns verbose$ ctx state)))))

(define atj-gather-info ((targets$ symbol-listp) (verbose$ booleanp) ctx state)
  :returns (mv erp
               (result "A tuple @('(pkgs
                                    pkg-witness
                                    fns-to-translate)')
                        satisfying
                        @('(typed-tuplep string-listp
                                         stringp
                                         symbol-listp
                                         result)'),
                        where @('pkgs') is the list of names of
                        all known packages in chronological order,
                        @('pkg-witness') is the package witness symbol name,
                        and @('fns-to-translate') are
                        the functions to translate to Java.")
               state)
  :mode :program
  :short "Gather the information about the ACL2 environment
          needed to generate Java code."
  (b* ((pkgs (known-packages state))
       ((run-when verbose$)
        (cw "~%Known ACL2 packages:~%")
        (atj-show-pkgs pkgs))
       (pkg-witness *pkg-witness-name*)
       ((run-when verbose$)
        (cw "~%Name of the ACL2 package witness symbol:~%  ~s0~%"
            pkg-witness))
       ((er fns-to-translate)
        (atj-fns-to-translate targets$ verbose$ ctx state)))
    (value (list pkgs pkg-witness fns-to-translate)))

  :prepwork
  ((define atj-show-pkgs ((pkgs string-listp))
     :returns (nothing null)
     :parents nil
     (if (endp pkgs)
         nil
       (b* ((- (cw "  ~s0~%" (car pkgs))))
         (atj-show-pkgs (cdr pkgs)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-code-generation
  :parents (atj-implementation)
  :short "Code generation performed by ATJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate directly Java concrete syntax,
     without going through an abstraxt syntax.
     We write to the output file(s), via an ACL2 output channel.")
   (xdoc::p
    "The @('atj-gen-...') functions
     that generate Java declarations and statements
     print those declarations and statements to the output file;
     they take and return @(tsee state).
     The @('atj-gen-...') functions that generate Java expressions
     instead return those expressions as
     <see topic='@(url msg)'>strings or structured messages</see>
     that are then printed to the output file
     by the functions that generate Java statements.
     However, the functions that generate Java expressions may print,
     to the output file,
     statements to recursively build the expressions,
     returning strings or structured messages that reference
     the variables set by the printed statements.
     So the functions that generate Java expressions
     may take and return @(tsee state) as well.")
   (xdoc::p
    "To illustrate the structure of the @('atj-gen-...') functions
     just described,
     consider the generation of a Java expression to build
     the Java representation of an ACL2 @(tsee cons) pair.
     The pair may be a large binary tree,
     so we prefer not to generate a large Java expression.
     Instead, we generate
     a statement that sets a local variable to the @(tsee car),
     a statement that sets another local variable to the @(tsee cdr),
     and then a Java expression that builds the pair
     from those two variables.
     But the expressions that the two local variables are set to
     may in turn need to be built that way, recursively.
     This recursion ends when an atom is reached.
     A similar strategy is used to build
     Java representations of ACL2 terms and lambda expressions,
     which have a recursive structure analogously to @(tsee cons) pairs.")
   (xdoc::p
    "The @('atj-gen-...') functions that generate Java expressions
     keep track of the next local variable to use via a numeric index.
     For building ACL2 values,
     the Java variables @('value1'), @('value2'), etc. are used;
     for building ACL2 terms,
     the Java variables @('term1'), @('term2'), etc. are used;
     for building ACL2 lambda expressions,
     the Java variables @('lambda1'), @('lambda2'), etc. are used.
     The numeric index of the next variable to use
     is threaded through the functions.
     The variable is declared as it is used."))
  :order-subtopics t
  :default-parent t)

(defval *atj-indent-1*
  :short "Spaces from the left margin for the first level of indentation
          in the generated Java code."
  (implode (repeat 4 #\Space)))

(defval *atj-indent-2*
  :short "Spaces from the left margin for the second level of indentation
          in the generated Java code."
  (implode (repeat 8 #\Space)))

(defval *atj-indent-3*
  :short "Spaces from the left margin for the third level of indentation
          in the generated Java code."
  (implode (repeat 12 #\Space)))

(defval *atj-value-local-var*
  :short "Base name of the Java local variables used to build
          Java representations of ACL2 values."
  :long
  "<p>
   The local variables are obtained by adding numeric indices (decimal digits)
   after this name.
   </p>"
  "value"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-value-local-var*)))

(defval *atj-term-local-var*
  :short "Base name of the Java local variables used to build
          Java representations of ACL2 terms."
  :long
  "<p>
   The local variables are obtained by adding numeric indices (decimal digits)
   after this name.
   </p>"
  "term"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-term-local-var*)))

(defval *atj-lambda-local-var*
  :short "Base name of the Java local variables used to build
          Java representations of ACL2 lambda expressions."
  :long
  "<p>
   The local variables are obtained by adding numeric indices (decimal digits)
   after this name.
   </p>"
  "lambda"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-lambda-local-var*)))

(defval *atj-imports-local-var*
  :short "Name of the Java local variable used to build
          the import lists of ACL2 packages."
  "imports"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-imports-local-var*)))

(defval *atj-name-local-var*
  :short "Name of the Java local variable used to build
          the name of a function call."
  "name"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-name-local-var*)))

(defval *atj-formals-local-var*
  :short "Name of the Java local variable used to build
          the formal arguments of a function definition."
  "formals"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-formals-local-var*)))

(defval *atj-body-local-var*
  :short "Name of the Java local variable used to build
          the body of a function definition."
  "body"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-body-local-var*)))

(defval *atj-function-local-var*
  :short "Name of the Java local variable used to build
          a named function."
  "function"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-function-local-var*)))

(defval *atj-arguments-local-var*
  :short "Name of the Java local variables used to build
          the array of argument values of a function call."
  "arguments"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-arguments-local-var*)))

(defval *atj-result-acl2-local-var*
  :short "Name of the Java local variables used to build
          the result of a test calculated in ACL2 (by ATJ)."
  "resultAcl2"
  ///
  (assert-event
   (atj-string-ascii-java-identifier-p *atj-result-acl2-local-var*)))

(defval *atj-result-java-local-var*
  :short "Name of the Java local variables used to build
          the result of a test calculated in Java (by AIJ)."
  "resultJava"
  ///
  (assert-event
   (atj-string-ascii-java-identifier-p *atj-result-java-local-var*)))

(define atj-gen-set-var
  ((varbase stringp "Base name of the local variable.")
   (vartype stringp "Java type of the local variable.")
   (expression msgp "Java expression to set the variable to.")
   (next-var posp "Index of the next local variable to use.")
   (channel symbolp)
   state)
  :returns (mv (varname "A @(tsee stringp), the name of the local variable.")
               (new-next-var "A @(tsee posp), the updated variable index.")
               state)
  :mode :program
  :short "Generate Java code to set a local variable to an expression,
          for the incremental construction of
          values, terms, and lambda expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a local variable declaration
     with the given expression as initializer.")
   (xdoc::p
    "The name of the local variable to use is obtained by
     adding the next variable index to the base name.
     The index is incremented and returned.")
   (xdoc::p
    "We print the statement to the file,
     and we return the variable name."))
  (b* ((varname (str::cat varbase (natstr next-var)))
       (next-var (1+ next-var))
       ((mv & state) (fmt1! "~s0~s1 ~s2 = ~@3;~%"
                            (list (cons #\0 *atj-indent-2*)
                                  (cons #\1 vartype)
                                  (cons #\2 varname)
                                  (cons #\3 expression))
                            0 channel state nil)))
    (mv varname next-var state)))

(define atj-gen-package-name ((pkg stringp))
  :returns (java-expression msgp)
  :short "Generate Java code to build an ACL2 package name."
  (msg "Acl2PackageName.make(~x0)" pkg))

(define atj-gen-character-value ((char characterp))
  :returns (java-expression msgp)
  :short "Generate Java code to build an ACL2 character value."
  (msg "Acl2Character.make((char) ~x0)" (char-code char)))

(define atj-gen-java-string ((string stringp))
  :returns (java-expression msgp)
  :short "Generate Java code to build a Java string from an ACL2 string."
  :long
  (xdoc::topstring
   (xdoc::p
    "Often, printing an ACL2 string via the @('~x') directive
     yields a valid Java string literal.
     Examples are @('\"abc\"') or @('\"x-y @ 5.A\"').")
   (xdoc::p
    "However, if the ACL2 string includes characters like @('#\Return'),
     printing it may result in invalid Java code.
     In this case, a safe way to build a Java string is
     via a Java character array with an initializer
     consisting of the codes of the ACL2 string.")
   (xdoc::p
    "If the ACL2 string consists of only pritable ASCII characters
     (i.e. space and visible ASCII characters),
     we can safely print it.
     Otherwise, we use the array.
     The array initializer is a comma-separated sequence of hexadecimal numbers
     between curly braces.
     We take advantage of Java's concession
     of a comma at the end of the sequence
     to avoid treating the last element specially.")
   (xdoc::p
    "Note that package names
     can always be safely printed as Java string literals.
     So, for example, @(tsee atj-gen-package-name) always does that."))
  (b* ((chars (explode string)))
    (if (printable-charlist-p chars)
        (msg "~x0" string)
      (msg "new String(new char[]{~s0})"
           (implode (atj-chars-to-comma-sep-hex (explode string))))))

  :prepwork
  ((define atj-chars-to-comma-sep-hex ((chars character-listp))
     :returns (hex-comma-sep character-listp)
     :parents nil
     (if (endp chars)
         nil
       (append (list #\0 #\x)
               (natchars16 (char-code (car chars)))
               (list #\, #\Space)
               (atj-chars-to-comma-sep-hex (cdr chars)))))))

(define atj-gen-string-value ((string stringp))
  :returns (java-expression msgp)
  :short "Generate Java code to build an ACL2 string value."
  (msg "Acl2String.make(~@0)"
       (atj-gen-java-string string)))

(define atj-gen-symbol-value ((symbol symbolp))
  :returns (java-expression msgp)
  :short "Generate Java code to build an ACL2 symbol value."
  (msg "Acl2Symbol.make(~@0, ~@1)"
       (atj-gen-java-string (symbol-package-name symbol))
       (atj-gen-java-string (symbol-name symbol))))

(define atj-gen-integer-value ((integer integerp))
  :returns (java-expression msgp)
  :short "Generate Java code to build an ACL2 integer value."
  :long
  (xdoc::topstring-p
   "If the ACL2 integer is representable as a Java integer,
    we print it as a Java integer literal.
    Otherwise, if it is representable as a Java long integer,
    we print it as a Java long integer literal.
    Otherwise, we print a Java big integer
    built out of the string representation of the ACL2 integer.")
  (cond ((signed-byte-p 32 integer)
         (msg "Acl2Integer.make(~x0)" integer))
        ((signed-byte-p 64 integer)
         (msg "Acl2Integer.make(~x0L)" integer))
        ((< integer 0)
         (msg "Acl2Integer.make(new BigInteger(\"-~x0\"))" integer))
        (t (msg "Acl2Integer.make(new BigInteger(\"~x0\"))" integer))))

(define atj-gen-rational-value ((rational rationalp))
  :returns (java-expression msgp)
  :short "Generate Java code to build an ACL2 rational value."
  (msg "Acl2Rational.make(~@0, ~@1)"
       (atj-gen-integer-value (numerator rational))
       (atj-gen-integer-value (denominator rational))))

(define atj-gen-number-value ((number acl2-numberp))
  :returns (java-expression msgp)
  :short "Generate Java code to build an ACL2 number."
  (msg "Acl2Number.make(~@0, ~@1)"
       (atj-gen-rational-value (realpart number))
       (atj-gen-rational-value (imagpart number))))

(defines atj-gen-values
  :short "Generate Java code to build ACL2 values."
  :long
  (xdoc::topstring-p
   "Since ACL2 values have a recursive structure,
   these functions are mutually recursive.")

  (define atj-gen-cpair-value ((pair consp)
                               (value-next-var posp)
                               (channel symbolp)
                               state)
    :returns (mv (java-expression "A @(tsee msgp).")
                 (new-value-next-var "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-values)
    :short "Generate Java code to build an ACL2 @(tsee cons) pair value."
    :long
    (xdoc::topstring-p
     "The generated code
      builds the @(tsee car),
      sets a local variable to it,
      builds the @(tsee cdr),
      sets another local variable to it,
      and returns an expression that builds the pair
      from the two local variables.")
    (b* (((mv car-expr
              value-next-var
              state) (atj-gen-value (car pair)
                                    value-next-var
                                    channel state))
         ((mv car-var
              value-next-var
              state) (atj-gen-set-var *atj-value-local-var*
                                      "Acl2Value"
                                      car-expr
                                      value-next-var
                                      channel
                                      state))
         ((mv cdr-expr
              value-next-var
              state) (atj-gen-value (cdr pair)
                                    value-next-var
                                    channel state))
         ((mv cdr-var
              value-next-var
              state) (atj-gen-set-var *atj-value-local-var*
                                      "Acl2Value"
                                      cdr-expr
                                      value-next-var
                                      channel
                                      state)))
      (mv (msg "Acl2ConsPair.make(~s0, ~s1)" car-var cdr-var)
          value-next-var
          state)))

  (define atj-gen-value ((x "Value.")
                         (value-next-var posp)
                         (channel symbolp)
                         state)
    :returns (mv (java-expression "A @(tsee msgp).")
                 (new-value-next-var "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-values)
    :short "Generate Java code to build an ACL2 value."
    (cond ((characterp x) (mv (atj-gen-character-value x)
                              value-next-var
                              state))
          ((stringp x) (mv (atj-gen-string-value x)
                           value-next-var
                           state))
          ((symbolp x) (mv (atj-gen-symbol-value x)
                           value-next-var
                           state))
          ((integerp x) (mv (atj-gen-integer-value x)
                            value-next-var
                            state))
          ((rationalp x) (mv (atj-gen-rational-value x)
                             value-next-var
                             state))
          ((acl2-numberp x) (mv (atj-gen-number-value x)
                                value-next-var
                                state))
          ((consp x) (atj-gen-cpair-value x
                                          value-next-var
                                          channel
                                          state))
          (t (prog2$ (raise "Internal error: the value ~x0 is a bad atom." x)
                     (mv "" value-next-var state))))))

(define atj-gen-qconstant-term
  ((constant "(Unquoted) value of the ACL2 quoted constant.")
   (value-next-var posp)
   (channel symbolp)
   state)
  :returns (mv (java-expression "A @(tsee msgp).")
               (new-value-next-var "A @(tsee posp).")
               state)
  :mode :program
  :short "Generate Java code to build an ACL2 quoted constant term."
  (b* (((mv value-expr
            value-next-var
            state) (atj-gen-value constant
                                  value-next-var
                                  channel
                                  state)))
    (mv (msg "Acl2QuotedConstant.make(~@0)" value-expr)
        value-next-var
        state)))

(define atj-gen-variable-term ((symbol symbolp "The ACL2 variable."))
  :returns (java-expression msgp)
  :short "Generate Java code to build an ACL2 variable term."
  (msg "Acl2Variable.make(~@0)" (atj-gen-symbol-value symbol)))

(define atj-gen-formals-array ((symbols symbol-listp "The ACL2 formals."))
  :returns (java-expression msgp)
  :short "Generate Java code to build a new array initialized with
          the given symbols, to be used as formal arguments."
  :long
  (xdoc::topstring-p
   "In building the comma-separated sequence of the array elements,
    we take advantage of Java's concession
    of a comma at the end of the sequence
    to avoid treating the last element specially.")
  (msg "new Acl2Symbol[]{~@0}"
       (atj-gen-formals-array-aux symbols))

  :prepwork
  ((define atj-gen-formals-array-aux ((symbols symbol-listp))
     :returns (comma-separated-sequence msgp)
     :parents nil
     (if (endp symbols)
         ""
       (msg "~@0, ~@1"
            (atj-gen-symbol-value (car symbols))
            (atj-gen-formals-array-aux (cdr symbols)))))))

(define atj-gen-java-array
  ((java-expressions msg-listp "Elements of the array.")
   (type stringp "Component type of the array."))
  :returns (java-expression msgp)
  :short "Generate Java code to build a new array
          initialized with the given expressions."
  :long
  (xdoc::topstring-p
   "In building the comma-separated sequence of the array elements,
    we take advantage of Java's concession
    of a comma at the end of the sequence
    to avoid treating the last element specially.")
  (msg "new ~s0[]{~@1}"
       type
       (atj-gen-java-array-aux java-expressions))

  :prepwork
  ((define atj-gen-java-array-aux ((java-expressions msg-listp))
     :returns (comma-separated-sequence msgp)
     :parents nil
     (if (endp java-expressions)
         ""
       (msg "~@0, ~@1"
            (car java-expressions)
            (atj-gen-java-array-aux (cdr java-expressions)))))))

(defines atj-gen-terms+lambdas
  :short "Generate Java code to build ACL2 terms and lambda expressions."
  :long
  (xdoc::topstring-p
   "Since ACL2 terms and lambda expressions have a recursive structure,
    these functions are mutually recursive.")

  (define atj-gen-application-term ((function pseudo-termfnp)
                                    (arguments pseudo-term-listp)
                                    (value-next-var posp)
                                    (term-next-var posp)
                                    (lambda-next-var posp)
                                    (channel symbolp)
                                    state)
    :returns (mv (java-expression "A @(tsee msgp).")
                 (new-value-next-var "A @(tsee posp).")
                 (new-term-next-var "A @(tsee posp).")
                 (new-lambda-next-var "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-terms+lambdas)
    :short "Generate Java code to build an ACL2 application term."
    :long
    (xdoc::topstring
     (xdoc::topstring-p
      "The generated code
       builds the function (a named function or a lambda expression),
       builds the arguments,
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
    (b* (((mv function arguments)
          (if (and (eq function 'if)
                   (= (len arguments) 3)
                   (equal (first arguments) (second arguments)))
              (mv 'or (list (first arguments) (third arguments)))
            (mv function arguments)))
         ((mv function-expr
              value-next-var
              term-next-var
              lambda-next-var
              state) (if (symbolp function)
                         (b* ((symbol-expr (atj-gen-symbol-value function)))
                           (mv (msg "Acl2NamedFunction.make(~@0)" symbol-expr)
                               value-next-var
                               term-next-var
                               lambda-next-var
                               state))
                       (atj-gen-lambda (lambda-formals function)
                                       (lambda-body function)
                                       value-next-var
                                       term-next-var
                                       lambda-next-var
                                       channel
                                       state)))
         ((mv argument-exprs
              value-next-var
              term-next-var
              lambda-next-var
              state) (atj-gen-terms arguments
                                    value-next-var
                                    term-next-var
                                    lambda-next-var
                                    channel
                                    state))
         (argument-array-expr (atj-gen-java-array argument-exprs "Acl2Term"))
         (application-expr (msg "Acl2FunctionApplication.make(~@0, ~@1)"
                                function-expr
                                argument-array-expr))
         ((mv application-var
              term-next-var
              state) (atj-gen-set-var *atj-term-local-var*
                                      "Acl2Term"
                                      application-expr
                                      term-next-var
                                      channel
                                      state)))
      (mv application-var
          value-next-var
          term-next-var
          lambda-next-var
          state)))

  (define atj-gen-lambda ((formals symbol-listp)
                          (body pseudo-termp)
                          (value-next-var posp)
                          (term-next-var posp)
                          (lambda-next-var posp)
                          (channel symbolp)
                          state)
    :returns (mv (java-expression "A @(tsee msgp).")
                 (new-value-next-var "A @(tsee posp).")
                 (new-term-next-var "A @(tsee posp).")
                 (new-lambda-next-var "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-terms+lambdas)
    :short "Generate Java code to build an ACL2 lambda expression."
    :long
    (xdoc::topstring-p
     "The generated code
      puts the formals into an array,
      builds the body,
      builds the lambda expression,
      puts it to a local variable,
      and returns the local variable.")
    (b* ((formals-array-expr (atj-gen-formals-array formals))
         ((mv body-expr
              value-next-var
              term-next-var
              lambda-next-var
              state) (atj-gen-term body
                                   value-next-var
                                   term-next-var
                                   lambda-next-var
                                   channel
                                   state))
         (lambda-expr (msg "Acl2LambdaExpression.make(~@0, ~@1)"
                           formals-array-expr
                           body-expr))
         ((mv lambda-var
              lambda-next-var
              state) (atj-gen-set-var *atj-lambda-local-var*
                                      "Acl2LambdaExpression"
                                      lambda-expr
                                      lambda-next-var
                                      channel
                                      state)))
      (mv lambda-var
          value-next-var
          term-next-var
          lambda-next-var
          state)))

  (define atj-gen-term ((term pseudo-termp)
                        (value-next-var posp)
                        (term-next-var posp)
                        (lambda-next-var posp)
                        (channel symbolp)
                        state)
    :returns (mv (java-expression "A @(tsee msgp).")
                 (new-value-next-var "A @(tsee posp).")
                 (new-term-next-var "A @(tsee posp).")
                 (new-lambda-next-var "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-terms+lambdas)
    :short "Generate Java code to build an ACL2 term."
    (cond ((variablep term) (mv (atj-gen-variable-term term)
                                value-next-var
                                term-next-var
                                lambda-next-var
                                state))
          ((fquotep term) (b* (((mv expr
                                    value-next-var
                                    state)
                                (atj-gen-qconstant-term (unquote term)
                                                        value-next-var
                                                        channel
                                                        state)))
                            (mv expr
                                value-next-var
                                term-next-var
                                lambda-next-var
                                state)))
          (t (atj-gen-application-term (ffn-symb term)
                                       (fargs term)
                                       value-next-var
                                       term-next-var
                                       lambda-next-var
                                       channel
                                       state))))

  (define atj-gen-terms ((terms pseudo-term-listp)
                         (value-next-var posp)
                         (term-next-var posp)
                         (lambda-next-var posp)
                         (channel symbolp)
                         state)
    :returns (mv (java-expressions "A @(tsee msg-listp).")
                 (new-value-next-var "A @(tsee posp).")
                 (new-term-next-var "A @(tsee posp).")
                 (new-lambda-next-var "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-terms+lambdas)
    :short "Generate Java code to build a sequence of ACL2 terms."
    (if (endp terms)
        (mv nil
            value-next-var
            term-next-var
            lambda-next-var
            state)
      (b* (((mv expr
                value-next-var
                term-next-var
                lambda-next-var
                state) (atj-gen-term (car terms)
                                     value-next-var
                                     term-next-var
                                     lambda-next-var
                                     channel
                                     state))
           ((mv exprs
                value-next-var
                term-next-var
                lambda-next-var
                state) (atj-gen-terms (cdr terms)
                                      value-next-var
                                      term-next-var
                                      lambda-next-var
                                      channel
                                      state)))
        (mv (cons expr exprs)
            value-next-var
            term-next-var
            lambda-next-var
            state)))))

(define atj-gen-add-package-def-method-name ((pkg stringp))
  :returns (method-name stringp)
  :short "Name of the Java method
          to add an ACL2 package definition to the environment."
  :long
  (xdoc::topstring-p
   "We generate a private static method for each ACL2 package definition
    to add to the Java representation of the ACL2 environment.
    This function generates the name of this method,
    which has the form @('addPackageDef_...'),
    where @('...') is a sequence of pairs of hexadecimal digits
    that are the codes of the package name's characters,
    e.g. @('41434C32') for the @('\"ACL2\"') package.
    This scheme is a simple way to keep the names all distinct;
    their readability is not important because
    they are names of private methods.")
  (str::cat "addPackageDef_"
            (ubyte8s=>hexstring (string=>nats pkg))))

(define atj-gen-add-package-def-method ((pkg stringp)
                                        (verbose$ booleanp)
                                        (channel symbolp)
                                        state)
  :returns state
  :mode :program
  :short "Generate a Java method
          to add an ACL2 package definition to the environment."
  :long
  (xdoc::topstring-p
   "This is a private static method
    that contains a sequence of assignment expression statements
    to incrementally construct
    the Java list of symbols imported by the package.
    The sequence starts with a declaration of a local variable
    initialized with an empty Java list
    whose capacity is the length of the import list.
    After all the assignments, we generate a call statement
    to add the package to the environment with the calculated import list.")
  (b* (((run-when verbose$)
        (cw "  ~s0~%" pkg))
       (name (atj-gen-add-package-def-method-name pkg))
       ((mv & state) (fmt1! "~%~s0private static void ~s1() {~%"
                            (list (cons #\0 *atj-indent-1*)
                                  (cons #\1 name))
                            0 channel state nil))
       (imports (pkg-imports pkg))
       ((mv & state) (fmt1! "~s0List<Acl2Symbol> ~s1 = new ArrayList<>(~x2);~%"
                            (list (cons #\0 *atj-indent-2*)
                                  (cons #\1 *atj-imports-local-var*)
                                  (cons #\2 (len imports)))
                            0 channel state nil))
       (state (atj-gen-add-package-def-method-aux imports channel state))
       (package-name-expr (atj-gen-package-name pkg))
       ((mv & state) (fmt1! "~s0Acl2Environment.addPackageDef(~@1, ~s2);~%"
                            (list (cons #\0 *atj-indent-2*)
                                  (cons #\1 package-name-expr)
                                  (cons #\2 *atj-imports-local-var*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0}~%" (list (cons #\0 *atj-indent-1*))
                            0 channel state nil)))
    state)

  :prepwork
  ((define atj-gen-add-package-def-method-aux ((imports symbol-listp)
                                               (channel symbolp)
                                               state)
     :returns state
     :mode :program
     :parents nil
     (if (endp imports)
         state
       (b* ((symbol-expr (atj-gen-symbol-value (car imports)))
            ((mv & state) (fmt1! "~s0~s1.add(~@2);~%"
                                 (list (cons #\0 *atj-indent-2*)
                                       (cons #\1 *atj-imports-local-var*)
                                       (cons #\2 symbol-expr))
                                 0 channel state nil)))
         (atj-gen-add-package-def-method-aux (cdr imports) channel state))))))

(define atj-gen-add-package-def-methods ((pkgs string-listp)
                                         (verbose$ booleanp)
                                         (channel symbolp)
                                         state)
  :returns state
  :mode :program
  :short "Generate all the Java methods
          to add the ACL2 package definitions to the environment."
  (if (endp pkgs)
      state
    (b* ((state
          (atj-gen-add-package-def-method (car pkgs) verbose$ channel state)))
      (atj-gen-add-package-def-methods (cdr pkgs) verbose$ channel state))))

(define atj-gen-add-package-defs ((pkgs string-listp)
                                  (channel symbolp)
                                  state)
  :returns state
  :mode :program
  :short "Generate Java code
          to add the ACL2 package definitions to the environment."
  :long
  (xdoc::topstring-p
   "This is a sequence of calls to the methods
    generated by @(tsee atj-gen-add-package-def-methods).
    These calls are part of the code that
    initializes (the Java representation of) the ACL2 environment.")
  (if (endp pkgs)
      state
    (b* ((method-name (atj-gen-add-package-def-method-name (car pkgs)))
         ((mv & state) (fmt1! "~s0~s1();~%"
                              (list (cons #\0 *atj-indent-2*)
                                    (cons #\1 method-name))
                              0 channel state nil)))
      (atj-gen-add-package-defs (cdr pkgs) channel state))))

(define atj-gen-set-pkg-witness ((pkg-witness stringp)
                                 (channel symbolp)
                                 state)
  :returns state
  :mode :program
  :short "Generate Java code to set the name of the ACL2 package witness."
  :long
  (xdoc::topstring-p
   "This is a statement that is part of
    initializing (the Java representation of) the ACL2 environment.")
  (b* (((mv & state) (fmt1! "~s0Acl2Environment.setPackageWitnessName(~x1);~%"
                            (list (cons #\0 *atj-indent-2*)
                                  (cons #\1 pkg-witness))
                            0 channel state nil)))
    state))

(define atj-gen-add-function-def-method-name ((fn-to-translate symbolp))
  :returns (method-name stringp)
  :short "Name of the Java method
          to add an ACL2 function definition to the environment."
  :long
  (xdoc::topstring-p
   "We generate a private static method for each ACL2 function definition
    to add to the Java representation of the ACL2 environment.
    This function generates the name of this method,
    which has the form @('addFunctionDef_..._...'),
    wher the first @('...') is a sequence of pairs of hexadecimal digits
    that are the codes of the function symbol's package name's characters
    (e.g. @('41434C32') for the @('\"ACL2\"') package)
    and the second @('...') is a sequence of pairs of hexadecimal digits
    that are the codes of the function symbol's name's characters
    (e.g. @('4C454E') for the @(tsee len) function).
    This scheme is a simple way to keep the names all distinct;
    their readability is not important because
    they are names of private methods.")
  (str::cat
   "addFunctionDef_"
   (ubyte8s=>hexstring (string=>nats (symbol-package-name fn-to-translate)))
   "_"
   (ubyte8s=>hexstring (string=>nats (symbol-name fn-to-translate)))))

(define atj-gen-add-function-def-method ((fn-to-translate symbolp)
                                         (verbose$ booleanp)
                                         (channel symbolp)
                                         state)
  :returns state
  :mode :program
  :short "Generate a Java method
          to add an ACL2 function definition to the environment."
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
    "The indices of the next local variables
     to build the recursive structures
     (i.e. values, terms, and lambda expressions)
     are all reset to 1,
     because each function definition is built in its own method
     (thus, there are no cross-references).")
   (xdoc::p
    "All the calls of @(tsee mbe) are replaced with their @(':logic') parts
     in the function's body,
     prior to generating code.
     This is consistent with the fact that the Java counterpart of the function
     is executed ``in the logic''."))
  (b* (((run-when verbose$)
        (cw "  ~s0~%" fn-to-translate))
       (name (atj-gen-add-function-def-method-name fn-to-translate))
       ((mv & state) (fmt1! "~%~s0private static void ~s1() {~%"
                            (list (cons #\0 *atj-indent-1*)
                                  (cons #\1 name))
                            0 channel state nil))
       (formals (formals fn-to-translate (w state)))
       (body (getpropc fn-to-translate 'acl2::unnormalized-body))
       (body (atj-remove-mbe-exec-from-term body))
       (name-expr (atj-gen-symbol-value fn-to-translate))
       (formals-expr (atj-gen-formals-array formals))
       ((mv body-expr
            & & &
            state) (atj-gen-term body 1 1 1 channel state))
       ((mv & state) (fmt1! "~s0Acl2NamedFunction ~s1 = ~
                                Acl2NamedFunction.make(~@2);~%"
                            (list (cons #\0 *atj-indent-2*)
                                  (cons #\1 *atj-function-local-var*)
                                  (cons #\2 name-expr))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0Acl2Symbol[] ~s1 = ~@2;~%"
                            (list (cons #\0 *atj-indent-2*)
                                  (cons #\1 *atj-formals-local-var*)
                                  (cons #\2 formals-expr))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0Acl2Term ~s1 = ~@2;~%"
                            (list (cons #\0 *atj-indent-2*)
                                  (cons #\1 *atj-body-local-var*)
                                  (cons #\2 body-expr))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0~s1.define(~s2, ~s3);~%"
                            (list (cons #\0 *atj-indent-2*)
                                  (cons #\1 *atj-function-local-var*)
                                  (cons #\2 *atj-formals-local-var*)
                                  (cons #\3 *atj-body-local-var*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0}~%" (list (cons #\0 *atj-indent-1*))
                            0 channel state nil)))
    state))

(define atj-gen-add-function-def-methods ((fns-to-translate symbol-listp)
                                          (verbose$ booleanp)
                                          (channel symbolp)
                                          state)
  :returns state
  :mode :program
  :short "Generate all the Java methods
          to add the ACL2 function definitions to the environment."
  (if (endp fns-to-translate)
      state
    (b* ((state (atj-gen-add-function-def-method (car fns-to-translate)
                                                 verbose$
                                                 channel
                                                 state)))
      (atj-gen-add-function-def-methods (cdr fns-to-translate)
                                        verbose$
                                        channel
                                        state))))

(define atj-gen-add-function-defs ((fns-to-translate symbol-listp)
                                   (channel symbolp)
                                   state)
  :returns state
  :mode :program
  :short "Generate Java code
          to add the ACL2 function definitions to the environment."
  :long
  (xdoc::topstring-p
   "This is a sequence of calls to the methods
    generated by @(tsee atj-gen-add-function-def-methods).
    These calls are part of the code that
    initializes (the Java representation of) the ACL2 environment.")
  (if (endp fns-to-translate)
      state
    (b* ((method-name (atj-gen-add-function-def-method-name
                       (car fns-to-translate)))
         ((mv & state) (fmt1! "~s0~s1();~%"
                              (list (cons #\0 *atj-indent-2*)
                                    (cons #\1 method-name))
                              0 channel state nil)))
      (atj-gen-add-function-defs (cdr fns-to-translate) channel state))))

(define atj-gen-init-method ((pkgs string-listp)
                             (pkg-witness stringp)
                             (fns-to-translate symbol-listp)
                             (channel symbolp)
                             state)
  :returns state
  :mode :program
  :short "Generate the Java public method to initialize the ACL2 environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a public static method,
     which must be called before calling the method to call ACL2 functions,
     and also before calling the AIJ methods
     to translate between Java and ACL2 values.")
   (xdoc::p
    "If the initialization flag is cleared,
     the initialization is performed and the flag is set.
     Otherwise, an exception is thrown,
     because initialization must occur only once."))
  (b* (((mv & state) (fmt1! "~%~s0public static void initialize() {~%"
                            (list (cons #\0 *atj-indent-1*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0if (initialized)~%"
                            (list (cons #\0 *atj-indent-2*))
                            0 channel state nil))
       (exception-message "The ACL2 environment is already initialized.")
       ((mv & state) (fmt1! "~s0throw new IllegalStateException(~x1);~%"
                            (list (cons #\0 *atj-indent-3*)
                                  (cons #\1 exception-message))
                            0 channel state nil))
       (state (atj-gen-add-package-defs pkgs channel state))
       (state (atj-gen-set-pkg-witness pkg-witness channel state))
       (state (atj-gen-add-function-defs fns-to-translate channel state))
       ((mv & state) (fmt1! "~s0Acl2NamedFunction.validateAll();~%"
                            (list (cons #\0 *atj-indent-2*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0initialized = true;~%"
                            (list (cons #\0 *atj-indent-2*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0}~%"
                            (list (cons #\0 *atj-indent-1*))
                            0 channel state nil)))
    state))

(define atj-gen-call-method ((channel symbolp) state)
  :returns state
  :mode :program
  :short "Generate the Java method to call ACL2 functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a public static method,
     which provides the means for external Java code
     to call (Java representations of) ACL2 functions.")
   (xdoc::p
    "Prior to calling this method,
     the ACL2 environment initialization method must be called,
     i.e. the initialization flag must be set.
     If the flag is not set, an exception is thrown."))
  (b* (((mv & state) (fmt1! "~%~s0public static Acl2Value ~
                             call(Acl2Symbol function, ~
                                  Acl2Value[] arguments)~%"
                            (list (cons #\0 *atj-indent-1*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0throws Acl2EvaluationException {~%"
                            (list (cons #\0 *atj-indent-2*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0if (!initialized)~%"
                            (list (cons #\0 *atj-indent-2*))
                            0 channel state nil))
       (exception-message "The ACL2 environment is not initialized.")
       ((mv & state) (fmt1! "~s0throw new IllegalStateException(~x1);~%"
                            (list (cons #\0 *atj-indent-3*)
                                  (cons #\1 exception-message))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0return Acl2NamedFunction.make(function).~
                                       call(arguments);~%"
                            (list (cons #\0 *atj-indent-2*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0}~%"
                            (list (cons #\0 *atj-indent-1*))
                            0 channel state nil)))
    state))

(define atj-gen-init-field ((channel symbolp) state)
  :returns state
  :mode :program
  :short "Generate the Java field for the initialization flag."
  :long
  (xdoc::topstring-p
   "This is a private static field that is initially cleared,
    indicating that the ACL2 environment has not been initialized yet.
    The flag is set when the ACL2 environment is initialized,
    and checked to avoid re-initializing the ACL2 environment again.")
  (b* (((mv & state) (fmt1! "~%~s0private static boolean initialized = false;~%"
                            (list (cons #\0 *atj-indent-1*))
                            0 channel state nil)))
    state))

(define atj-gen-class ((pkgs string-listp)
                       (pkg-witness stringp)
                       (fns-to-translate symbol-listp)
                       (java-class$ stringp)
                       (verbose$ booleanp)
                       (channel symbolp)
                       state)
  :returns state
  :mode :program
  :short "Generate the main Java class declaration."
  :long
  (xdoc::topstring-p
   "This is a public class that contains all the generated fields and methods.
    [JLS] says that a Java implementation may require
    public classes to be in files with the same names (plus extension).
    The code that we generate satisfies this requirement.")
  (b* (((mv & state) (fmt1! "public class ~s0 {~%"
                            (list (cons #\0 java-class$))
                            0 channel state nil))
       (state (atj-gen-init-field channel state))
       ((run-when verbose$)
        (cw "~%Generating Java code for the ACL2 packages:~%"))
       (state (atj-gen-add-package-def-methods pkgs verbose$ channel state))
       ((run-when verbose$)
        (cw "~%Generating Java code for the ACL2 functions:~%"))
       (state (atj-gen-add-function-def-methods fns-to-translate
                                                verbose$ channel state))
       (state (atj-gen-init-method pkgs pkg-witness fns-to-translate
                                   channel state))
       (state (atj-gen-call-method channel state))
       ((mv & state) (fmt1! "}~%" nil 0 channel state nil)))
    state))

(define atj-gen-test-method-name ((name stringp))
  :returns (method-name stringp)
  :short "Name of the Java method to run one of the specified tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "We generate a private static method for each test
     specified by the @(':tests') input.
     This function generates the name of this method,
     which has the form @('test_...'),
     where @('...') is the name of the test.
     Since ATJ checks that the tests have unique names,
     this scheme ensures that the method names are all distinct.")
   (xdoc::p
    "The argument of this function is the name of the test."))
  (str::cat "test_" name))

(define atj-gen-test-method ((test$ atj-testp)
                             (java-class$ stringp)
                             (verbose$ booleanp)
                             (channel symbolp)
                             state)
  :returns state
  :mode :program
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
     and prints a message of success or failure.")
   (xdoc::p
    "We use an auxiliary recursive function to build the argument values.
     We initialize the local variable index for values to 1."))
  (b* (((atj-test test) test$)
       ((run-when verbose$)
        (cw "  ~s0~%" test.name))
       (method-name (atj-gen-test-method-name test.name))
       ((mv & state) (fmt1! "~%~s0private static void ~s1()~%"
                            (list (cons #\0 *atj-indent-1*)
                                  (cons #\1 method-name))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0throws Acl2EvaluationException {~%"
                            (list (cons #\0 *atj-indent-2*))
                            0 channel state nil))
       ((mv & state) (fmt1!
                      "~s0System.out.print(\"Testing \" + ~x1 + \"... \");~%"
                      (list (cons #\0 *atj-indent-2*)
                            (cons #\1 test.name))
                      0 channel state nil))
       (fn-symbol-expr (atj-gen-symbol-value test.function))
       ((mv & state) (fmt1! "~s0Acl2Symbol ~s1 = ~@2;~%"
                            (list (cons #\0 *atj-indent-2*)
                                  (cons #\1 *atj-name-local-var*)
                                  (cons #\2 fn-symbol-expr))
                            0 channel state nil))
       ((mv args-exprs value-next-var state) (atj-gen-test-method-aux
                                              test.arguments 1 channel state))
       (args-expr (atj-gen-java-array args-exprs "Acl2Value"))
       ((mv & state) (fmt1! "~s0Acl2Value[] ~s1 = ~@2;~%"
                            (list (cons #\0 *atj-indent-2*)
                                  (cons #\1 *atj-arguments-local-var*)
                                  (cons #\2 args-expr))
                            0 channel state nil))
       ((mv res-expr & state) (atj-gen-value
                               test.result value-next-var channel state))
       ((mv & state) (fmt1! "~s0Acl2Value ~s1 = ~@2;~%"
                            (list (cons #\0 *atj-indent-2*)
                                  (cons #\1 *atj-result-acl2-local-var*)
                                  (cons #\2 res-expr))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0Acl2Value ~s1 = ~s2.call(~s3, ~s4);~%"
                            (list (cons #\0 *atj-indent-2*)
                                  (cons #\1 *atj-result-java-local-var*)
                                  (cons #\2 java-class$)
                                  (cons #\3 *atj-name-local-var*)
                                  (cons #\4 *atj-arguments-local-var*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0if (~s1.equals(~s2))~%"
                            (list (cons #\0 *atj-indent-2*)
                                  (cons #\1 *atj-result-acl2-local-var*)
                                  (cons #\2 *atj-result-java-local-var*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0System.out.println(\"PASS\");~%"
                            (list (cons #\0 *atj-indent-3*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0else~%"
                            (list (cons #\0 *atj-indent-2*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0System.out.println(\"FAIL\");~%"
                            (list (cons #\0 *atj-indent-3*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0}~%" (list (cons #\0 *atj-indent-1*))
                            0 channel state nil)))
    state)

  :prepwork
  ((define atj-gen-test-method-aux ((args true-listp)
                                    (value-next-var posp)
                                    (channel symbolp)
                                    state)
     :returns (mv java-expressions ;; MSG-LISTP
                  new-value-next-var ;; POSP
                  state)
     :mode :program
     :parents nil
     (b* (((when (endp args)) (mv nil value-next-var state))
          (arg (car args))
          ((mv java-expression new-value-next-var state)
           (atj-gen-value arg value-next-var channel state))
          ((mv java-expressions new-new-value-next-var state)
           (atj-gen-test-method-aux
            (cdr args) new-value-next-var channel state)))
       (mv (cons java-expression java-expressions)
           new-new-value-next-var
           state)))))

(define atj-gen-test-methods ((tests$ atj-test-listp)
                              (java-class$ stringp)
                              (verbose$ booleanp)
                              (channel symbolp)
                              state)
  :returns state
  :mode :program
  :short "Generate all the Java methods to run the specified tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are generated only if the @(':tests') input is not @('nil')."))
  (if (endp tests$)
      state
    (b* ((state (atj-gen-test-method
                 (car tests$) java-class$ verbose$ channel state)))
      (atj-gen-test-methods (cdr tests$) java-class$ verbose$ channel state))))

(define atj-gen-run-tests ((tests$ atj-test-listp)
                           (channel symbolp)
                           state)
  :returns state
  :mode :program
  :short "Generate Java code to run the specified tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "This is a sequence of calls to the methods
     generated by @(tsee atj-gen-test-methods).
     These calls are part of the main method of the test Java class."))
  (if (endp tests$)
      state
    (b* ((method-name (atj-gen-test-method-name (atj-test->name (car tests$))))
         ((mv & state) (fmt1! "~s0~s1();~%"
                              (list (cons #\0 *atj-indent-2*)
                                    (cons #\1 method-name))
                              0 channel state nil)))
      (atj-gen-run-tests (cdr tests$) channel state))))

(define atj-gen-main-method ((tests$ atj-test-listp)
                             (java-class$ stringp)
                             (channel symbolp)
                             state)
  :returns state
  :mode :program
  :short "Generate the main method of the Java test class."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "This method initializes the ACL2 environment
     and then calls each test method."))
  (b* (((mv & state) (fmt1! "~%~s0public static void main(String[] args)~%"
                            (list (cons #\0 *atj-indent-1*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0throws Acl2EvaluationException {~%"
                            (list (cons #\0 *atj-indent-2*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0~s1.initialize();~%"
                            (list (cons #\0 *atj-indent-2*)
                                  (cons #\1 java-class$))
                            0 channel state nil))
       (state (atj-gen-run-tests tests$ channel state))
       ((mv & state) (fmt1! "~s0}~%"
                            (list (cons #\0 *atj-indent-1*))
                            0 channel state nil)))
    state))

(define atj-gen-class-test ((tests$ atj-test-listp)
                            (java-class$ stringp)
                            (verbose$ booleanp)
                            (channel symbolp)
                            state)
  :returns state
  :mode :program
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
  (b* (((mv & state) (fmt1! "~%public class ~s0Test {~%"
                            (list (cons #\0 java-class$))
                            0 channel state nil))
       ((run-when verbose$)
        (cw "~%Generating Java code for the tests:~%"))
       (state (atj-gen-test-methods tests$ java-class$ verbose$ channel state))
       (state (atj-gen-main-method tests$ java-class$ channel state))
       ((mv & state) (fmt1! "}~%" nil 0 channel state nil)))
    state))

(define atj-gen-file-header ((channel symbolp) state)
  :returns state
  :mode :program
  :short "Generate the Java file header."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now this is just a comment indicating
     the provenance of the generated file.
     It could be extended and made customizable.")
   (xdoc::p
    "This is common to the file of the main Java class
     and (if generated) to the file of the test Java class."))
  (b* (((mv & state)
        (fmt1! "// This file is automatically generated by ATJ.~%~%"
               nil 0 channel state nil)))
    state))

(define atj-gen-package-decl ((java-package$ maybe-stringp)
                              (channel symbolp)
                              state)
  :returns state
  :mode :program
  :short "Generate the Java package declaration (if any)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the package is named,
     i.e. @('java-package') is not @('nil').
     If the package is unnamed, no declaration is generated.")
   (xdoc::p
    "This is common to the file of the main Java class
     and (if generated) to the file of the test Java class."))
  (if java-package$
      (b* (((mv & state) (fmt1! "package ~s0;~%~%"
                                (list (cons #\0 java-package$))
                                0 channel state nil)))
        state)
    state))

(define atj-gen-import-decls ((channel symbolp) state)
  :returns state
  :mode :program
  :short "Generate the Java import declarations for the main file."
  :long
  (xdoc::topstring
   (xdoc::p
    "We import all the public classes
     in the Java package of AIJ.
     This way, those classes can be referenced in the generated code
     by their simple (i.e. unqualified) names.")
   (xdoc::p
    "We also import some Java library classes."))
  (b* (((mv & state) (fmt1! "import ~s0.*;~%"
                            (list (cons #\0 *atj-aij-package*))
                            0 channel state nil))
       ((mv & state) (fmt1! "import java.math.BigInteger;~%"
                            nil 0 channel state nil))
       ((mv & state) (fmt1! "import java.util.ArrayList;~%"
                            nil 0 channel state nil))
       ((mv & state) (fmt1! "import java.util.List;~%"
                            nil 0 channel state nil))
       ((mv & state) (fmt1! "~%" nil 0 channel state nil)))
    state))

(define atj-gen-import-decls-test ((channel symbolp) state)
  :returns state
  :mode :program
  :short "Generate the Java import declarations for the test file."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the @(':tests') input is not @('nil').")
   (xdoc::p
    "We import all the public classes
     in the Java package of AIJ.
     This way, those classes can be referenced in the generated code
     by their simple (i.e. unqualified) names.")
   (xdoc::p
    "We also import a Java library class."))
  (b* (((mv & state) (fmt1! "import ~s0.*;~%"
                            (list (cons #\0 *atj-aij-package*))
                            0 channel state nil))
       ((mv & state) (fmt1! "import java.math.BigInteger;~%"
                            nil 0 channel state nil))
       ((mv & state) (fmt1! "~%" nil 0 channel state nil)))
    state))

(define atj-gen-file ((java-package$ maybe-stringp)
                      (java-class$ maybe-stringp)
                      (output-file$ stringp)
                      (pkgs string-listp)
                      (pkg-witness stringp)
                      (fns-to-translate symbol-listp)
                      (verbose$ booleanp)
                      state)
  :returns (mv (erp "Always @('nil').")
               (val "Always @('nil').")
               state)
  :mode :program
  :short "Generate the main Java file."
  (b* (((mv channel state) (open-output-channel! output-file$
                                                 :character state))
       (state (atj-gen-file-header channel state))
       (state (atj-gen-package-decl java-package$ channel state))
       (state (atj-gen-import-decls channel state))
       (state (atj-gen-class pkgs pkg-witness fns-to-translate java-class$
                             verbose$ channel state))
       (state (close-output-channel channel state)))
    (value nil))
  :prepwork ((defttag :open-input-channel)))

(define atj-gen-file-test ((java-package$ maybe-stringp)
                           (java-class$ stringp)
                           (output-file-test$ stringp)
                           (tests$ atj-test-listp)
                           (verbose$ booleanp)
                           state)
  :returns (mv (erp "Always @('nil').")
               (val "Always @('nil').")
               state)
  :mode :program
  :short "Generate the test Java file."
  (b* (((mv channel state) (open-output-channel! output-file-test$
                                                 :character state))
       (state (atj-gen-file-header channel state))
       (state (atj-gen-package-decl java-package$ channel state))
       (state (atj-gen-import-decls-test channel state))
       (state (atj-gen-class-test tests$ java-class$ verbose$ channel state))
       (state (close-output-channel channel state)))
    (value nil))
  :prepwork ((defttag :open-input-channel)))

(define atj-gen-everything ((java-package$ maybe-stringp)
                            (java-class$ maybe-stringp)
                            (output-file$ stringp)
                            (output-file-test$ maybe-stringp)
                            (tests$ atj-test-listp)
                            (pkgs string-listp)
                            (pkg-witness stringp)
                            (fns-to-translate symbol-listp)
                            (verbose$ booleanp)
                            state)
  :returns (mv (erp "Always @('nil').")
               (val "Always @('nil').")
               state)
  :mode :program
  :short "Generate the Java file."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the soft and hard right margins to very large values
     to avoid line breaks in virtually all cases.
     Setting these margins to ``infinity'' is not supported.")
   (xdoc::p
    "We always generate the main Java file.
     We generated the test Java file only if @(':tests') is not @('nil')."))
  (state-global-let*
   ((acl2::fmt-soft-right-margin 100000 set-fmt-soft-right-margin)
    (acl2::fmt-hard-right-margin 100000 set-fmt-hard-right-margin))
   (b* (((er &) (atj-gen-file java-package$
                              java-class$
                              output-file$
                              pkgs
                              pkg-witness
                              fns-to-translate
                              verbose$
                              state))
        ((er &) (if tests$
                    (atj-gen-file-test java-package$
                                       java-class$
                                       output-file-test$
                                       tests$
                                       verbose$
                                       state)
                  (value :this-is-irrelevant))))
     (value nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-fn ((args true-listp) ctx state)
  :returns (mv erp
               (result "Always @('(value-triple :invisible)').")
               state)
  :mode :program
  :parents (atj-implementation)
  :short "Validate the inputs, gather information, and generate the Java file."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee atj-implementation).")
   (xdoc::p
    "Since the result of this function is passed to @(tsee make-event),
     this function must return an event form.
     By returning @('(value-triple :invisible)'),
     no return value is printed on the screen.
     A message of successful completion is printed,
     regardless of @(':verbose')."))
  (b* (((er (list targets$
                  java-package$
                  java-class
                  output-file$
                  output-file-test$
                  tests$
                  verbose$)) (atj-process-inputs args ctx state))
       ((er (list pkgs
                  pkg-witness
                  fns-to-translate)) (atj-gather-info
                                      targets$ verbose$ ctx state))
       ((er &) (atj-gen-everything java-package$
                                   java-class
                                   output-file$
                                   output-file-test$
                                   tests$
                                   pkgs
                                   pkg-witness
                                   fns-to-translate
                                   verbose$
                                   state))
       (- (if output-file-test$
              (cw "~%Generated Java files:~% ~x0~% ~x1~%"
                  output-file$ output-file-test$)
            (cw "~%Generated Java file:~%  ~x0~%" output-file$))))
    (value '(value-triple :invisible))))

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
