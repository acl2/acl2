; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

; Avoid failure for atj-gen-anumber in ACL2(r):
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
     "@('deep'),
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
     "@('apkgs') is the list of names of all the currently known ACL2 packages,
      in chronological order.")
    (xdoc::li
     "@('afns') is the list of ACL2 functions to be translated to Java.")
    (xdoc::li
     "@('afns-by-apkg') consists of @('afns'),
      plus all the ACL2 primitive functions,
      organized as an alist from ACL2 package names to
      the non-empty lists of the functions in the respective packages.
      See @(tsee atj-code-generation).")
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
     "@('jvar-var-indices') is an alist with the indices
      of the next Java local variable to use, for each ACL2 variable,
      to construct shallowly embedded ACL2 terms and lambda expressions.
      See @(tsee atj-code-generation).")
    (xdoc::li
     "@('jvar-result-index') is the index of the next Java local variable to use
      to store the results of arguments of non-strict ACL2 functions.
      See @(tsee atj-code-generation).")
    (xdoc::li
     "@('jvars') is an alist with the names
      of the current Java local variables
      that represent ACL2 variables
      when constructing shallowly embedded ACL2 terms and lambda expressions.
      See @(tsee atj-code-generation).")
    (xdoc::li
     "@('channel') is the output channel of the generated Java file(s).")
    (xdoc::li
     "@('indent-level') is the (starting) indentation level to use
      when printing Java code
      to the output channel of the generated Java file(s)."))
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

(defrule msg-listp-when-string-listp
  :parents nil
  (implies (string-listp x)
           (msg-listp x))
  :enable msg-listp)

(defines remove-mbe-exec-from-term
  :short "Turn every call @('(mbe :logic a :exec b)') in a term
          into just its @(':logic') part @('a')."
  :long
  (xdoc::topstring-p
   "In translated terms,
    these have the form @('(return-last 'acl2::mbe1-raw b a)').")

  (define remove-mbe-exec-from-term ((term pseudo-termp))
    :returns (new-term "A @(tsee pseudo-termp).")
    (b* (((when (variablep term)) term)
         ((when (fquotep term)) term)
         (fn (ffn-symb term))
         (args (fargs term))
         ((when (and (eq fn 'return-last)
                     (equal (first args) '(quote acl2::mbe1-raw))))
          (remove-mbe-exec-from-term (third args)))
         (new-fn (if (symbolp fn)
                     fn
                   (make-lambda (lambda-formals fn)
                                (remove-mbe-exec-from-term
                                 (lambda-body fn)))))
         (new-args (remove-mbe-exec-from-terms args)))
      (fcons-term new-fn new-args)))

  (define remove-mbe-exec-from-terms ((terms pseudo-term-listp))
    :returns (new-terms "A @(tsee pseudo-term-listp).")
    (b* (((when (endp terms)) nil)
         ((cons term terms) terms)
         (new-term (remove-mbe-exec-from-term term))
         (new-terms (remove-mbe-exec-from-terms terms)))
      (cons new-term new-terms))))

(define unquote-list ((list quote-listp))
  :returns (new-list true-listp)
  :verify-guards nil
  :short "Unquote all the elements of a list."
  (cond ((endp list) nil)
        (t (cons (unquote (car list))
                 (unquote-list (cdr list))))))

(define decompose-at-dots ((string stringp))
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
  (decompose-at-dots-aux (explode string) nil)

  :prepwork
  ((define decompose-at-dots-aux ((chars character-listp)
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
               (decompose-at-dots-aux chars rev-current-substrings))
           (b* ((substring (implode chars))
                (rev-final-substrings (cons substring rev-current-substrings)))
             (rev rev-final-substrings)))))
     :measure (len chars))))

(std::defalist symbol-nat-alistp (x)
  :short "Recognize alists from symbols to natural numbers."
  :key (symbolp x)
  :val (natp x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil)

(std::defalist symbol-string-alistp (x)
  :short "Recognize alists from symbols to strings."
  :key (symbolp  x)
  :val (stringp x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil)

(std::defalist string-symbols-alistp (x)
  :short "Recognize alists from strings to true lists of symbols."
  :key (stringp x)
  :val (symbol-listp x)
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t)

(define organize-fns-by-pkg ((fns symbol-listp))
  :returns (fns-by-pkg "A @(tsee string-symbols-alistp).")
  :verify-guards nil
  :short "Organize a list of function names by their packages."
  :long
  (xdoc::topstring-p
   "The result is an alist from package names (strings)
    to the non-empty lists of the function symbols
    that are in the respective packages.")
  (organize-fns-by-pkg-aux fns nil)

  :prepwork
  ((define organize-fns-by-pkg-aux ((fns symbol-listp)
                                    (acc string-symbols-alistp))
     :returns fns-by-pkg ; STRING-SYMBOLS-ALISTP
     :verify-guards nil
     :parents nil
     (b* (((when (endp fns)) acc)
          (fn (car fns))
          (pkg (symbol-package-name fn))
          (prev-fns-for-pkg (cdr (assoc-equal pkg acc))))
       (organize-fns-by-pkg-aux (cdr fns)
                                (acons pkg (cons fn prev-fns-for-pkg) acc))))))

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
  :short "Check if an ACL2 string is a valid ASCII Java identifier."
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

(define atj-string-ascii-java-package-name-p ((string stringp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Check if an ACL2 string is a valid ASCII Java package name."
  :long
  (xdoc::topstring-p
   "The string must consist of one or more ASCII Java identifiers
    separated by dots.")
  (b* ((identifiers (decompose-at-dots string)))
    (and (consp identifiers)
         (atj-string-ascii-java-identifier-listp identifiers))))

(defval *atj-aij-package*
  :short "Name of the Java package of AIJ."
  "edu.kestrel.acl2.aij"
  ///
  (assert-event (atj-string-ascii-java-package-name-p *atj-aij-package*)))

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
       ((when (equal java-package *atj-aij-package*))
        (er-soft+ ctx t nil
                  "The :JAVA-PACKAGE input ~x0 must differ from ~
                   the name of the Java package of AIJ ~x1."
                  java-package *atj-aij-package*)))
    (value nil)))

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

(std::defaggregate atj-test
  :short "Recognize a processed test specified by the @(':tests') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each test specified by the @(':tests') input
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
     and the result of the ground call @('(fn qc1 qc2 ...)')."))
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
          (args (unquote-list qcs))
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
  (list :deep
        :java-package
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
                                    deep$
                                    java-package$
                                    java-class$
                                    output-file$
                                    output-file-test$
                                    tests$
                                    verbose$)')
                        satisfying
                        @('(typed-tuplep symbol-listp
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
       (java-package (cdr (assoc-eq :java-package options)))
       (java-class (cdr (assoc-eq :java-class options)))
       (output-dir (or (cdr (assoc-eq :output-dir options)) "."))
       (tests (cdr (assoc-eq :tests options)))
       (verbose (cdr (assoc-eq :verbose options)))
       ((er &) (atj-process-targets targets ctx state))
       ((er &) (ensure-boolean$ deep "The :DEEP intput" t nil))
       ((er &) (atj-process-java-package java-package ctx state))
       ((er java-class$) (atj-process-java-class java-class ctx state))
       ((er tests$) (atj-process-tests tests targets ctx state))
       ((when (and tests$ (not deep)))
        (er-soft+ ctx t nil "The :TESTS input must be NIL ~
                             when :DEEP is (perhaps by default) NIL."))
       ((er (list output-file$
                  output-file-test$)) (atj-process-output-dir
                                       output-dir java-class$ tests$ ctx state))
       ((er &) (ensure-boolean$ verbose "The :VERBOSE input" t nil)))
    (value (list targets
                 deep
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
     "The names of all the non-primitive functions to be translated to Java,
      as determined by @('fn1'), ..., @('fnp').")))
  :order-subtopics t
  :default-parent t)

(defval *atj-allowed-raws*
  :short "ACL2 functions with raw Lisp code that are accepted by ATJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the whitelist mentioned in the documentation.")
   (xdoc::p
    "The functions in this list have no side effects
     and their execution is functionally equivalent to
     their @('unnormalized-body') property.")
   (xdoc::p
    "@(tsee return-last) is not explicitly included in this list,
     because it is only partially whitelisted,
     as explained in the documentation.
     Calls of @(tsee return-last) are handled specially in the code.")
   (xdoc::p
    "This whitelist will be extended as needed."))
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
               (fns "A @(tsee symbol-listp).")
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
                                     (acc symbol-listp)
                                     (verbose$ booleanp)
                                     ctx
                                     state)
     :returns (mv erp ; BOOLEANP
                  fns ; SYMBOL-LISTP
                  state)
     :mode :program
     :parents nil
     (b* (((when (endp worklist)) (value acc))
          ((cons fn worklist) worklist)
          ((when (primitivep fn))
           (atj-fns-to-translate-aux worklist acc verbose$ ctx state))
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
          (acc (add-to-set-eq fn acc))
          (called-fns (all-ffn-symbs (remove-mbe-exec-from-term body) nil))
          (fns-to-add-to-worklist (set-difference-eq called-fns acc))
          (worklist (union-eq fns-to-add-to-worklist worklist)))
       (atj-fns-to-translate-aux worklist acc verbose$ ctx state)))))

(define atj-gather-info ((targets$ symbol-listp) (verbose$ booleanp) ctx state)
  :returns (mv erp
               (result "A tuple @('(pkgs
                                    fns-to-translate)')
                        satisfying
                        @('(typed-tuplep string-listp
                                         symbol-listp
                                         result)'),
                        where @('pkgs') is the list of names of
                        all known packages in chronological order,
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
       ((er fns-to-translate)
        (atj-fns-to-translate targets$ verbose$ ctx state)))
    (value (list pkgs fns-to-translate)))

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
    "The @('atj-gen-...') functions
     that generate Java expressions for these recursive structures
     keep track of the next local variables to use via numeric indices
     that are threaded through the functions.
     The indices are appended to the base names for the local variables
     in order to guarantee the uniqueness of the local variables.")
   (xdoc::p
    "The @('atj-gen-deep-...') functions are used
     for the deep embedding approach.
     The @('atj-gen-shallow-...') functions are used
     for the shallow embedding approach.
     The other functions are generally used for both approaches."))
  :order-subtopics t
  :default-parent t)

(define atj-indent ((level natp))
  :returns (spaces stringp)
  :short "Spaces from the left margin for the specified level of indentation."
  :long
  (xdoc::topstring-p
   "We indent by increments of 4 spaces.")
  (implode (repeat (* 4 level) #\Space)))

(define atj-gen-comma-sep-jexprs ((exprs msg-listp))
  :returns (comma-sep-exprs msgp :hyp (msg-listp exprs))
  :short "Generate a comma-separated sequence of Java expressions."
  :long
  (xdoc::topstring-p
   "The list of expressions are passed as argument.
    This function essentially puts commas and spaces between them.")
  (cond ((endp exprs) "")
        ((endp (cdr exprs)) (car exprs))
        (t (msg "~@0, ~@1"
                (car exprs)
                (atj-gen-comma-sep-jexprs (cdr exprs))))))

(define atj-gen-jarray ((exprs msg-listp "Elements of the array.")
                        (type stringp "Component type of the array."))
  :returns (jexpr msgp)
  :short "Generate Java code to build a new array
          initialized with the given expressions."
  (msg "new ~s0[]{~@1}"
       type
       (atj-gen-comma-sep-jexprs exprs)))

(define atj-achars-to-jhexlits ((achars character-listp))
  :returns (jhexlits string-listp)
  :short "Turn a list of ACL2 characters
          into a list of Java hexadecimal literals for the character codes."
  (cond ((endp achars) nil)
        (t (cons (str::cat "0x" (str::natstr16 (char-code (car achars))))
                 (atj-achars-to-jhexlits (cdr achars))))))

(define atj-gen-jstring ((astring stringp))
  :returns (jexpr msgp)
  :short "Generate Java code to build a Java string from an ACL2 string."
  :long
  (xdoc::topstring
   (xdoc::p
    "Often, formatting an ACL2 string via the @('~x') directive
     yields a valid Java string literal.
     Examples are @('\"abc\"') or @('\"x-y @ 5.A\"').")
   (xdoc::p
    "However, if the ACL2 string includes characters like @('#\Return'),
     formatting it with @('~x') may result in invalid Java code.
     In this case, a safe way to build a Java string is
     via a Java character array with an initializer
     consisting of the codes of the ACL2 string.")
   (xdoc::p
    "If the ACL2 string consists of only pritable ASCII characters
     (i.e. space and visible ASCII characters),
     we can safely generate it with @('~x').
     Otherwise, we generate the array."))
  (b* ((achars (explode astring)))
    (if (printable-charlist-p achars)
        (msg "~x0" astring)
      (msg "new String(new char[]{~@0})"
           (atj-gen-comma-sep-jexprs (atj-achars-to-jhexlits achars))))))

(define atj-gen-jparamlist-avalues ((jparams string-listp))
  :returns (jparamlists msgp)
  :short "Generate a Java formal parameter list for ACL2 values."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a list of Java parameter names,
     this function generates a Java formal parameter list
     that associates the Java type @('Acl2Value') for ACL2 values
     to each Java parameter."))
  (cond ((endp jparams) "")
        ((endp (cdr jparams)) (msg "Acl2Value ~s0" (car jparams)))
        (t (msg "Acl2Value ~s0, ~@1"
                (car jparams)
                (atj-gen-jparamlist-avalues (cdr jparams))))))

(define atj-achar-to-jchars-id ((achar characterp) (startp booleanp))
  :returns (jchars character-listp :hyp (characterp achar))
  :short "Turn an ACL2 character into one or more Java characters
          of an ASCII Java identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "For certain purposes,
     we want to turn ACL2 symbols and package names into Java identifiers.
     ACL2 symbols may consist of arbitrary sequences of 8-bit characters,
     while Java identifiers may only contain certain Unicode characters;
     when Unicode is restricted to ASCII,
     Java identifiers are much more restricted than ACL2 symbols.
     They are also more restricted than ACL2 package names,
     although ACL2 package names have restrictions of their own
     compared to Java identifiers, notably the uppercase restriction.")
   (xdoc::p
    "If an ACL2 character (part of an ACL2 symbol or package name) is a letter,
     we keep it unchanged in forming the Java identifier.
     If the ACL2 character is a digit, we keep it unchanged
     only if it is not at the start of the Java identifier:
     this is indicated by the @('startp') flag.
     Otherwise, we turn it into an ``escape'' consisting of
     @('$') followed by two hexadecimal digits for the ASCII code of the digit.
     We use this same mapping for all the ACL2 characters
     that are neither letters nor digits,
     except for dash, which is very common in ACL2 symbols and package names,
     and which we map into an underscore in Java,
     which is allowed in Java identifiers.
     The hexadecimal digits greater than 9 are uppercase.
     Note that @('$') itself, which is valid in Java identifiers,
     is mapped to itself followed by its hex code (not just to itself)
     when it appears in the ACL2 symbol or package name."))
  (cond ((or (str::down-alpha-p achar)
             (str::up-alpha-p achar)) (list achar))
        ((and (digit-char-p achar)
              (not startp)) (list achar))
        ((eql achar #\-) (list #\_))
        (t (b* ((acode (char-code achar))
                ((mv hi-char lo-char) (acl2::ubyte8=>hexchars acode)))
             (list #\$ hi-char lo-char)))))

(define atj-achars-to-jchars-id ((achars character-listp) (startp booleanp))
  :returns (jchars character-listp :hyp (character-listp achars))
  :short "Lift @(tsee atj-achar-to-jchars-id) to lists."
  :long
  (xdoc::topstring-p
   "This is used on the sequence of characters
    that form an ACL2 symbol or package name;
    see the callers of this function for details.
    The @('startp') flag becomes @('nil') at the first recursive call,
    because after the first character
    we are no longer at the start of the Java identifier.")
  (cond ((endp achars) nil)
        (t (append (atj-achar-to-jchars-id (car achars) startp)
                   (atj-achars-to-jchars-id (cdr achars) nil)))))

(define atj-gen-jvar-decl-init
  ((var-type stringp "Java type of the local variable.")
   (var-base stringp "Base name of the local variable.")
   (var-index natp "Index of the local variable.")
   (expr msgp "Initializer of the local variable (a Java expression).")
   (indent-level natp)
   (channel symbolp)
   state)
  :returns (mv (var-name "A @(tsee stringp), the name of the local variable.")
               (new-var-index "A @(tsee natp), the updated variable index.")
               state)
  :mode :program
  :short "Generate Java code for
          a local variable declaration with an initializer."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name of the local variable to use is obtained by
     adding the next variable index after the base name.
     The index is incremented and returned.")
   (xdoc::p
    "We print the statement to the file,
     and we return the variable name."))
  (b* ((var-name (str::cat var-base (natstr var-index)))
       (new-var-index (1+ var-index))
       ((mv & state) (fmt1! "~s0~s1 ~s2 = ~@3;~%"
                            (list (cons #\0 (atj-indent indent-level))
                                  (cons #\1 var-type)
                                  (cons #\2 var-name)
                                  (cons #\3 expr))
                            0 channel state nil)))
    (mv var-name new-var-index state)))

(defval *atj-jvar-value*
  :short "Base name of the Java local variables used to build
          Java representations of ACL2 values."
  :long
  (xdoc::topstring-p
   "We start the name with a @('$') to avoid possible conflicts with
    the Java variables generated for the shallow embedding approach.")
  "$value"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-value*)))

(define atj-gen-achar ((achar characterp))
  :returns (jexpr msgp)
  :short "Generate Java code to build an ACL2 character."
  (msg "Acl2Character.make((char) ~x0)" (char-code achar)))

(define atj-gen-astring ((astring stringp))
  :returns (jexpr msgp)
  :short "Generate Java code to build an ACL2 string."
  (msg "Acl2String.make(~@0)"
       (atj-gen-jstring astring)))

(define atj-gen-asymbol ((asymbol symbolp))
  :returns (jexpr msgp)
  :short "Generate Java code to build an ACL2 symbol."
  (msg "Acl2Symbol.make(~@0, ~@1)"
       (atj-gen-jstring (symbol-package-name asymbol))
       (atj-gen-jstring (symbol-name asymbol))))

(define atj-gen-ainteger ((ainteger integerp))
  :returns (jexpr msgp)
  :short "Generate Java code to build an ACL2 integer."
  :long
  (xdoc::topstring-p
   "If the ACL2 integer is representable as a Java integer,
    we generate a Java integer literal.
    Otherwise, if it is representable as a Java long integer,
    we generate a Java long integer literal.
    Otherwise, we generate a Java big integer
    built out of the string representation of the ACL2 integer.")
  (cond ((signed-byte-p 32 ainteger)
         (msg "Acl2Integer.make(~x0)" ainteger))
        ((signed-byte-p 64 ainteger)
         (msg "Acl2Integer.make(~x0L)" ainteger))
        ((< ainteger 0)
         (msg "Acl2Integer.make(new BigInteger(\"-~x0\"))" ainteger))
        (t (msg "Acl2Integer.make(new BigInteger(\"~x0\"))" ainteger))))

(define atj-gen-arational ((arational rationalp))
  :returns (jexpr msgp)
  :short "Generate Java code to build an ACL2 rational."
  (msg "Acl2Rational.make(~@0, ~@1)"
       (atj-gen-ainteger (numerator arational))
       (atj-gen-ainteger (denominator arational))))

(define atj-gen-anumber ((anumber acl2-numberp))
  :returns (jexpr msgp)
  :short "Generate Java code to build an ACL2 number."
  (msg "Acl2Number.make(~@0, ~@1)"
       (atj-gen-arational (realpart anumber))
       (atj-gen-arational (imagpart anumber))))

(defines atj-gen-avalue
  :short "Generate Java code to build an ACL2 value."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a @(tsee cons) pair,
     the generated code
     builds the @(tsee car),
     sets a local variable to it,
     builds the @(tsee cdr),
     sets another local variable to it,
     and returns an expression that builds the pair
     from the two local variables."))

  (define atj-gen-aconspair ((aconspair consp)
                             (jvar-value-index posp)
                             (indent-level natp)
                             (channel symbolp)
                             state)
    :returns (mv jexpr ; MSGP
                 new-jvar-value-index ; POSP
                 state)
    :mode :program
    :parents nil
    (b* (((mv car-jexpr
              jvar-value-index
              state) (atj-gen-avalue (car aconspair)
                                     jvar-value-index
                                     indent-level
                                     channel
                                     state))
         ((mv car-jvar
              jvar-value-index
              state) (atj-gen-jvar-decl-init "Acl2Value"
                                             *atj-jvar-value*
                                             jvar-value-index
                                             car-jexpr
                                             indent-level
                                             channel
                                             state))
         ((mv cdr-jexpr
              jvar-value-index
              state) (atj-gen-avalue (cdr aconspair)
                                     jvar-value-index
                                     indent-level
                                     channel
                                     state))
         ((mv cdr-jvar
              jvar-value-index
              state) (atj-gen-jvar-decl-init "Acl2Value"
                                             *atj-jvar-value*
                                             jvar-value-index
                                             cdr-jexpr
                                             indent-level
                                             channel
                                             state)))
      (mv (msg "Acl2ConsPair.make(~s0, ~s1)" car-jvar cdr-jvar)
          jvar-value-index
          state)))

  (define atj-gen-avalue (avalue
                          (jvar-value-index posp)
                          (indent-level natp)
                          (channel symbolp)
                          state)
    :returns (mv jexpr ; MSGP
                 new-jvar-value-index ; POSP
                 state)
    :mode :program
    :parents nil
    (cond ((characterp avalue) (mv (atj-gen-achar avalue)
                                   jvar-value-index
                                   state))
          ((stringp avalue) (mv (atj-gen-astring avalue)
                                jvar-value-index
                                state))
          ((symbolp avalue) (mv (atj-gen-asymbol avalue)
                                jvar-value-index
                                state))
          ((integerp avalue) (mv (atj-gen-ainteger avalue)
                                 jvar-value-index
                                 state))
          ((rationalp avalue) (mv (atj-gen-arational avalue)
                                  jvar-value-index
                                  state))
          ((acl2-numberp avalue) (mv (atj-gen-anumber avalue)
                                     jvar-value-index
                                     state))
          ((consp avalue) (atj-gen-aconspair avalue
                                             jvar-value-index
                                             indent-level
                                             channel
                                             state))
          (t (prog2$ (raise "Internal error: the value ~x0 is a bad atom."
                            avalue)
                     (mv "" jvar-value-index state))))))

(define atj-gen-asymbols ((asymbols symbol-listp))
  :returns (jexprs msg-listp)
  :short "Lift @(tsee atj-gen-asymbol) to lists."
  (cond ((endp asymbols) nil)
        (t (cons (atj-gen-asymbol (car asymbols))
                 (atj-gen-asymbols (cdr asymbols))))))

(defval *atj-jvar-term*
  :short "Base name of the Java local variables used to build
          deeply embedded Java representations of ACL2 terms."
  "term"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-term*)))

(defval *atj-jvar-lambda*
  :short "Base name of the Java local variables used to build
          deeply embedded Java representations of ACL2 lambda expressions."
  "lambda"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-lambda*)))

(define atj-gen-deep-aqconst
  ((aqconst "(Unquoted) value of the ACL2 quoted constant.")
   (jvar-value-index posp)
   (indent-level natp)
   (channel symbolp)
   state)
  :returns (mv (jexpr "A @(tsee msgp).")
               (new-jvar-value-index "A @(tsee posp).")
               state)
  :mode :program
  :short "Generate Java code to build a deeply embedded ACL2 quoted constant."
  (b* (((mv value-jexpr
            jvar-value-index
            state) (atj-gen-avalue aqconst
                                   jvar-value-index
                                   indent-level
                                   channel
                                   state)))
    (mv (msg "Acl2QuotedConstant.make(~@0)" value-jexpr)
        jvar-value-index
        state)))

(define atj-gen-deep-avar ((avar symbolp "The ACL2 variable."))
  :returns (jexpr msgp)
  :short "Generate Java code to build a deeply embedded ACL2 variable."
  (msg "Acl2Variable.make(~@0)" (atj-gen-asymbol avar)))

(define atj-gen-deep-aformals ((aformals symbol-listp))
  :returns (jexpr msgp)
  :short "Generate Java code to build a deeply embedded formals parameter list
          of an ACL2 named function or lambda expression."
  :long
  (xdoc::topstring-p
   "The generated code builds an array of the formals as symbols.")
  (msg "new Acl2Symbol[]{~@0}"
       (atj-gen-comma-sep-jexprs (atj-gen-asymbols aformals))))

(defines atj-gen-deep-aterms+alambdas
  :short "Generate Java code to build
          deeply embedded ACL2 terms and lambda expressions."

  (define atj-gen-deep-afnapp ((afn pseudo-termfnp)
                               (aargs pseudo-term-listp)
                               (jvar-value-index posp)
                               (jvar-term-index posp)
                               (jvar-lambda-index posp)
                               (indent-level natp)
                               (channel symbolp)
                               state)
    :returns (mv (jexpr "A @(tsee msgp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-term-index "A @(tsee posp).")
                 (new-jvar-lambda-index "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-deep-aterms+alambdas)
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
    (b* (((mv afn aargs)
          (if (and (eq afn 'if)
                   (= (len aargs) 3)
                   (equal (first aargs) (second aargs)))
              (mv 'or (list (first aargs) (third aargs)))
            (mv afn aargs)))
         ((mv afn-jexpr
              jvar-value-index
              jvar-term-index
              jvar-lambda-index
              state) (if (symbolp afn)
                         (mv (msg "Acl2NamedFunction.make(~@0)"
                                  (atj-gen-asymbol afn))
                             jvar-value-index
                             jvar-term-index
                             jvar-lambda-index
                             state)
                       (atj-gen-deep-alambda (lambda-formals afn)
                                             (lambda-body afn)
                                             jvar-value-index
                                             jvar-term-index
                                             jvar-lambda-index
                                             indent-level
                                             channel
                                             state)))
         ((mv aarg-jexprs
              jvar-value-index
              jvar-term-index
              jvar-lambda-index
              state) (atj-gen-deep-aterms aargs
                                          jvar-value-index
                                          jvar-term-index
                                          jvar-lambda-index
                                          indent-level
                                          channel
                                          state))
         (aargs-jexpr (atj-gen-jarray aarg-jexprs "Acl2Term"))
         (afnapp-jexpr (msg "Acl2FunctionApplication.make(~@0, ~@1)"
                            afn-jexpr
                            aargs-jexpr))
         ((mv afnapp-jvar
              jvar-term-index
              state) (atj-gen-jvar-decl-init "Acl2Term"
                                             *atj-jvar-term*
                                             jvar-term-index
                                             afnapp-jexpr
                                             indent-level
                                             channel
                                             state)))
      (mv afnapp-jvar
          jvar-value-index
          jvar-term-index
          jvar-lambda-index
          state)))

  (define atj-gen-deep-alambda ((aformals symbol-listp)
                                (abody pseudo-termp)
                                (jvar-value-index posp)
                                (jvar-term-index posp)
                                (jvar-lambda-index posp)
                                (indent-level natp)
                                (channel symbolp)
                                state)
    :returns (mv (jexpr "A @(tsee msgp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-term-index "A @(tsee posp).")
                 (new-jvar-lambda-index "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-deep-aterms+alambdas)
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
    (b* ((aformals-jexpr (atj-gen-deep-aformals aformals))
         ((mv abody-jexpr
              jvar-value-index
              jvar-term-index
              jvar-lambda-index
              state) (atj-gen-deep-aterm abody
                                         jvar-value-index
                                         jvar-term-index
                                         jvar-lambda-index
                                         indent-level
                                         channel
                                         state))
         (alambda-jexpr (msg "Acl2LambdaExpression.make(~@0, ~@1)"
                             aformals-jexpr
                             abody-jexpr))
         ((mv alambda-jvar
              jvar-lambda-index
              state) (atj-gen-jvar-decl-init "Acl2LambdaExpression"
                                             *atj-jvar-lambda*
                                             jvar-lambda-index
                                             alambda-jexpr
                                             indent-level
                                             channel
                                             state)))
      (mv alambda-jvar
          jvar-value-index
          jvar-term-index
          jvar-lambda-index
          state)))

  (define atj-gen-deep-aterm ((aterm pseudo-termp)
                              (jvar-value-index posp)
                              (jvar-term-index posp)
                              (jvar-lambda-index posp)
                              (indent-level natp)
                              (channel symbolp)
                              state)
    :returns (mv (jexpr "A @(tsee msgp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-term-index "A @(tsee posp).")
                 (new-jvar-lambda-index "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-deep-aterms+alambdas)
    :short "Generate Java code to build a deeply embedded ACL2 term."
    (cond ((variablep aterm) (mv (atj-gen-deep-avar aterm)
                                 jvar-value-index
                                 jvar-term-index
                                 jvar-lambda-index
                                 state))
          ((fquotep aterm) (b* (((mv jexpr
                                     jvar-value-index
                                     state)
                                 (atj-gen-deep-aqconst (unquote aterm)
                                                       jvar-value-index
                                                       indent-level
                                                       channel
                                                       state)))
                             (mv jexpr
                                 jvar-value-index
                                 jvar-term-index
                                 jvar-lambda-index
                                 state)))
          (t (atj-gen-deep-afnapp (ffn-symb aterm)
                                  (fargs aterm)
                                  jvar-value-index
                                  jvar-term-index
                                  jvar-lambda-index
                                  indent-level
                                  channel
                                  state))))

  (define atj-gen-deep-aterms ((aterms pseudo-term-listp)
                               (jvar-value-index posp)
                               (jvar-term-index posp)
                               (jvar-lambda-index posp)
                               (indent-level natp)
                               (channel symbolp)
                               state)
    :returns (mv (jexprs "A @(tsee msg-listp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-term-index "A @(tsee posp).")
                 (new-jvar-lambda-index "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-deep-aterms+alambdas)
    :short "Lift @(tsee atj-gen-deep-aterm) to lists."
    (if (endp aterms)
        (mv nil
            jvar-value-index
            jvar-term-index
            jvar-lambda-index
            state)
      (b* (((mv jexpr
                jvar-value-index
                jvar-term-index
                jvar-lambda-index
                state) (atj-gen-deep-aterm (car aterms)
                                           jvar-value-index
                                           jvar-term-index
                                           jvar-lambda-index
                                           indent-level
                                           channel
                                           state))
           ((mv jexprs
                jvar-value-index
                jvar-term-index
                jvar-lambda-index
                state) (atj-gen-deep-aterms (cdr aterms)
                                            jvar-value-index
                                            jvar-term-index
                                            jvar-lambda-index
                                            indent-level
                                            channel
                                            state)))
        (mv (cons jexpr jexprs)
            jvar-value-index
            jvar-term-index
            jvar-lambda-index
            state)))))

(defval *atj-disallowed-shallow-jvars*
  :short "Disallowed Java variable names
          for the shallowly embedded ACL2 variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 variable is turned into a Java variable.
     The function @(tsee atj-achars-to-jchars-id) takes care of
     ensuring that only characters valid for Java identifiers are used,
     but this is not sufficient:
     a Java variable name cannot be a keyword,
     a boolean literal, or the null literal.")
   (xdoc::p
    "This constant collects these disallowed sequences of characters,
     which otherwise consist of valid Java identifier characters.
     It also includes the empty sequence,
     because an ACL2 symbol may consist of no characters,
     but a Java identifier cannot be empty."))
  (append *atj-java-keywords*
          *atj-java-boolean-literals*
          (list *atj-java-null-literal*)
          (list ""))
  ///
  (assert-event (string-listp *atj-disallowed-shallow-jvars*))
  (assert-event (no-duplicatesp-equal *atj-disallowed-shallow-jvars*)))

(define atj-gen-shallow-avar ((avar symbolp) (index natp) (curr-apkg stringp))
  :returns (jvar stringp)
  :short "Generate a shallowly embedded ACL2 variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 variable is turned into a Java variable:
     either a local variable or a method parameter.
     This function computes the name of the Java variable
     from the ACL2 variable.")
   (xdoc::p
    "Each ACL2 function is turned into a Java method,
     whose body is a shallowly embedded represented of the ACL2 function body.
     The ACL2 function body may reference the ACL2 function's parameter,
     as well as @(tsee let)-bound variables (via lambda expressions).
     Thus, the same variable name may in fact denote different variables
     in different parts of an ACL2 function body.
     Java does not allow different local variables with the same
     (in nested scopes in) the same method,
     and so we need to map equally named ACL2 variables
     in the same ACL2 function
     to differently named Java variables
     in the same Java method.
     We use numeric indices, one for each variable name,
     which is appended (as explained below) to the Java variable name
     to make it unique within the Java mehtod.")
   (xdoc::p
    "Another need for disambiguation arises because of package prefixes.
     An ACL2 variable is a symbol,
     which consists of a name and also a package name:
     two distinct variables may have the same name
     but different package names.
     However, when we append the package name and the name of the symbol,
     we have unique Java variable names.")
   (xdoc::p
    "Systematically prefixing, in the generated Java variables,
     every symbol name with the package prefix affects readability.
     In ACL2, package prefixes are normally omitted
     for symbols in the current ACL2 package.
     We do something similar for the Java variable names,
     where the notion of current package is as follows.
     As mentioned above, each ACL2 function is turned into a Java method:
     this method is inside a Java class whose name is derived from
     the ACL2 package name of the function name:
     thus, the ``current package'' in this context is
     the one of the function name.
     This is the @('curr-apkg') parameter of this code generation function.")
   (xdoc::p
    "Given an ACL2 variable (i.e. symbol)
     with name @('name') and package name @('pname'),
     in general the generated Java variable name is
     @('<pname>$$$<name>$$<index>'),
     where @('<pname>') and @('<name>') are representations of the ACL2 names
     that are valid for Java identifiers,
     and @('<index>') is a decimal representation of the numeric index.
     If @('pname') is the same as the current package, we omit @('<pname>$$$').
     If the index is 0, we omit @('$$<index>'),
     so that if there is just one variable with a certain name,
     since we start with index 0, no index is added to the name.
     Thus there are a few combinations possible with these three parts;
     the use of triple and double @('$') characters guaranteee
     that there is no confusion with the @('$hh') escapes
     where @('hh') is the hex code of an ACL2 character
     that is not valid for a Java identifier.
     Furthermore, if the resulting variable name if just @('<name>')
     and happens to be a Java keyword or Java literal or empty,
     we add a single @('$') at the end, which again is unambiguous.")
   (xdoc::p
    "This is a simple scheme to keep names unique,
     but we may improve it to generate more readable names.")
   (xdoc::p
    "We call @(tsee atj-achars-to-jchars-id) to create
     @('<pname') and @('<name>') from @('pname') and @('name').
     If there is a package prefix, the @('startp') flag is @('t')
     only for @('pname'), but not for @('name'),
     because @('<name>') is not the start of the Java identifier.
     Otherwise, @('startp') is @('t') for @('name')
     if there is no package prefix."))
  (b* ((apkg (symbol-package-name avar))
       (pname$$$-jchars (if (equal apkg curr-apkg)
                            nil
                          (append (atj-achars-to-jchars-id (explode apkg) t)
                                  (list #\$ #\$ #\$))))
       (name-jchars (atj-achars-to-jchars-id (explode (symbol-name avar))
                                             (endp pname$$$-jchars)))
       ($$index-jchars (if (= index 0)
                           nil
                         (append (list #\$ #\$)
                                 (str::natchars index))))
       (jchars (append pname$$$-jchars name-jchars $$index-jchars))
       (jvar (implode jchars))
       (jvar (if (member-equal jvar *atj-disallowed-shallow-jvars*)
                 (str::cat jvar "$")
               jvar)))
    jvar))

(define atj-gen-shallow-avars ((avars symbol-listp)
                               (jvar-var-indices symbol-nat-alistp)
                               (curr-apkg stringp))
  :returns (mv (jvars "A @(tsee symbol-string-alistp).")
               (new-jvar-var-indices "A @(tsee symbol-nat-alistp)."))
  :verify-guards nil
  :short "Generate a sequence of shallowly embedded ACL2 variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-gen-shallow-avar),
     the shallowly embedded ACL2 variables are made unique via indices.
     There is an independent index for each ACL2 variable,
     so we use an alist from symbols to natural numbers
     to keep track of these indices.
     This alist is threaded through the code generation functions.")
   (xdoc::p
    "In ACL2, a variable is ``introduced''
     as a formal parameter of a function or lambda expression,
     and then referenced in the body of the function or lambda expression.
     The choice and use of the index must be done at this introduction time,
     and not at every reference to the variable after its introduction.
     Thus, in the shallow embedding approach,
     when we encounter the formals of a function or lambda expression,
     we generate the Java variable names for these ACL2 variables,
     using the current indices, and update and return the indices.
     This code generation function does that,
     and returns the generated Java variables as an alist
     from the ACL2 variables (symbols) to the Java variables (strings).")
   (xdoc::p
    "Each ACL2 variable in the list is processed as follows.
     If it has no index in the alist of indices,
     it has index 0,
     and the alist is extended to associate 1 (the next index) to the symbol.
     Otherwise, the index in the alist is used,
     and the alist is updated with the next index."))
  (b* (((when (endp avars)) (mv nil jvar-var-indices))
       (avar (car avars))
       (avar+index (assoc-eq avar jvar-var-indices))
       (index (if avar+index (cdr avar+index) 0))
       (jvar-var-indices (acons avar (1+ index) jvar-var-indices))
       ((mv jvars jvar-var-indices) (atj-gen-shallow-avars (cdr avars)
                                                           jvar-var-indices
                                                           curr-apkg)))
    (mv (acons avar (atj-gen-shallow-avar avar index curr-apkg) jvars)
        jvar-var-indices)))

(defval *atj-aij-class-names*
  :short "Names of the Java classes that form AIJ."
  (list "Acl2Character"
        "Acl2ComplexRational"
        "Acl2ConsPair"
        "Acl2DefinedFunction"
        "Acl2Environment"
        "Acl2EvaluationException"
        "Acl2Function"
        "Acl2FunctionApplication"
        "Acl2Integer"
        "Acl2LambdaExpression"
        "Acl2NamedFunction"
        "Acl2NativeFunction"
        "Acl2Number"
        "Acl2PackageName"
        "Acl2QuotedConstant"
        "Acl2Ratio"
        "Acl2Rational"
        "Acl2String"
        "Acl2Symbol"
        "Acl2Term"
        "Acl2Value"
        "Acl2Variable")
  ///
  (assert-event (string-listp *atj-aij-class-names*))
  (assert-event (no-duplicatesp-equal *atj-aij-class-names*)))

(defval *atj-disallowed-shallow-jclasses*
  :short "Disallowed Java class names
          for the shallowly embedded ACL2 packages."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     a Java class is generated for each ACL2 package
     that includes ACL2 functions for which we generate Java code.
     Each ACL2 function is turned into a Java method in that Java class.")
   (xdoc::p
    "The name of the Java class is obtained from the name of the ACL2 package,
     but since the generated Java code imports some classes
     from other Java packages,
     we need to make sure that the Java class name for an ACL2 package
     does not conflict with any of the imported classes.")
   (xdoc::p
    "The generated Java code imports all the classes
     in the Java package of AIJ, as well as some other Java library classes.
     This constant collects all of these.")
   (xdoc::p
    "We also disallow Java keywords, boolean literals, and null literal,
     which are not valid Java identiers.
     There is no need to exclude the empty string explicitly,
     because ACL2 package names are never empty
     and thus they never result in the empty string."))
  (append *atj-java-keywords*
          *atj-java-boolean-literals*
          (list *atj-java-null-literal*)
          *atj-aij-class-names*
          (list "BigInteger"
                "ArrayList"
                "List"))
  ///
  (assert-event (string-listp *atj-disallowed-shallow-jclasses*))
  (assert-event (no-duplicatesp-equal *atj-disallowed-shallow-jclasses*)))

(define atj-gen-shallow-apkgname ((apkg stringp) (java-class$ stringp))
  :returns (jclass stringp)
  :short "Generate a shallowly embedded ACL2 package name."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     a Java class is generated for each ACL2 package
     that includes ACL2 functions that we generate Java code for.
     Each ACL2 function is turned into a Java method in that Java class.")
   (xdoc::p
    "The name of the Java class for the ACL2 package
     is obtained by turning the ACL2 package name
     into a valid Java identifier,
     in the same way as done for shallowly embedded Java variables.
     The resulting Java class name
     must not be a keyword, a boolean or null literal,
     or any of the imported Java classes
     (see @(tsee *atj-disallowed-shallow-jclasses*)).
     We also ensure that is is distinct from the main class generated.
     If the candidate Java class name is one of these,
     we add a @('$') at the end."))
  (b* ((jchars (atj-achars-to-jchars-id (explode apkg) t))
       (jstring (implode jchars))
       (jstring (if (or (member-equal jstring *atj-disallowed-shallow-jclasses*)
                        (equal jstring java-class$))
                    (str::cat jstring "$")
                  jstring)))
    jstring))

(defval *atj-disallowed-shallow-jmethods*
  :short "Disallowed Java method names
          for the shallowly embedded ACL2 functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     ACL2 function names are turned into Java method names
     that must be valid identifiers.
     The same character mapping used for ACL2 variables and package names
     is used for ACL2 function names,
     but the result must be a valid Java identifier,
     which means that it must not be
     a Java keyword, boolean or null literal, or empty.")
   (xdoc::p
    "This constant collects these disallowed names."))
  (append *atj-java-keywords*
          *atj-java-boolean-literals*
          (list *atj-java-null-literal*)
          (list ""))
  ///
  (assert-event (string-listp *atj-disallowed-shallow-jmethods*))
  (assert-event (no-duplicatesp-equal *atj-disallowed-shallow-jmethods*)))

(define atj-gen-shallow-afnname ((afn symbolp) (curr-apkg stringp))
  :returns (jmeth stringp)
  :short "Generate a shallowly embedded ACL2 function name."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 function is represented as a Java method.
     The Java methods for all the ACL2 functions that are translated to Java
     are partitioned by ACL2 packages:
     there is a Java class for each ACL2 package,
     and the Java method for each ACL2 function
     is in the Java class corresponding to the ACL2 package of the function.")
   (xdoc::p
    "These are all static methods, which can therefore be referenced as
     @('<jclass>.<jmethod>') in Java code,
     not dissmilarly to @('<apkg>::<afn>') in ACL2.
     However, inside @('<jclass>'), it suffices to use @('<jmethod>'),
     which is more readable.
     Thus, somewhat analogously to @(tsee atj-gen-shallow-avar),
     we prepend the Java class name to the Java method name
     if and only if the current ACL2 package (the @('curr-apkg') argument)
     differs from the ACL2 function's package.")
   (xdoc::p
    "The Java class name @('<jclass>') is generated
     via @(tsee atj-gen-shallow-apkgname).
     The method name is generated using the same character mapping
     used for shallowly embedded ACL2 variables and package names.
     We avoid Java keyword, boolean and null literals,
     and the empty string,
     by appending a @('$') at their end if they come up."))
  (b* ((apkg (symbol-package-name afn))
       (jclass.-jchars (if (equal apkg curr-apkg)
                           nil
                         (append (atj-achars-to-jchars-id (explode apkg) t)
                                 (list #\.))))
       (jmethod-jchars (atj-achars-to-jchars-id (explode (symbol-name afn)) t))
       (jmethod-jchars (if (member-equal jmethod-jchars
                                         *atj-disallowed-shallow-jmethods*)
                           (rcons #\$ jmethod-jchars)
                         jmethod-jchars))
       (jchars (append jclass.-jchars jmethod-jchars))
       (jstring (implode jchars)))
    jstring))

(define atj-gen-shallow-let-bindings ((avars symbol-listp)
                                      (jexprs msg-listp)
                                      (jvars symbol-string-alistp)
                                      (indent-level natp)
                                      (channel symbolp)
                                      state)
  :guard (and (= (len jexprs) (len avars))
              (subsetp-eq avars (strip-cars jvars)))
  :returns state
  :mode :program
  :short "Generate shallowly embedded ACL2 @(tsee let) bindings."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     ACL2 lambda expressions (i.e. @(tsee let)s)
     are handled by introducing Java local variables
     for the formal parameters of the lambda expression
     and assigning to them the Java expressions
     generated from the actual parameters of the lambda expression.
     This function generates these bindings,
     given the ACL2 variables that are the formal arguments
     and the Java expressions to assign to them.")
   (xdoc::p
    "The names for the local variables
     are generated by @(tsee atj-gen-shallow-avars)
     prior to calling this function,
     and thus the names of the Java local variables
     are stored in the @('jvars') alist."))
  (b* (((when (endp avars)) state)
       (avar (car avars))
       (jexpr (car jexprs))
       (jvar (cdr (assoc-eq avar jvars)))
       ((mv & state) (fmt1! "~s0Acl2Value ~s1 = ~@2;~%"
                            (list (cons #\0 (atj-indent indent-level))
                                  (cons #\1 jvar)
                                  (cons #\2 jexpr))
                            0 channel state nil)))
    (atj-gen-shallow-let-bindings (cdr avars)
                                  (cdr jexprs)
                                  jvars
                                  indent-level
                                  channel
                                  state)))

(defval *atj-jvar-result*
  :short "Base name of the Java local variables used to store
          the results of arguments of non-strict ACL2 functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Normally, in the shallow embedding approach,
     the actual arguments of an ACL2 function or lambda expression
     are calculated by the generated Java code,
     and then the (shallowly embedded) ACL2 function or lambda expression
     is called on them.
     For the non-strict function @(tsee if)
     and the non-strict ``pseudo-function'' @('or')
     (see the documentation of AIJ for details on the latter),
     the generated Java code follows a different strategy,
     in order to realize the required non-strictness.")
   (xdoc::p
    "This strategy involves generating Java local variables
     to store results of arguments of non-strict ACL2 functions.
     This constant is the base name to use for these Java local variables;
     indices are appended to them as neede, as with other recursive structures
     (note that non-strict ACL2 functions may be in fact nested).
     The fact that it starts with a @('$')
     and that the two subsequent characters @('r') and @('e')
     are not hexadecimal digits,
     means that this name (possibly with an index after it)
     will be always distinct from the names of the variables
     generated by @(tsee atj-gen-shallow-avar)."))
  "$result"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-result*)))

(defines atj-gen-shallow-aterms+alambdas
  :short "Generate shallowly embedded ACL2 terms and lambda expressions."

  (define atj-gen-shallow-aifapp ((atest pseudo-termp)
                                  (athen pseudo-termp)
                                  (aelse pseudo-termp)
                                  (jvars symbol-string-alistp)
                                  (jvar-var-indices symbol-nat-alistp)
                                  (jvar-value-index posp)
                                  (jvar-result-index posp)
                                  (curr-pkg stringp)
                                  (indent-level natp)
                                  (channel symbolp)
                                  state)
    :returns (mv (jexpr "A @(tsee msgp).")
                 (new-jvar-var-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Generate a shallowly embedded ACL2 @(tsee if) application."
    :long
    (xdoc::topstring
     (xdoc::p
      "Consider a call @('(if a b c)').
       If the Java code generated for @('a')
       consists of the statements @('<a-jstmts>') and expression @('<a-jexpr>'),
       and similarly for @('b') and @('c'),
       we generate the Java statements")
     (xdoc::codeblock
      "<a-stmts>"
      "Acl2Value <result> = null;"
      "if (Acl2Symbol.NIL.equals(<a-expr>)) {"
      "    <c-stmts>"
      "    <result> = <c-expr>;"
      "} else {"
      "    <b-stmts>"
      "    <result> = <b-expr>;"
      "}")
     (xdoc::p
      "and the Java expression @('<result>'),
       where @('<result>') consists of
       @(tsee *atj-jvar-result*) followed by a numeric index.")
     (xdoc::p
      "In other words, we first compute the test
       and create a local variable to store the final result.
       Based on the test, we execute either branch (non-strictness),
       storing the result into the variable."))
    (b* (((mv jtest
              jvar-var-indices
              jvar-value-index
              jvar-result-index
              state) (atj-gen-shallow-aterm atest
                                            jvars
                                            jvar-var-indices
                                            jvar-value-index
                                            jvar-result-index
                                            curr-pkg
                                            indent-level
                                            channel
                                            state))
         ((mv jvar-result jvar-result-index state)
          (atj-gen-jvar-decl-init "Acl2Value"
                                  *atj-jvar-result*
                                  jvar-result-index
                                  "null"
                                  indent-level
                                  channel
                                  state))
         ((mv & state) (fmt1! "~s0if (Acl2Symbol.NIL.equals(~@1)) {~%"
                              (list (cons #\0 (atj-indent indent-level))
                                    (cons #\1 jtest))
                              0 channel state nil))
         ((mv jelse
              jvar-var-indices
              jvar-value-index
              jvar-result-index
              state) (atj-gen-shallow-aterm aelse
                                            jvars
                                            jvar-var-indices
                                            jvar-value-index
                                            jvar-result-index
                                            curr-pkg
                                            (1+ indent-level)
                                            channel
                                            state))
         ((mv & state) (fmt1! "~s0~s1 = ~@2;~%"
                              (list (cons #\0 (atj-indent (1+ indent-level)))
                                    (cons #\1 jvar-result)
                                    (cons #\2 jelse))
                              0 channel state nil))
         ((mv & state) (fmt1! "~s0} else {~%"
                              (list (cons #\0 (atj-indent indent-level)))
                              0 channel state nil))
         ((mv jthen
              jvar-var-indices
              jvar-value-index
              jvar-result-index
              state) (atj-gen-shallow-aterm athen
                                            jvars
                                            jvar-var-indices
                                            jvar-value-index
                                            jvar-result-index
                                            curr-pkg
                                            (1+ indent-level)
                                            channel
                                            state))
         ((mv & state) (fmt1! "~s0~s1 = ~@2;~%"
                              (list (cons #\0 (atj-indent (1+ indent-level)))
                                    (cons #\1 jvar-result)
                                    (cons #\2 jthen))
                              0 channel state nil))
         ((mv & state) (fmt1! "~s0}~%"
                              (list (cons #\0 (atj-indent indent-level)))
                              0 channel state nil)))
      (mv jvar-result
          jvar-var-indices
          jvar-value-index
          jvar-result-index
          state)))

  (define atj-gen-shallow-aorapp ((afirst pseudo-termp)
                                  (asecond pseudo-termp)
                                  (jvars symbol-string-alistp)
                                  (jvar-var-indices symbol-nat-alistp)
                                  (jvar-value-index posp)
                                  (jvar-result-index posp)
                                  (curr-pkg stringp)
                                  (indent-level natp)
                                  (channel symbolp)
                                  state)
    :returns (mv (jexpr "A @(tsee msgp).")
                 (new-jvar-var-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Generate a shallowly embedded ACL2 @('or') application."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is for the @('or') ACL2 ``pseudo-function''
       (see the AIJ documentation for details).
       We treat @('(or a b)') non-strictly like @('(if a a b)'),
       but we avoid calculating @('a') twice.
       Similarly to how we treat @(tsee if),
       we generate the Java statements")
     (xdoc::codeblock
      "<a-stmts>"
      "Acl2Value <result> = null;"
      "if (Acl2Symbol.NIL.equals(<a-expr>)) {"
      "    <b-stmts>"
      "    <result> = <b-expr>;"
      "} else {"
      "    <result> = <a-expr>;"
      "}")
     (xdoc::p
      "and the Java expression @('<result>')."))
    (b* (((mv jfirst
              jvar-var-indices
              jvar-value-index
              jvar-result-index
              state) (atj-gen-shallow-aterm afirst
                                            jvars
                                            jvar-var-indices
                                            jvar-value-index
                                            jvar-result-index
                                            curr-pkg
                                            indent-level
                                            channel
                                            state))
         ((mv jvar-result jvar-result-index state)
          (atj-gen-jvar-decl-init "Acl2Value"
                                  *atj-jvar-result*
                                  jvar-result-index
                                  "null"
                                  indent-level
                                  channel
                                  state))
         ((mv & state) (fmt1! "~s0if (Acl2Symbol.NIL.equals(~@1)) {~%"
                              (list (cons #\0 (atj-indent indent-level))
                                    (cons #\1 jfirst))
                              0 channel state nil))
         ((mv jsecond
              jvar-var-indices
              jvar-value-index
              jvar-result-index
              state) (atj-gen-shallow-aterm asecond
                                            jvars
                                            jvar-var-indices
                                            jvar-value-index
                                            jvar-result-index
                                            curr-pkg
                                            (1+ indent-level)
                                            channel
                                            state))
         ((mv & state) (fmt1! "~s0~s1 = ~@2;~%"
                              (list (cons #\0 (atj-indent (1+ indent-level)))
                                    (cons #\1 jvar-result)
                                    (cons #\2 jsecond))
                              0 channel state nil))
         ((mv & state) (fmt1! "~s0} else {~%"
                              (list (cons #\0 (atj-indent indent-level)))
                              0 channel state nil))
         ((mv & state) (fmt1! "~s0~s1 = ~@2;~%"
                              (list (cons #\0 (atj-indent (1+ indent-level)))
                                    (cons #\1 jvar-result)
                                    (cons #\2 jfirst))
                              0 channel state nil))
         ((mv & state) (fmt1! "~s0}~%"
                              (list (cons #\0 (atj-indent indent-level)))
                              0 channel state nil)))
      (mv jvar-result
          jvar-var-indices
          jvar-value-index
          jvar-result-index
          state)))

  (define atj-gen-shallow-afnapp ((afn pseudo-termfnp)
                                  (aargs pseudo-term-listp)
                                  (jvars symbol-string-alistp)
                                  (jvar-var-indices symbol-nat-alistp)
                                  (jvar-value-index posp)
                                  (jvar-result-index posp)
                                  (curr-pkg stringp)
                                  (indent-level natp)
                                  (channel symbolp)
                                  state)
    :returns (mv (jexpr "A @(tsee msgp).")
                 (new-jvar-var-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Generate a shallowly embedded ACL2 function application."
    :long
    (xdoc::topstring
     (xdoc::topstring
      "Terms of the form @('(if a a b)') are treated as @('(or a b)'),
       via @(tsee atj-gen-shallow-aorapp), non-strictly.
       Other @(tsee if) calls are treated via @(tsee atj-gen-shallow-aifapp).")
     (xdoc::p
      "For calls of other ACL2 named functions, which are strict,
       we generate Java code to compute all the actual arguments,
       and we generate a call of the method that corresponds to
       the ACL2 function.")
     (xdoc::p
      "For calls of an ACL2 lambda expression,
       we also compute all the actual arguments
       (lambda expressions are strict too),
       and then use a separate code generation function
       for the lambda expression (applied to the computed arguments)."))
    (b* (((when (eq afn 'if))
          (b* ((afirst (first aargs))
               (asecond (second aargs))
               (athird (third aargs)))
            (if (equal afirst asecond)
                (atj-gen-shallow-aorapp afirst
                                        asecond
                                        jvars
                                        jvar-var-indices
                                        jvar-value-index
                                        jvar-result-index
                                        curr-pkg
                                        indent-level
                                        channel
                                        state)
              (atj-gen-shallow-aifapp afirst
                                      asecond
                                      athird
                                      jvars
                                      jvar-var-indices
                                      jvar-value-index
                                      jvar-result-index
                                      curr-pkg
                                      indent-level
                                      channel
                                      state))))
         ((mv jargs
              jvar-var-indices
              jvar-value-index
              jvar-result-index
              state) (atj-gen-shallow-aterms aargs
                                             jvars
                                             jvar-var-indices
                                             jvar-value-index
                                             jvar-result-index
                                             curr-pkg
                                             indent-level
                                             channel
                                             state))
         ((when (symbolp afn))
          (mv (msg "~s0(~@1)"
                   (atj-gen-shallow-afnname afn curr-pkg)
                   (atj-gen-comma-sep-jexprs jargs))
              jvar-var-indices
              jvar-value-index
              jvar-result-index
              state)))
      (atj-gen-shallow-alambda (lambda-formals afn)
                               (lambda-body afn)
                               jargs
                               jvar-var-indices
                               jvar-value-index
                               jvar-result-index
                               curr-pkg
                               indent-level
                               channel
                               state)))

  (define atj-gen-shallow-alambda ((aformals symbol-listp)
                                   (abody pseudo-termp)
                                   (jargs msg-listp)
                                   (jvar-var-indices symbol-nat-alistp)
                                   (jvar-value-index posp)
                                   (jvar-result-index posp)
                                   (curr-pkg stringp)
                                   (indent-level natp)
                                   (channel symbolp)
                                   state)
    :guard (= (len jargs) (len aformals))
    :returns (mv (jexpr "A @(tsee msgp).")
                 (new-jvar-var-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Generate a shallowly embedded ACL2 lambda expression,
            applied to given Java expressions as arguments."
    :long
    (xdoc::topstring
     (xdoc::p
      "Since a lambda expression introduces new ACL2 variables,
       we first generate new Java local variables
       for the ACL2 variables that form the formal parameters,
       producing a new @('jvars') alist
       and updating the @('jvar-var-indices') alist.")
     (xdoc::p
      "Then we assign to these Java local variables
       the Java expressions for the actual arguments,
       as in @(tsee let) bindings.")
     (xdoc::p
      "Finally, we generate Java code
       for the body of the lambda expression."))
    (b* (((mv jvars jvar-var-indices) (atj-gen-shallow-avars aformals
                                                             jvar-var-indices
                                                             curr-pkg))
         (state (atj-gen-shallow-let-bindings aformals
                                              jargs
                                              jvars
                                              indent-level
                                              channel
                                              state)))
      (atj-gen-shallow-aterm abody
                             jvars
                             jvar-var-indices
                             jvar-value-index
                             jvar-result-index
                             curr-pkg
                             indent-level
                             channel
                             state)))

  (define atj-gen-shallow-aterm ((aterm pseudo-termp)
                                 (jvars symbol-string-alistp)
                                 (jvar-var-indices symbol-nat-alistp)
                                 (jvar-value-index posp)
                                 (jvar-result-index posp)
                                 (curr-pkg stringp)
                                 (indent-level natp)
                                 (channel symbolp)
                                 state)
    :returns (mv (jexpr "A @(tsee msgp).")
                 (new-jvar-var-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Generate a shallowly embedded ACL2 term."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the ACL2 term is a variable,
       it must be in the @('jvar') alist,
       so we just look it up there.")
     (xdoc::p
      "If the ACL2 term is a quoted constant,
       we represent it as its value.
       Note that the Java variables with base name @(tsee *atj-jvar-value*),
       used to construct ACL2 values,
       never conflicts with the Java variables
       with base name @(tsee *atj-jvar-result*)
       or with the shallowly embedded ACL2 variables."))
    (cond ((variablep aterm) (mv (cdr (assoc-eq aterm jvars))
                                 jvar-var-indices
                                 jvar-value-index
                                 jvar-result-index
                                 state))
          ((fquotep aterm) (b* (((mv jexpr jvar-value-index state)
                                 (atj-gen-avalue (unquote aterm)
                                                 jvar-value-index
                                                 indent-level
                                                 channel
                                                 state)))
                             (mv jexpr
                                 jvar-var-indices
                                 jvar-value-index
                                 jvar-result-index
                                 state)))
          (t (atj-gen-shallow-afnapp (ffn-symb aterm)
                                     (fargs aterm)
                                     jvars
                                     jvar-var-indices
                                     jvar-value-index
                                     jvar-result-index
                                     curr-pkg
                                     indent-level
                                     channel
                                     state))))

  (define atj-gen-shallow-aterms ((aterms pseudo-term-listp)
                                  (jvars symbol-string-alistp)
                                  (jvar-var-indices symbol-nat-alistp)
                                  (jvar-value-index posp)
                                  (jvar-result-index posp)
                                  (curr-pkg stringp)
                                  (indent-level natp)
                                  (channel symbolp)
                                  state)
    :returns (mv (jexprs "A @(tsee msg-listp).")
                 (new-jvar-var-indices "A @(tsee symbol-nat-alistp).")
                 (new-jvar-value-index "A @(tsee posp).")
                 (new-jvar-result-index "A @(tsee posp).")
                 state)
    :mode :program
    :parents (atj-code-generation atj-gen-shallow-aterms+alambdas)
    :short "Lift @(tsee atj-gen-shallow-aterm) to lists."
    (if (endp aterms)
        (mv nil jvar-var-indices jvar-value-index jvar-result-index state)
      (b* (((mv jexpr
                jvar-var-indices
                jvar-value-index
                jvar-result-index
                state) (atj-gen-shallow-aterm (car aterms)
                                              jvars
                                              jvar-var-indices
                                              jvar-value-index
                                              jvar-result-index
                                              curr-pkg
                                              indent-level
                                              channel
                                              state))
           ((mv jexprs
                jvar-var-indices
                jvar-value-index
                jvar-result-index
                state) (atj-gen-shallow-aterms (cdr aterms)
                                               jvars
                                               jvar-var-indices
                                               jvar-value-index
                                               jvar-result-index
                                               curr-pkg
                                               indent-level
                                               channel
                                               state)))
        (mv (cons jexpr jexprs)
            jvar-var-indices
            jvar-value-index
            jvar-result-index
            state)))))

(define atj-gen-apkg-jmethod-name ((apkg stringp))
  :returns (method-name stringp)
  :short "Name of the Java method
          that adds an ACL2 package definition to the environment."
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
            (ubyte8s=>hexstring (string=>nats apkg))))

(define atj-gen-apkg-name ((apkg stringp))
  :returns (jexpr msgp)
  :short "Generate Java code to build an ACL2 package name."
  :long
  (xdoc::topstring-p
   "Note that package names
    can always be safely generated as Java string literals.")
  (msg "Acl2PackageName.make(~x0)" apkg))

(defval *atj-jvar-imports*
  :short "Name of the Java local variable used to build
          the import lists of ACL2 packages."
  "imports"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-imports*)))

(define atj-gen-apkg-jmethod ((apkg stringp)
                              (verbose$ booleanp)
                              (indent-level natp)
                              (channel symbolp)
                              state)
  :returns state
  :mode :program
  :short "Generate a Java method
          that adds an ACL2 package definition to the environment."
  :long
  (xdoc::topstring-p
   "This is a private static method
    that contains a sequence of statements
    to incrementally construct
    the Java list of symbols imported by the package.
    The sequence starts with a declaration of a local variable
    initialized with an empty Java list
    whose capacity is the length of the import list.
    After all the assignments, we generate a method call
    to add the package to the environment with the calculated import list.")
  (b* (((run-when verbose$)
        (cw "  ~s0~%" apkg))
       (jmethod-name (atj-gen-apkg-jmethod-name apkg))
       ((mv & state) (fmt1! "~%~s0private static void ~s1() {~%"
                            (list (cons #\0 (atj-indent indent-level))
                                  (cons #\1 jmethod-name))
                            0 channel state nil))
       (imports (pkg-imports apkg))
       ((mv & state) (fmt1! "~s0List<Acl2Symbol> ~s1 = new ArrayList<>(~x2);~%"
                            (list (cons #\0 (atj-indent (1+ indent-level)))
                                  (cons #\1 *atj-jvar-imports*)
                                  (cons #\2 (len imports)))
                            0 channel state nil))
       (state (atj-gen-apkg-jmethod-aux imports indent-level channel state))
       (apkg-name-jexpr (atj-gen-apkg-name apkg))
       ((mv & state) (fmt1! "~s0Acl2Environment.addPackageDef(~@1, ~s2);~%"
                            (list (cons #\0 (atj-indent (1+ indent-level)))
                                  (cons #\1 apkg-name-jexpr)
                                  (cons #\2 *atj-jvar-imports*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0}~%" (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil)))
    state)

  :prepwork
  ((define atj-gen-apkg-jmethod-aux ((imports symbol-listp)
                                     (indent-level natp)
                                     (channel symbolp)
                                     state)
     :returns state
     :mode :program
     :parents nil
     (if (endp imports)
         state
       (b* ((import-jexpr (atj-gen-asymbol (car imports)))
            ((mv & state) (fmt1! "~s0~s1.add(~@2);~%"
                                 (list (cons #\0 (atj-indent indent-level))
                                       (cons #\1 *atj-jvar-imports*)
                                       (cons #\2 import-jexpr))
                                 0 channel state nil)))
         (atj-gen-apkg-jmethod-aux
          (cdr imports) indent-level channel state))))))

(define atj-gen-apkg-jmethods ((apkgs string-listp)
                               (verbose$ booleanp)
                               (indent-level natp)
                               (channel symbolp)
                               state)
  :returns state
  :mode :program
  :short "Generate all the Java methods
          that add the ACL2 package definitions to the environment."
  (if (endp apkgs)
      state
    (b* ((state (atj-gen-apkg-jmethod (car apkgs) verbose$
                                      indent-level channel state)))
      (atj-gen-apkg-jmethods (cdr apkgs) verbose$
                             indent-level channel state))))

(define atj-gen-apkgs ((apkgs string-listp)
                       (indent-level natp)
                       (channel symbolp)
                       state)
  :returns state
  :mode :program
  :short "Generate Java code to build the ACL2 packages."
  :long
  (xdoc::topstring-p
   "This is a sequence of calls to the methods
    generated by @(tsee atj-gen-apkg-jmethods).
    These calls are part of the code that
    initializes (the Java representation of) the ACL2 environment.")
  (if (endp apkgs)
      state
    (b* ((jmethod-name (atj-gen-apkg-jmethod-name (car apkgs)))
         ((mv & state) (fmt1! "~s0~s1();~%"
                              (list (cons #\0 (atj-indent indent-level))
                                    (cons #\1 jmethod-name))
                              0 channel state nil)))
      (atj-gen-apkgs (cdr apkgs) indent-level channel state))))

(define atj-gen-apkg-witness ((indent-level natp)
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
                            (list (cons #\0 (atj-indent indent-level))
                                  (cons #\1 *pkg-witness-name*))
                            0 channel state nil)))
    state))

(define atj-gen-deep-afndef-jmethod-name ((afn symbolp))
  :returns (method-name stringp)
  :short "Name of the Java method that builds
          a deeply embedded ACL2 function definition."
  :long
  (xdoc::topstring-p
   "We generate a private static method
    for each deeply embedded ACL2 function definition to build.
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
   (ubyte8s=>hexstring (string=>nats (symbol-package-name afn)))
   "_"
   (ubyte8s=>hexstring (string=>nats (symbol-name afn)))))

(defval *atj-jvar-formals*
  :short "Name of the Java local variable used to store
          the formal arguments of a deeply embedded ACL2 function definition."
  "formals"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-formals*)))

(defval *atj-jvar-body*
  :short "Name of the Java local variable used to store
          the body of a deeply embedded ACL2 function definition."
  "body"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-body*)))

(defval *atj-jvar-function*
  :short "Name of the Java local variable used to store
          a deeply embedded ACL2 function."
  "function"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-function*)))

(define atj-gen-deep-afndef-jmethod ((afn symbolp)
                                     (verbose$ booleanp)
                                     (indent-level natp)
                                     (channel symbolp)
                                     state)
  :returns state
  :mode :program
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
    "The indices of the local variables
     to build values, terms, and lambda expressions
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
        (cw "  ~s0~%" afn))
       (jmethod-name (atj-gen-deep-afndef-jmethod-name afn))
       ((mv & state) (fmt1! "~%~s0private static void ~s1() {~%"
                            (list (cons #\0 (atj-indent indent-level))
                                  (cons #\1 jmethod-name))
                            0 channel state nil))
       (aformals (formals afn (w state)))
       (abody (getpropc afn 'acl2::unnormalized-body))
       (abody (remove-mbe-exec-from-term abody))
       (afn-jexpr (atj-gen-asymbol afn))
       (aformals-jexpr (atj-gen-deep-aformals aformals))
       ((mv abody-jexpr
            & & &
            state) (atj-gen-deep-aterm abody 1 1 1
                                       (1+ indent-level) channel state))
       ((mv & state) (fmt1! "~s0Acl2NamedFunction ~s1 = ~
                                Acl2NamedFunction.make(~@2);~%"
                            (list (cons #\0 (atj-indent (1+ indent-level)))
                                  (cons #\1 *atj-jvar-function*)
                                  (cons #\2 afn-jexpr))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0Acl2Symbol[] ~s1 = ~@2;~%"
                            (list (cons #\0 (atj-indent (1+ indent-level)))
                                  (cons #\1 *atj-jvar-formals*)
                                  (cons #\2 aformals-jexpr))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0Acl2Term ~s1 = ~@2;~%"
                            (list (cons #\0 (atj-indent (1+ indent-level)))
                                  (cons #\1 *atj-jvar-body*)
                                  (cons #\2 abody-jexpr))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0~s1.define(~s2, ~s3);~%"
                            (list (cons #\0 (atj-indent (1+ indent-level)))
                                  (cons #\1 *atj-jvar-function*)
                                  (cons #\2 *atj-jvar-formals*)
                                  (cons #\3 *atj-jvar-body*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0}~%" (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil)))
    state))

(define atj-gen-deep-afndef-jmethods ((afns symbol-listp)
                                      (verbose$ booleanp)
                                      (indent-level natp)
                                      (channel symbolp)
                                      state)
  :returns state
  :mode :program
  :short "Generate all the Java methods that build
          the deeply embedded ACL2 function definitions."
  (if (endp afns)
      state
    (b* ((state (atj-gen-deep-afndef-jmethod (car afns)
                                             verbose$
                                             indent-level
                                             channel
                                             state)))
      (atj-gen-deep-afndef-jmethods (cdr afns)
                                    verbose$
                                    indent-level
                                    channel
                                    state))))

(define atj-gen-deep-afndefs ((afns symbol-listp)
                              (indent-level natp)
                              (channel symbolp)
                              state)
  :returns state
  :mode :program
  :short "Generate Java code to build
          the deeply embedded ACL2 function definitions."
  :long
  (xdoc::topstring-p
   "This is a sequence of calls to the methods
    generated by @(tsee atj-gen-deep-afndef-jmethods).
    These calls are part of the code that
    initializes (the Java representation of) the ACL2 environment.")
  (if (endp afns)
      state
    (b* ((jmethod-name (atj-gen-deep-afndef-jmethod-name (car afns)))
         ((mv & state) (fmt1! "~s0~s1();~%"
                              (list (cons #\0 (atj-indent indent-level))
                                    (cons #\1 jmethod-name))
                              0 channel state nil)))
      (atj-gen-deep-afndefs (cdr afns) indent-level channel state))))

(define atj-gen-shallow-afnprimitive ((afn symbolp)
                                      (verbose$ booleanp)
                                      (curr-pkg stringp)
                                      (indent-level natp)
                                      (channel symbolp)
                                      state)
  :guard (and (primitivep afn)
              (equal (symbol-package-name afn) curr-pkg))
  :returns state
  :mode :program
  :short "Generate a shallowly embedded ACL2 primitive function."
  :long
  (xdoc::topstring
   (xdoc::p
    "AIJ's @('Acl2NativeFunction') class provides native Java implementations
     of the ACL2 primitive functions, as public static Java methods.
     Thus, in the shallow embedding approach,
     we could translate each reference to an ACL2 primitive function
     to the names of those public static Java methods.
     However, for greater uniformity,
     we generate Java methods for the ACL2 primitive functions
     whose names are constructed in the same way as
     the Java methods for the non-primitive ACL2 functions,
     and that reside in the Java classes generated for
     the @('\"COMMON-LISP\"') and @('\"ACL2\"') ACL2 packages.
     These Java methods for the ACL2 primitive functions
     simply call the aforementioned public methods."))
  (b* (((run-when verbose$)
        (cw "  ~s0~%" afn))
       (jcall
        (case afn
          (characterp "execCharacterp(x)")
          (stringp "execStringp(x)")
          (symbolp "execSymbolp(x)")
          (integerp "execIntegerp(x)")
          (rationalp "execRationalp(x)")
          (complex-rationalp "execComplexRationalp(x)")
          (acl2-numberp "execAcl2Numberp(x)")
          (consp "execConsp(x)")
          (char-code "execCharCode(x)")
          (code-char "execCodeChar(x)")
          (coerce "execCoerce(x, y)")
          (intern-in-package-of-symbol "execInternInPackageOfSymbol(str, sym)")
          (symbol-package-name "execSymbolPackageName(x)")
          (symbol-name "execSymbolName(x)")
          (pkg-imports "execPkgImports(pkg)")
          (pkg-witness "execPkgWitness(pkg)")
          (unary-- "execUnaryMinus(x)")
          (unary-/ "execUnarySlash(x)")
          (binary-+ "execBinaryPlus(x, y)")
          (binary-* "execBinaryStar(x, y)")
          (< "execLessThan(x, y)")
          (complex "execComplex(x, y)")
          (realpart "execRealPart(x)")
          (imagpart "execImagPart(x)")
          (numerator "execNumerator(x)")
          (denominator "execDenominator(x)")
          (cons "execCons(x, y)")
          (car "execCar(x)")
          (cdr "execCdr(x)")
          (equal "execEqual(x, y)")
          (bad-atom<= "execBadAtomLessThanOrEqualTo(x, y)")
          (if "execIf(x, y, z)")
          (t (acl2::impossible))))
       (jcall (str::cat "Acl2NativeFunction." jcall))
       (jparamlist
        (case afn
          (intern-in-package-of-symbol "Acl2Value str, Acl2Value sym")
          (if "Acl2Value x, Acl2Value y, Acl2Value z")
          ((pkg-imports
            pkg-witness) "Acl2Value pkg")
          ((coerce
            binary-+
            binary-*
            <
            complex
            cons
            equal
            bad-atom<=) "Acl2Value x, Acl2Value y")
          (t "Acl2Value x")))
       (jmethod-name (atj-gen-shallow-afnname afn curr-pkg))
       ((mv & state) (fmt1! "~%~s0public static Acl2Value ~s1(~s2)~%"
                            (list (cons #\0 (atj-indent indent-level))
                                  (cons #\1 jmethod-name)
                                  (cons #\2 jparamlist))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0throws Acl2EvaluationException {~%"
                            (list (cons #\0 (atj-indent (1+ indent-level))))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0return ~s1;~%"
                            (list (cons #\0 (atj-indent (1+ indent-level)))
                                  (cons #\1 jcall))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0}~%"
                            (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil)))
    state))

(define atj-gen-shallow-afndef ((afn symbolp)
                                (verbose$ booleanp)
                                (curr-pkg stringp)
                                (indent-level natp)
                                (channel symbolp)
                                state)
  :guard (equal (symbol-package-name afn) curr-pkg)
  :returns state
  :mode :program
  :short "Generate a shallowly embedded ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 function definition is turned into a Java method.
     This is a public static method
     with the same number of parameters as the ACL2 function,
     all of Java type @('Acl2Value'),
     and that returns a value of the same type.")
   (xdoc::p
    "We turn the ACL2 formal parameters
     into Java variables to use as the method parameters,
     starting with no indices for the variables,
     since we are at the top level of the generation of
     the shallowly embedded ACL2 terms and lambda expressions.
     Note that @(tsee atj-gen-shallow-avars) preserves the order,
     so its @(tsee strip-cdrs) consists of the Java parameters
     in the same order as the corresponding ACL2 parameters.")
   (xdoc::p
    "We turn the body of the ACL2 function
     into Java statements and a Java expression,
     which constitute the shallow embedding of the ACL2 function body;
     the indices for the Java local variables
     with base names @(tsee *atj-jvar-value*) and @(tsee *atj-jvar-result*)
     are initialized to 1, since we are at the top level here.
     The body of the Java method consists of those Java statements,
     followed by a @('return') statement with that Java expression.")
   (xdoc::p
    "Prior to shallowly embedding the ACL2 function body,
     all the calls of @(tsee mbe) are replaced with their @(':logic') parts
     in the function's body.
     This is consistent with the fact that the Java counterpart of the function
     is executed ``in the logic''."))
  (b* (((run-when verbose$)
        (cw "  ~s0~%" afn))
       (jmethod-name (atj-gen-shallow-afnname afn curr-pkg))
       (aformals (formals afn (w state)))
       ((mv jvars
            jvar-var-indices) (atj-gen-shallow-avars aformals nil curr-pkg))
       (jparams (strip-cdrs jvars))
       (jparamlist (atj-gen-jparamlist-avalues jparams))
       ((mv & state) (fmt1! "~%~s0public static Acl2Value ~s1(~@2)~%"
                            (list (cons #\0 (atj-indent indent-level))
                                  (cons #\1 jmethod-name)
                                  (cons #\2 jparamlist))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0throws Acl2EvaluationException {~%"
                            (list (cons #\0 (atj-indent (1+ indent-level))))
                            0 channel state nil))
       (abody (getpropc afn 'acl2::unnormalized-body))
       (abody (remove-mbe-exec-from-term abody))
       ((mv jexpr & & & state) (atj-gen-shallow-aterm abody
                                                      jvars
                                                      jvar-var-indices
                                                      1
                                                      1
                                                      curr-pkg
                                                      (1+ indent-level)
                                                      channel
                                                      state))
       ((mv & state) (fmt1! "~s0return ~@1;~%"
                            (list (cons #\0 (atj-indent (1+ indent-level)))
                                  (cons #\1 jexpr))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0}~%"
                            (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil)))
    state))

(define atj-gen-shallow-afn ((afn symbolp)
                             (verbose$ booleanp)
                             (curr-pkg stringp)
                             (indent-level natp)
                             (channel symbolp)
                             state)
  :guard (equal (symbol-package-name afn) curr-pkg)
  :returns state
  :mode :program
  :short "Generate a shallowly embedded
          ACL2 primitive function or function definition."
  (if (primitivep afn)
      (atj-gen-shallow-afnprimitive
       afn verbose$ curr-pkg indent-level channel state)
    (atj-gen-shallow-afndef
     afn verbose$ curr-pkg indent-level channel state)))

(define atj-gen-shallow-afns ((afns symbol-listp)
                              (verbose$ booleanp)
                              (curr-pkg stringp)
                              (indent-level natp)
                              (channel symbolp)
                              state)
  :guard (equal (acl2::symbol-package-name-lst afns)
                (repeat (len afns) curr-pkg))
  :returns state
  :mode :program
  :short "Lift @(tsee atj-gen-shallow-afn) to lists."
  (cond ((endp afns) state)
        (t (b* ((state (atj-gen-shallow-afn (car afns)
                                            verbose$
                                            curr-pkg
                                            indent-level
                                            channel
                                            state)))
             (atj-gen-shallow-afns (cdr afns)
                                   verbose$
                                   curr-pkg
                                   indent-level
                                   channel
                                   state)))))

(define atj-gen-shallow-afns-in-apkg ((afns symbol-listp)
                                      (apkg stringp)
                                      (java-class$ stringp)
                                      (verbose$ booleanp)
                                      (indent-level natp)
                                      (channel symbolp)
                                      state)
  :guard (equal (acl2::symbol-package-name-lst afns)
                (repeat (len afns) apkg))
  :returns state
  :mode :program
  :short "Generate the shallowly embedded ACL2 functions
          in an ACL2 package."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     we generate a Java class for each ACL2 package
     that includes ACL2 functions for which we generate Java code
     (each ACL2 function is turned into a Java method in this class).
     This is a public static Java class,
     nested into the main Java class that ATJ generates."))
  (b* ((jclass-name (atj-gen-shallow-apkgname apkg java-class$))
       ((mv & state) (fmt1! "~%~s0public static class ~s1 {~%"
                            (list (cons #\0 (atj-indent indent-level))
                                  (cons #\1 jclass-name))
                            0 channel state nil))
       (state (atj-gen-shallow-afns afns verbose$ apkg
                                    (1+ indent-level) channel state))
       ((mv & state) (fmt1! "~s0}~%"
                            (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil)))
    state))

(define atj-gen-shallow-afns-by-apkg ((afns-by-apkg string-symbols-alistp)
                                      (java-class$ stringp)
                                      (verbose$ booleanp)
                                      (indent-level natp)
                                      (channel symbolp)
                                      state)
  :returns state
  :mode :program
  :short "Generate shallowly embedded ACL2 functions, by ACL2 packages."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through each pair in the alist
     from ACL2 package names to ACL2 functions,
     and generate all the Java classes corresponding to the ACL2 packages."))
  (b* ((apkgs (remove-duplicates-equal (strip-cars afns-by-apkg))))
    (atj-gen-shallow-afns-by-apkg-aux apkgs afns-by-apkg java-class$ verbose$
                                      indent-level channel state))

  :prepwork
  ((define atj-gen-shallow-afns-by-apkg-aux
     ((apkgs string-listp)
      (afns-by-apkg string-symbols-alistp)
      (java-class$ stringp)
      (verbose$ booleanp)
      (indent-level natp)
      (channel symbolp)
      state)
     :returns state
     :mode :program
     (cond ((endp apkgs) state)
           (t (b* ((apkg (car apkgs))
                   (afns (cdr (assoc-equal apkg afns-by-apkg)))
                   (state (atj-gen-shallow-afns-in-apkg
                           afns apkg java-class$ verbose$
                           indent-level channel state)))
                (atj-gen-shallow-afns-by-apkg-aux (cdr apkgs)
                                                  afns-by-apkg
                                                  java-class$
                                                  verbose$
                                                  indent-level
                                                  channel
                                                  state)))))))

(define atj-gen-init-jmethod ((apkgs string-listp)
                              (afns symbol-listp)
                              (deep$ booleanp)
                              (indent-level natp)
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
     because initialization must occur only once.")
   (xdoc::p
    "If @(':deep') is @('t'), we generate code
     to build the deeply embedded representations of the ACL2 functions.
     Otherwise, we skip this step.
     The representations of the ACL2 packages are needed for
     both deep and shallow embedding.")
   (xdoc::p
    "If @(':deep') is @('t'), we generate code
     to validate the definitions of all the deeply embedded ACL2 functions.
     Otherwise, we skip this step."))
  (b* (((mv & state) (fmt1! "~%~s0public static void initialize() {~%"
                            (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0if (initialized)~%"
                            (list (cons #\0 (atj-indent (1+ indent-level))))
                            0 channel state nil))
       (exception-message "The ACL2 environment is already initialized.")
       ((mv & state) (fmt1! "~s0throw new IllegalStateException(~x1);~%"
                            (list (cons #\0 (atj-indent (+ 2 indent-level)))
                                  (cons #\1 exception-message))
                            0 channel state nil))
       (state (atj-gen-apkgs apkgs (1+ indent-level) channel state))
       (state (atj-gen-apkg-witness (1+ indent-level) channel state))
       (state (if deep$
                  (atj-gen-deep-afndefs afns (1+ indent-level) channel state)
                state))
       ((mv & state) (if deep$
                         (fmt1! "~s0Acl2NamedFunction.validateAll();~%"
                                (list (cons #\0 (atj-indent (1+ indent-level))))
                                0 channel state nil)
                       (mv 0 state)))
       ((mv & state) (fmt1! "~s0initialized = true;~%"
                            (list (cons #\0 (atj-indent (1+ indent-level))))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0}~%"
                            (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil)))
    state))

(define atj-gen-init-jfield ((indent-level natp)
                             (channel symbolp)
                             state)
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
                            (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil)))
    state))

(define atj-gen-call-jmethod ((indent-level natp)
                              (channel symbolp)
                              state)
  :returns state
  :mode :program
  :short "Generate the Java method to call ACL2 functions,
          in the deep embedding approach."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a public static method,
     which provides the means for external Java code to call
     the deeply embedded Java representations of ACL2 functions."))
  (b* (((mv & state) (fmt1! "~%~s0public static Acl2Value ~
                             call(Acl2Symbol function, ~
                                  Acl2Value[] arguments)~%"
                            (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0throws Acl2EvaluationException {~%"
                            (list (cons #\0 (atj-indent (1+ indent-level))))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0if (!initialized)~%"
                            (list (cons #\0 (atj-indent (1+ indent-level))))
                            0 channel state nil))
       (exception-message "The ACL2 environment is not initialized.")
       ((mv & state) (fmt1! "~s0throw new IllegalStateException(~x1);~%"
                            (list (cons #\0 (atj-indent (+ 2 indent-level)))
                                  (cons #\1 exception-message))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0return Acl2NamedFunction.make(function).~
                                       call(arguments);~%"
                            (list (cons #\0 (atj-indent (1+ indent-level))))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0}~%"
                            (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil)))
    state))

(define atj-gen-jclass ((apkgs string-listp)
                        (afns symbol-listp)
                        (deep$ booleanp)
                        (java-class$ stringp)
                        (verbose$ booleanp)
                        (indent-level natp)
                        (channel symbolp)
                        state)
  :returns state
  :mode :program
  :short "Generate the main (i.e. non-test) Java class declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a public class that contains all the generated members.
     [JLS] says that a Java implementation may require
     public classes to be in files with the same names (plus extension).
     The code that we generate satisfies this requirement.")
   (xdoc::p
    "If @(':deep') is @('t'), we generate the Java methods
     to build the deeply embedded ACL2 functions
     and the @('call') method.
     If @(':deep') is @('nil'), we generate the Java classes and methods
     for the shallowly embedded ACL2 functions,
     and no @('call') method.
     In the latter case, we ensure that the ACL2 primitives are included,
     we organize the resulting functions by packages,
     and we proceed to generate the Java nested classes and methods."))
  (b* (((mv & state) (fmt1! "~s0public class ~s1 {~%"
                            (list (cons #\0 (atj-indent indent-level))
                                  (cons #\1 java-class$))
                            0 channel state nil))
       (state (atj-gen-init-jfield (1+ indent-level) channel state))
       ((run-when verbose$)
        (cw "~%Generating Java code for the ACL2 packages:~%"))
       (state (atj-gen-apkg-jmethods apkgs verbose$
                                     (1+ indent-level) channel state))
       ((run-when verbose$)
        (cw "~%Generating Java code for the ACL2 functions:~%"))
       (state (if deep$
                  (atj-gen-deep-afndef-jmethods afns
                                                verbose$
                                                (1+ indent-level)
                                                channel
                                                state)
                (b* ((afns+primitives
                      (remove-duplicates-eq
                       (append afns
                               (strip-cars *primitive-formals-and-guards*))))
                     (afns-by-apkg (organize-fns-by-pkg afns+primitives)))
                  (atj-gen-shallow-afns-by-apkg afns-by-apkg
                                                java-class$
                                                verbose$
                                                (1+ indent-level)
                                                channel
                                                state))))
       (state (atj-gen-init-jmethod apkgs afns deep$
                                    (1+ indent-level) channel state))
       (state (if deep$
                  (atj-gen-call-jmethod (1+ indent-level) channel state)
                state))
       ((mv & state) (fmt1! "}~%" nil 0 channel state nil)))
    state))

(define atj-gen-test-jmethod-name ((test-name stringp))
  :returns (jmethod-name stringp)
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
  (str::cat "test_" test-name))

(defval *atj-jvar-fnname*
  :short "Name of the Java local variable used to store
          the function name of an ACL2 function call."
  "name"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-fnname*)))

(defval *atj-jvar-fnargs*
  :short "Name of the Java local variables used to store
          the array of argument values of an ACL2 function call."
  "arguments"
  ///
  (assert-event (atj-string-ascii-java-identifier-p *atj-jvar-fnargs*)))

(defval *atj-jvar-aresult*
  :short "Name of the Java local variables used to store
          the result of a test calculated in ACL2 (by ATJ)."
  "resultAcl2"
  ///
  (assert-event
   (atj-string-ascii-java-identifier-p *atj-jvar-aresult*)))

(defval *atj-jvar-jresult*
  :short "Name of the Java local variables used to store
          the result of a test calculated in Java (by AIJ)."
  "resultJava"
  ///
  (assert-event
   (atj-string-ascii-java-identifier-p *atj-jvar-jresult*)))

(define atj-gen-test-jmethod ((test$ atj-testp)
                              (java-class$ stringp)
                              (verbose$ booleanp)
                              (indent-level natp)
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
       (jmethod-name (atj-gen-test-jmethod-name test.name))
       ((mv & state) (fmt1! "~%~s0private static void ~s1()~%"
                            (list (cons #\0 (atj-indent indent-level))
                                  (cons #\1 jmethod-name))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0throws Acl2EvaluationException {~%"
                            (list (cons #\0 (atj-indent (1+ indent-level))))
                            0 channel state nil))
       ((mv & state) (fmt1!
                      "~s0System.out.print(\"Testing \" + ~x1 + \"... \");~%"
                      (list (cons #\0 (atj-indent (1+ indent-level)))
                            (cons #\1 test.name))
                      0 channel state nil))
       (afnname-jexpr (atj-gen-asymbol test.function))
       ((mv & state) (fmt1! "~s0Acl2Symbol ~s1 = ~@2;~%"
                            (list (cons #\0 (atj-indent (1+ indent-level)))
                                  (cons #\1 *atj-jvar-fnname*)
                                  (cons #\2 afnname-jexpr))
                            0 channel state nil))
       ((mv aarg-jexprs jvar-value-index state) (atj-gen-test-jmethod-aux
                                                 test.arguments
                                                 1
                                                 (1+ indent-level)
                                                 channel
                                                 state))
       (aargs-jexpr (atj-gen-jarray aarg-jexprs "Acl2Value"))
       ((mv & state) (fmt1! "~s0Acl2Value[] ~s1 = ~@2;~%"
                            (list (cons #\0 (atj-indent (1+ indent-level)))
                                  (cons #\1 *atj-jvar-fnargs*)
                                  (cons #\2 aargs-jexpr))
                            0 channel state nil))
       ((mv ares-jexpr & state) (atj-gen-avalue
                                 test.result jvar-value-index
                                 (1+ indent-level) channel state))
       ((mv & state) (fmt1! "~s0Acl2Value ~s1 = ~@2;~%"
                            (list (cons #\0 (atj-indent (1+ indent-level)))
                                  (cons #\1 *atj-jvar-aresult*)
                                  (cons #\2 ares-jexpr))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0Acl2Value ~s1 = ~s2.call(~s3, ~s4);~%"
                            (list (cons #\0 (atj-indent (1+ indent-level)))
                                  (cons #\1 *atj-jvar-jresult*)
                                  (cons #\2 java-class$)
                                  (cons #\3 *atj-jvar-fnname*)
                                  (cons #\4 *atj-jvar-fnargs*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0if (~s1.equals(~s2))~%"
                            (list (cons #\0 (atj-indent (1+ indent-level)))
                                  (cons #\1 *atj-jvar-aresult*)
                                  (cons #\2 *atj-jvar-jresult*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0System.out.println(\"PASS\");~%"
                            (list (cons #\0 (atj-indent (+ 2 indent-level))))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0else~%"
                            (list (cons #\0 (atj-indent (1+ indent-level))))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0System.out.println(\"FAIL\");~%"
                            (list (cons #\0 (atj-indent (+ 2 indent-level))))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0}~%" (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil)))
    state)

  :prepwork
  ((define atj-gen-test-jmethod-aux ((aargs true-listp)
                                     (jvar-value-index posp)
                                     (indent-level natp)
                                     (channel symbolp)
                                     state)
     :returns (mv jexprs ;; MSG-LISTP
                  new-jvar-value-index ;; POSP
                  state)
     :mode :program
     :parents nil
     (b* (((when (endp aargs)) (mv nil jvar-value-index state))
          (aarg (car aargs))
          ((mv jexpr jvar-value-index state)
           (atj-gen-avalue aarg jvar-value-index indent-level channel state))
          ((mv jexprs jvar-value-index state)
           (atj-gen-test-jmethod-aux (cdr aargs) jvar-value-index
                                     indent-level channel state)))
       (mv (cons jexpr jexprs)
           jvar-value-index
           state)))))

(define atj-gen-test-jmethods ((tests$ atj-test-listp)
                               (java-class$ stringp)
                               (verbose$ booleanp)
                               (indent-level natp)
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
    (b* ((state (atj-gen-test-jmethod (car tests$) java-class$ verbose$
                                      indent-level channel state)))
      (atj-gen-test-jmethods (cdr tests$) java-class$ verbose$
                             indent-level channel state))))

(define atj-gen-run-tests ((tests$ atj-test-listp)
                           (indent-level natp)
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
     generated by @(tsee atj-gen-test-jmethods).
     These calls are part of the main method of the test Java class."))
  (if (endp tests$)
      state
    (b* ((method-name (atj-gen-test-jmethod-name (atj-test->name (car tests$))))
         ((mv & state) (fmt1! "~s0~s1();~%"
                              (list (cons #\0 (atj-indent indent-level))
                                    (cons #\1 method-name))
                              0 channel state nil)))
      (atj-gen-run-tests (cdr tests$) indent-level channel state))))

(define atj-gen-test-main-jmethod ((tests$ atj-test-listp)
                                   (java-class$ stringp)
                                   (indent-level natp)
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
                            (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0throws Acl2EvaluationException {~%"
                            (list (cons #\0 (atj-indent (1+ indent-level))))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0~s1.initialize();~%"
                            (list (cons #\0 (atj-indent (1+ indent-level)))
                                  (cons #\1 java-class$))
                            0 channel state nil))
       (state (atj-gen-run-tests tests$ 2 channel state))
       ((mv & state) (fmt1! "~s0}~%"
                            (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil)))
    state))

(define atj-gen-test-jclass ((tests$ atj-test-listp)
                             (java-class$ stringp)
                             (verbose$ booleanp)
                             (indent-level natp)
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
       (state (atj-gen-test-jmethods tests$ java-class$ verbose$
                                     indent-level channel state))
       (state (atj-gen-test-main-jmethod tests$ java-class$
                                         (1+ indent-level) channel state))
       ((mv & state) (fmt1! "}~%" nil 0 channel state nil)))
    state))

(define atj-gen-jfile-header ((indent-level natp)
                              (channel symbolp)
                              state)
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
        (fmt1! "~s0// This file is automatically generated by ATJ.~%~%"
               (list (cons #\0 (atj-indent indent-level)))
               0 channel state nil)))
    state))

(define atj-gen-jpkg ((java-package$ maybe-stringp)
                      (indent-level natp)
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
      (b* (((mv & state) (fmt1! "~s0package ~s1;~%~%"
                                (list (cons #\0 (atj-indent indent-level))
                                      (cons #\1 java-package$))
                                0 channel state nil)))
        state)
    state))

(define atj-gen-jimport ((indent-level natp)
                         (channel symbolp)
                         state)
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
  (b* (((mv & state) (fmt1! "~s0import ~s1.*;~%"
                            (list (cons #\0 (atj-indent indent-level))
                                  (cons #\1 *atj-aij-package*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0import java.math.BigInteger;~%"
                            (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0import java.util.ArrayList;~%"
                            (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0import java.util.List;~%"
                            (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil))
       ((mv & state) (fmt1! "~%" nil 0 channel state nil)))
    state))

(define atj-gen-test-jimport ((indent-level natp)
                              (channel symbolp)
                              state)
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
  (b* (((mv & state) (fmt1! "~s0import ~s`.*;~%"
                            (list (cons #\0 (atj-indent indent-level))
                                  (cons #\1 *atj-aij-package*))
                            0 channel state nil))
       ((mv & state) (fmt1! "~s0import java.math.BigInteger;~%"
                            (list (cons #\0 (atj-indent indent-level)))
                            0 channel state nil))
       ((mv & state) (fmt1! "~%" nil 0 channel state nil)))
    state))

(define atj-gen-jfile ((deep$ booleanp)
                       (java-package$ maybe-stringp)
                       (java-class$ maybe-stringp)
                       (output-file$ stringp)
                       (pkgs string-listp)
                       (afns symbol-listp)
                       (verbose$ booleanp)
                       state)
  :returns (mv (erp "Always @('nil').")
               (val "Always @('nil').")
               state)
  :mode :program
  :short "Generate the main Java file."
  (b* (((mv channel state) (open-output-channel! output-file$
                                                 :character state))
       (state (atj-gen-jfile-header 0 channel state))
       (state (atj-gen-jpkg java-package$ 0 channel state))
       (state (atj-gen-jimport 0 channel state))
       (state (atj-gen-jclass
               pkgs afns deep$ java-class$ verbose$ 0 channel state))
       (state (close-output-channel channel state)))
    (value nil))
  :prepwork ((defttag :open-input-channel)))

(define atj-gen-test-jfile ((java-package$ maybe-stringp)
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
       (state (atj-gen-jfile-header 0 channel state))
       (state (atj-gen-jpkg java-package$ 0 channel state))
       (state (atj-gen-test-jimport 0 channel state))
       (state (atj-gen-test-jclass tests$ java-class$ verbose$ 0 channel state))
       (state (close-output-channel channel state)))
    (value nil))
  :prepwork ((defttag :open-input-channel)))

(define atj-gen-everything ((deep$ booleanp)
                            (java-package$ maybe-stringp)
                            (java-class$ maybe-stringp)
                            (output-file$ stringp)
                            (output-file-test$ maybe-stringp)
                            (tests$ atj-test-listp)
                            (pkgs string-listp)
                            (afns symbol-listp)
                            (verbose$ booleanp)
                            state)
  :returns (mv (erp "Always @('nil').")
               (val "Always @('nil').")
               state)
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
     We generated the test Java file only if @(':tests') is not @('nil')."))
  (state-global-let*
   ((acl2::fmt-soft-right-margin 100000 set-fmt-soft-right-margin)
    (acl2::fmt-hard-right-margin 100000 set-fmt-hard-right-margin))
   (b* (((er &) (atj-gen-jfile deep$
                               java-package$
                               java-class$
                               output-file$
                               pkgs
                               afns
                               verbose$
                               state))
        ((er &) (if tests$
                    (atj-gen-test-jfile java-package$
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
                  deep$
                  java-package$
                  java-class
                  output-file$
                  output-file-test$
                  tests$
                  verbose$)) (atj-process-inputs args ctx state))
       ((er (list pkgs
                  afns)) (atj-gather-info targets$ verbose$ ctx state))
       ((er &) (atj-gen-everything deep$
                                   java-package$
                                   java-class
                                   output-file$
                                   output-file-test$
                                   tests$
                                   pkgs
                                   afns
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
