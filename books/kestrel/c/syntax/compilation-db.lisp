; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "kestrel/fty/string-option" :dir :system)

(include-book "kestrel/json-parser/parse-json-file" :dir :system)
(include-book "kestrel/json/top" :dir :system)

(include-book "std/strings/strpos" :dir :system)
(include-book "std/strings/strsubst" :dir :system)
(include-book "std/strings/suffixp" :dir :system)

(include-book "kestrel/utilities/messages" :dir :system)
(include-book "system/extend-pathname" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (:e tau-system))))
(set-induction-depth-limit 0)

(local (in-theory (enable acons)))

(local (include-book "kestrel/strings-light/char" :dir :system))
(local (include-book "kestrel/typed-lists-light/string-listp" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ compilation-database
  :parents (syntax-for-tools)
  :short "Utilities for reading and modifying JSON compilation databases."
  :long
  (xdoc::topstring
   (xdoc::p
     "The @('clang') ecosystem uses the "
     (xdoc::ahref "https://clang.llvm.org/docs/JSONCompilationDatabase.html"
                  "JSON compilation database format")
     " to represent compilation commands. Compilation database files are a
      convenient way to read the necessary compiler flags for all the source
      files of a large, complicated project automatically.")
   (xdoc::p
     "Various tools support the generation of compilation database files.
      On Linux, the "
     (xdoc::ahref "https://github.com/rizsotto/Bear" "Bear")
     " tool can be used to generate compilation databases from traditional
      @('Makefile')-based projects by intercepting and recording compiler
      calls.")
   (xdoc::p
     "Currently, the primary use-case for compilation database files is to
      gather all the necessary flags to pass to the C "
     (xdoc::seetopic "preprocessing" "preprocessor")
     "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod comp-db-arg
  :short "A fixtype for a compiler argument parsed from a @(see
          compilation-database)."
  :long
  (xdoc::topstring
    (xdoc::p
      "An argument is represented by a name and an optional value.")
    (xdoc::p
      "The separator field represents the string which separates the name from
       the value. For instance, in the argument @('\"-std=c17\"'), the
       separator is @('\"=\"').  In the argument @('\"-iquote /usr/include\"'),
       the separator is @('\" \"'). And in the argument
       @('\"-I/usr/include\"'), the separator is @('\"\"'). For arguments which
       do not have an associated value, the separator is @('\"\"')."))
  ((name string)
   (separator string)
   (value acl2::string-option))
  :pred comp-db-argp)

(defirrelevant irr-comp-db-arg
  :short "An irrelevant @(see comp-db-arg)."
  :type comp-db-argp
  :body (make-comp-db-arg :name "" :separator "" :value nil))

(define comp-db-arg-to-string
  ((arg comp-db-argp))
  :returns (string stringp)
  :short "Turn a @(see comp-db-arg) into a string."
  (b* (((comp-db-arg arg) arg))
    (concatenate 'string arg.name arg.separator (or arg.value "")))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist comp-db-arg-list
  :short "A fixtype for lists of compiler arguments parsed from a @(see
          compilation-database)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Note that the order of argument is meaningful. For instance, the
       argument @('-U') cancels previous definitions."))
  :elt-type comp-db-arg
  :true-listp t
  :elementp-of-nil nil
  :pred comp-db-arg-listp)

(define comp-db-arg-list-to-string-list
  ((args comp-db-arg-listp))
  :returns (strings string-listp)
  :short "Turn a @(see comp-db-arg-list) into a string list."
  (if (endp args)
      nil
    (cons (comp-db-arg-to-string (first args))
          (comp-db-arg-list-to-string-list (rest args))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod comp-db-entry
  :short "A fixtype for entries parsed from a @(see compilation-database)."
  :long
  (xdoc::topstring
    (xdoc::p
      "The @('exec') field is the executable which performs compilation. The
       @('directory') is the working directory in which to compile. The
       optional @('output') field represents the created file (typically a
       @('.o') file. When present, it is the value associated with the @('-o')
       flag for C compilations. Lastly, @('arguments') is a list of arguments
       provided to the compiler."))
  ((exec string)
   (directory string)
   (output acl2::string-option)
   (arguments comp-db-arg-list))
  :pred comp-db-entryp)

(encapsulate ()
  (local (set-induction-depth-limit 1))

  (fty::defalist comp-db
    :short "A fixtype for parsed @(see compilation-database)s."
    :long
    (xdoc::topstring
      (xdoc::p
        "This type is an alist associating file names to "
        (xdoc::seetopic "comp-db-entry" "entries")
        ". Note that a file name may be associated with "
        (xdoc::i "multiple")
        " entries. This may happen if, for instance, if a compilation database
         stores the compilation step for both a regular and a
         position-independent version of the same source file."))
    :key-type string
    :val-type comp-db-entry
    :true-listp t
    :pred comp-dbp))

(defrule alistp-when-comp-dbp-rewrite-cheap
  (implies (comp-dbp db)
           (alistp db))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable alistp-when-comp-dbp-rewrite)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *cc-options-space-sep*
  :short "C flags whose value follows after a whitespace separator."
  '("-o" "-include" "-idirafter" "-imacros" "-imultilib" "-iprefix" "-iquote"
    "-isysroot" "-isystem" "-iwithprefix" "-iwithprefixbefore"))

(defval *cc-options-equal-sep*
  :short "C flags whose value follows after an @('=') character."
  '("-std" "-iplugindir" "--sysroot"))

(defval *cc-options-dir*
  :short "C flags whose value represents a directory."
  '("-B" "-I" "-idirafter" "-imacros" "-imultilib" "-iplugindir" "-iprefix"
    "-iquote" "-isysroot" "-isystem" "-iwithprefix" "-withprefixbefore" "-L"
    "--sysroot" "-include"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db-get-file
  ((entry json::valuep))
  :guard (eq (json::value-kind entry) :object)
  :returns (mv erp (file stringp))
  (b* (((reterr) "")
       (entry (json::value-fix entry))
       (values (json::object-member-values "file" entry))
       ((when (endp values))
        (retmsg$ "JSON compilation entry has no \"file\" member. ~
                  Compilation entry: ~x0"
                 entry))
       ((unless (endp (rest values)))
        (retmsg$ "JSON compilation entry has multiple \"file\" members. ~
                  Compilation entry: ~x0"
                 entry))
       (value (first values)))
    (json::value-case
      value
      :string (retok value.get)
      :otherwise (retmsg$ "Expected string type in member field \"file\" of ~
                           JSON compilation database entry.
                           Found ~x0 instead."
                          (json::value-kind value))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db-get-output
  ((entry json::valuep))
  :guard (eq (json::value-kind entry) :object)
  :returns (mv erp (output? string-optionp))
  (b* (((reterr) nil)
       (entry (json::value-fix entry))
       (values (json::object-member-values "output" entry))
       ((when (endp values))
        (retok nil))
       ((unless (endp (rest values)))
        (retmsg$ "JSON compilation entry has multiple \"output\" members. ~
                  Compilation entry: ~x0"
                 entry))
       (value (first values)))
    (json::value-case
      value
      :string (retok value.get)
      :otherwise (retmsg$ "Expected string type in member field \"output\" of ~
                           JSON compilation database entry.
                           Found ~x0 instead."
                         (json::value-kind value))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db-get-directory
  ((entry json::valuep))
  :guard (eq (json::value-kind entry) :object)
  :returns (mv erp (directory stringp))
  (b* (((reterr) "")
       (entry (json::value-fix entry))
       (values (json::object-member-values "directory" entry))
       ((when (endp values))
        (retmsg$ "JSON compilation entry has no \"directory\" member. ~
                  Compilation entry: ~x0"
                 entry))
       ((unless (endp (rest values)))
        (retmsg$ "JSON compilation entry has multiple \"directory\" members. ~
                  Compilation entry: ~x0"
                 entry))
       (value (first values)))
    (json::value-case
      value
      :string (retok value.get)
      :otherwise (retmsg$ "Expected string type in member field \"directory\" ~
                           of JSON compilation database entry.
                           Found ~x0 instead."
                         (json::value-kind value))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db-try-parse-short-option
  ((argument stringp))
  :returns (mv erp (argument$ comp-db-argp))
  :short "Try to parse a short option."
  :long
  (xdoc::topstring
   (xdoc::p
     "A short option is a dash, followed by a single uppercase letter, followed
      by a value. For instance, @('-I/usr/include')."))
  (b* (((reterr) (irr-comp-db-arg)))
    (if (and (< 1 (length argument))
             (eql (char argument 0) #\-)
             (acl2::upper-case-p (char argument 1)))
        (retok (make-comp-db-arg :name (subseq argument 0 2)
                                 :separator ""
                                 :value (subseq argument 2 nil)))
      (reterr t))))

(define json-to-comp-db-try-parse-equal-arg
  ((argument stringp))
  :returns (mv erp (argument$ comp-db-argp))
  :short "Try to parse an argument with an @('=') separator."
  :long
  (xdoc::topstring
   (xdoc::p
     "For instance, @('-std=c17')."))
  (b* (((reterr) (irr-comp-db-arg))
       (pos (str::strpos "=" argument))
       ((unless pos)
        (reterr t))
       (name (subseq argument 0 pos))
       ((unless (member-equal name *cc-options-equal-sep*))
        (reterr t))
       (value (subseq argument (1+ pos) nil)))
    (retok (make-comp-db-arg :name name :separator "=" :value value)))
  :guard-hints (("Goal" :in-theory (enable length))))

(define json-to-comp-db-arguments
  ((arguments json::value-listp))
  :returns (mv erp (arguments$ comp-db-arg-listp))
  :short "Parse an argument list into structured, name/value arguments."
  (b* (((reterr) nil)
       (arguments (json::value-list-fix arguments))
       ((when (endp arguments))
        (retok nil))
       (name-value? (first arguments))
       ((unless (eq (json::value-kind name-value?) :string))
        (retmsg$ "Expected string type in \"arguments\" array of ~
                  JSON compilation database entry.
                  Found ~x0 instead."
                 (json::value-kind name-value?)))
       (name-value?-str (json::value-string->get name-value?))
       ((erp comp-db-arg rest-arguments)
        (b* (((reterr) nil nil)
             ((unless (member-equal name-value?-str *cc-options-space-sep*))
              (b* (((mv erp argument?)
                    (json-to-comp-db-try-parse-short-option name-value?-str))
                   ((unless erp)
                    (retok argument? (rest arguments)))
                   ((mv erp argument?)
                    (json-to-comp-db-try-parse-equal-arg name-value?-str))
                   ((unless erp)
                    (retok argument? (rest arguments))))
                (retok (make-comp-db-arg :name name-value?-str
                                         :separator ""
                                         :value nil)
                       (rest arguments))))
             ((when (endp (rest arguments)))
              (retmsg$ "Argument ~x0 is not followed by a value."
                       name-value?-str))
             (value (second arguments))
             ((unless (eq (json::value-kind value) :string))
              (retmsg$ "Expected string type in \"arguments\" array of ~
                        JSON compilation database entry.
                        Found ~x0 instead."
                       (json::value-kind value)))
             (value-str (json::value-string->get value)))
          (retok (make-comp-db-arg :name name-value?-str
                                   :separator " "
                                   :value value-str)
                 (rest (rest arguments)))))
       ((erp arguments$) (json-to-comp-db-arguments rest-arguments)))
    (retok (cons comp-db-arg arguments$)))
  :measure (json::value-list-count arguments)
  :hints (("Goal" :in-theory (enable json::value-list-fix)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db-exec-and-arguments
  ((arguments json::value-listp))
  :returns (mv erp (exec stringp) (arguments$ comp-db-arg-listp))
  (b* (((reterr) "" nil)
       (arguments (json::value-list-fix arguments))
       ((when (endp arguments))
        (reterr "The arguments array should have at least one element ~
                 for the name of the executable."))
       (exec (first arguments))
       ((unless (eq (json::value-kind exec) :string))
        (retmsg$ "Expected string type in \"arguments\" array of ~
                  JSON compilation database entry.
                  Found ~x0 instead."
                 (json::value-kind exec)))
       (exec-str (json::value-string->get exec))
       ((erp arguments$) (json-to-comp-db-arguments (rest arguments))))
    (retok exec-str arguments$))
  :hooks (:fix))

(define json-to-comp-db-get-exec-and-arguments
  ((entry json::valuep))
  :guard (equal (json::value-kind entry) :object)
  :returns (mv erp (exec stringp) (arguments$ comp-db-arg-listp))
  (b* (((reterr) "" nil)
       (entry (json::value-fix entry))
       (values (json::object-member-values "arguments" entry))
       ((when (endp values))
        (retmsg$ "JSON compilation entry has no \"arguments\" member. ~
                  Compilation entry: ~x0"
                 entry))
       ((unless (endp (rest values)))
        (retmsg$ "JSON compilation entry has multiple \"arguments\" members. ~
                  Compilation entry: ~x0"
                 entry))
       (value (first values)))
    (json::value-case
      value
      :array (json-to-comp-db-exec-and-arguments value.elements)
      :otherwise (retmsg$ "Expected array type in member field \"arguments\" ~
                           of JSON compilation database entry.
                           Found ~x0 instead."
                         (json::value-kind value))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db-entry
  ((entry json::valuep)
   (db comp-dbp)
   (warnings-onp booleanp)
   (warnings acl2::msg-listp))
  :returns (mv erp
               (db$ comp-dbp)
               (warnings$ acl2::msg-listp))
  (b* ((db (comp-db-fix db))
       (warnings (mbe :logic (if (acl2::msg-listp warnings) warnings nil)
                      :exec warnings))
       ((reterr) nil warnings))
    (json::value-case
      entry
      :object
      (b* (((erp file) (json-to-comp-db-get-file entry))
           (warnings (if (and warnings-onp
                              (assoc-equal file db))
                         (cons (msg$ "Found multiple entries for file: ~x0"
                                     file)
                               warnings)
                       warnings))
           ((erp output) (json-to-comp-db-get-output entry))
           ((erp directory) (json-to-comp-db-get-directory entry))
           ((erp exec arguments) (json-to-comp-db-get-exec-and-arguments entry))
           (entry (make-comp-db-entry :exec exec
                                      :directory directory
                                      :output output
                                      :arguments arguments)))
        (retok (cons (cons file entry) (comp-db-fix db)) warnings))
      :otherwise (retmsg$ "Expected object type in ~
                           JSON compilation database entry.
                           Found ~x0 instead."
                          (json::value-kind entry))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db-entry-list
  ((entries json::value-listp)
   (db comp-dbp)
   (warnings-onp booleanp)
   (warnings acl2::msg-listp))
  :returns (mv erp
               (db$ comp-dbp)
               (warnings$ acl2::msg-listp))
  (b* ((warnings (mbe :logic (if (acl2::msg-listp warnings) warnings nil)
                      :exec warnings))
       ((reterr) nil warnings)
       ((when (endp entries))
        (retok (comp-db-fix db) warnings))
       ((erp db warnings)
        (json-to-comp-db-entry (first entries) db warnings-onp warnings)))
    (json-to-comp-db-entry-list (rest entries) db warnings-onp warnings))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db
  ((value json::valuep)
   (warnings-onp booleanp)
   (warnings acl2::msg-listp))
  :returns (mv erp
               (db comp-dbp)
               (warnings$ acl2::msg-listp))
  (b* ((warnings (mbe :logic (if (acl2::msg-listp warnings) warnings nil)
                      :exec warnings))
       ((reterr) nil warnings))
    (json::value-case
      value
      :array (json-to-comp-db-entry-list value.elements
                                         nil
                                         warnings-onp
                                         warnings)
      :otherwise
      (retmsg$ "Expected array type at ~
                top level of JSON compilation database. ~
                Found ~x0 instead."
               (json::value-kind value))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-comp-db
  ((filename stringp)
   (warnings-onp booleanp)
   (warnings acl2::msg-listp)
   state)
  :returns (mv erp
               (db comp-dbp)
               (warnings$ acl2::msg-listp)
               state)
  :short "Parse a @(see compilation-database) from a file."
  (b* ((warnings (mbe :logic (if (acl2::msg-listp warnings) warnings nil)
                      :exec warnings))
       ((reterr) nil warnings state)
       ((erp parsed state)
        (acl2::parse-file-as-json filename state))
       ((erp value) (json::parsed-to-value parsed))
       ((erp db warnings) (json-to-comp-db value warnings-onp warnings)))
    (retok db warnings state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define comp-db-drop-non-c
  ((db comp-dbp))
  :returns (db$ comp-dbp)
  :short "Drop @(see compilation-database) entries which do not apply to
          @('.c') file or which don't include a @('-c') flag."
  (b* ((db (comp-db-fix db))
       ((when (endp db))
        nil)
       (file (acl2::str-fix (car (first db))))
       (entry (comp-db-entry-fix (cdr (first db))))
       (keep (and (str::strsuffixp ".c" file)
                  (member-equal (make-comp-db-arg :name "-c"
                                                  :separator ""
                                                  :value nil)
                                (comp-db-entry->arguments entry)))))
    (if keep
        (acons file
               entry
               (comp-db-drop-non-c (rest db)))
      (comp-db-drop-non-c (rest db))))
  :measure (acl2-count (comp-db-fix db))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable alistp-when-comp-dbp-rewrite)))
  :hooks (:fix))

(define comp-db-drop-shared
  ((db comp-dbp))
  :returns (db$ comp-dbp)
  :short "Drop @(see compilation-database) entries which produce shared or
          position-independent code."
  (b* ((db (comp-db-fix db))
       ((when (endp db))
        nil)
       (entry (cdr (first db)))
       (drop (or (member-equal (make-comp-db-arg :name "-fPIC"
                                                 :separator ""
                                                 :value nil)
                               (comp-db-entry->arguments entry))
                 (member-equal (make-comp-db-arg :name "-fpic"
                                                 :separator ""
                                                 :value nil)
                               (comp-db-entry->arguments entry)))))
    (if drop
        (comp-db-drop-shared (rest db))
      (cons (first db)
            (comp-db-drop-shared (rest db)))))
  :measure (acl2-count (comp-db-fix db))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable alistp-when-comp-dbp-rewrite)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define comp-db-arguments-keep-only-preprocessor-args
  ((arguments comp-db-arg-listp))
  :returns (arguments$ comp-db-arg-listp)
  (b* (((when (endp arguments))
        nil)
       (argument (first arguments))
       (argument-name (comp-db-arg->name argument))
       ((when (or (member-equal argument-name
                                '("-c" "-S" "-o" "-M" "-d" "-save-temps"))
                  (= 0 (length argument-name))
                  (not (eql (char argument-name 0) #\-))))
        (comp-db-arguments-keep-only-preprocessor-args (rest arguments))))
    (cons (comp-db-arg-fix argument)
          (comp-db-arguments-keep-only-preprocessor-args (rest arguments))))
  ;; TODO: why is this hook taking a little long?
  :hooks (:fix))

(define comp-db-keep-only-preprocessor-args
  ((db comp-dbp))
  :returns (db$ comp-dbp)
  :short "Filter out @(see compilation-database) arguments which are disruptive
          or irrelevant to preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
     "Generally, it seems easier to blacklist arguments which are disruptive to
      preprocessing than it is to whitelist the preprocessing-relevant
      arguments. Most flags do not prevent us from preprocessing, and some are
      surprisingly relevant to preprocessing (fir instance, the @('-fPIE') flag
      indicates a code-generation strategy, but it also causes two macros to be
      defined: @('__pie__') and @('__PIE__'))."))
  (b* ((db (comp-db-fix db))
       ((when (endp db))
        nil)
       (file (car (first db)))
       (entry (cdr (first db)))
       (arguments (comp-db-arguments-keep-only-preprocessor-args
                    (comp-db-entry->arguments entry)))
       (entry (change-comp-db-entry entry :arguments arguments)))
    (acons file
           entry
           (comp-db-keep-only-preprocessor-args (rest db))))
  :measure (acl2-count (comp-db-fix db))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable alistp-when-comp-dbp-rewrite)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define comp-db-arguments-absolute-dirs
  ((directory stringp)
   (arguments comp-db-arg-listp)
   state)
  :returns (arguments$ comp-db-arg-listp)
  (b* ((directory (acl2::str-fix directory))
       (arguments (comp-db-arg-list-fix arguments))
       ((when (endp arguments))
        nil)
       (argument (first arguments))
       ((comp-db-arg argument) argument)
       ((unless (member-equal argument.name *cc-options-dir*))
        (cons (comp-db-arg-fix argument)
              (comp-db-arguments-absolute-dirs directory (rest arguments) state)))
       (value (if argument.value
                  (ec-call (extend-pathname directory argument.value state))
                argument.value))
       (value (if (stringp value) value argument.value)))
    (cons (change-comp-db-arg argument :value value)
          (comp-db-arguments-absolute-dirs directory (rest arguments) state)))
  :measure (acl2-count (comp-db-arg-list-fix arguments))
  :hints (("Goal" :in-theory (enable comp-db-arg-list-fix)))
  :hooks ((:fix
           :hints (("Goal" :induct t
                           :expand ((comp-db-arguments-absolute-dirs
                                      directory
                                      (comp-db-arg-list-fix arguments)
                                      state))
                           :in-theory (disable acl2::member-of-cons
                                               acl2::member-when-atom))))))

(define comp-db-absolute-dirs
  ((db comp-dbp)
   state)
  :returns (db$ comp-dbp)
  :short "Make relative directories absolute in directory-valued arguments of a
          @(see compilation-database)."
  (b* ((db (comp-db-fix db))
       ((when (endp db))
        nil)
       (file (car (first db)))
       ((comp-db-entry entry) (cdr (first db)))
       (arguments (comp-db-arguments-absolute-dirs entry.directory
                                                   entry.arguments
                                                   state))
       (entry (change-comp-db-entry entry :arguments arguments)))
    (acons file
           entry
           (comp-db-absolute-dirs (rest db) state)))
  :measure (acl2-count (comp-db-fix db))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable alistp-when-comp-dbp-rewrite)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-escape-for-shell
  ((str stringp))
  :returns (str$ stringp)
  :short "Escape characters interpreted specially by the shell."
  (b* ((str (str::strsubst "\\" "\\\\" str))
       (str (str::strsubst "\"" "\\\"" str))
       (str (str::strsubst "$" "\\$" str))
       (str (str::strsubst "`" "\\`" str))
       (str (str::strsubst "!" "``!" str))
       (str (str::strsubst " " "\\ " str))
       (str (str::strsubst ";" "\\;" str))
       (str (str::strsubst "|" "\\|" str))
       (str (str::strsubst "&" "\\&" str))
       (str (str::strsubst "<" "\\<" str))
       (str (str::strsubst ">" "\\>" str))
       (str (str::strsubst "{" "\\{" str))
       (str (str::strsubst "}" "\\}" str))
       (str (str::strsubst "[" "\\[" str))
       (str (str::strsubst "]" "\\]" str))
       (str (str::strsubst "*" "\\*" str))
       (str (str::strsubst "?" "\\?" str))
       (str (str::strsubst "~" "\\~" str)))
    str))

(define comp-db-arguments-escape-for-shell
  ((arguments comp-db-arg-listp))
  :returns (arguments$ comp-db-arg-listp)
  (b* ((arguments (comp-db-arg-list-fix arguments))
       ((when (endp arguments))
        nil)
       (argument (first arguments))
       ((comp-db-arg argument) argument)
       (argument$ (change-comp-db-arg
                    argument
                    :name (string-escape-for-shell argument.name)
                    :value (if argument.value
                               (string-escape-for-shell argument.value)
                             nil))))
    (cons argument$
          (comp-db-arguments-escape-for-shell  (rest arguments))))
  :measure (acl2-count (comp-db-arg-list-fix arguments))
  :hints (("Goal" :in-theory (enable comp-db-arg-list-fix)))
  :hooks (:fix))

(define comp-db-escape-for-shell
  ((db comp-dbp))
  :returns (db$ comp-dbp)
  :short "Escape strings in arguments of a @(see compilation-database) for use
          in the shell."
  (b* ((db (comp-db-fix db))
       ((when (endp db))
        nil)
       (file (car (first db)))
       ((comp-db-entry entry) (cdr (first db)))
       (arguments
         (comp-db-arguments-escape-for-shell entry.arguments))
       (entry (change-comp-db-entry entry :arguments arguments)))
    (acons file
           entry
           (comp-db-escape-for-shell (rest db))))
  :measure (acl2-count (comp-db-fix db))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable alistp-when-comp-dbp-rewrite)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define to-preproc-db
  ((db comp-dbp)
   (drop-shared booleanp)
   state)
  :returns (db$ comp-dbp)
  :short "Transform a @(see compilation-database) to prepare for use in
          preprocessing."
  (b* ((db (comp-db-drop-non-c db))
       (db (if drop-shared (comp-db-drop-shared db) db))
       (db (comp-db-keep-only-preprocessor-args db))
       (db (comp-db-absolute-dirs db state))
       (db (comp-db-escape-for-shell db)))
    db)
  :hooks (:fix))

(define preproc-db-to-map
  ((db comp-dbp))
  :returns (map omap::mapp)
  (b* ((db (comp-db-fix db))
       ((when (endp db))
        nil)
       (file (car (first db)))
       ((comp-db-entry entry) (cdr (first db))))
    (omap::update file
                  (comp-db-arg-list-to-string-list entry.arguments)
                  (preproc-db-to-map (rest db))))
  :measure (acl2-count (comp-db-fix db))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable alistp-when-comp-dbp-rewrite)))
  :hooks (:fix))

(define to-preproc-map
  ((db comp-dbp)
   (drop-shared booleanp)
   state)
  :returns (map omap::mapp)
  (preproc-db-to-map (to-preproc-db db drop-shared state))
  :hooks (:fix))

(define preproc-map-from-comp-file
  ((filename stringp)
   (drop-shared booleanp)
   (warnings-onp booleanp)
   (warnings acl2::msg-listp)
   state)
  :returns (mv erp
               (map omap::mapp)
               (warnings acl2::msg-listp)
               state)
  (b* ((warnings (mbe :logic (if (acl2::msg-listp warnings) warnings nil)
                      :exec warnings))
       ((reterr) nil warnings state)
       ((erp db warnings state)
        (parse-comp-db filename warnings-onp warnings state)))
    (retok (to-preproc-map db drop-shared state) warnings state)))
