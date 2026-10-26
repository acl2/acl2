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
(include-book "kestrel/fty/string-stringlist-map" :dir :system)

(include-book "kestrel/json-parser/parse-json-file" :dir :system)
(include-book "kestrel/json/top" :dir :system)

(include-book "std/strings/strpos" :dir :system)
(include-book "std/strings/strsubst" :dir :system)
(include-book "std/strings/suffixp" :dir :system)

(include-book "kestrel/strings-light/split-string-last" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)
(include-book "kestrel/filepath/paths" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/strings-light/char" :dir :system))
(local (include-book "kestrel/typed-lists-light/string-listp" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (e/d (acons)
                       ;; This slows down a couple of proofs with excessive
                       ;; case splitting.
                       (acl2::member-of-cons))))

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
    (concatenate 'string arg.name arg.separator (or arg.value ""))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist comp-db-arg-list
  :short "A fixtype for lists of compiler arguments parsed from a @(see
          compilation-database)."
  :long
  (xdoc::topstring-p
    "Note that the order of argument is meaningful. For instance, the
     argument @('-U') cancels previous definitions.")
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
          (comp-db-arg-list-to-string-list (rest args)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: consider storing directories, source files, and outputs as structured
;; paths from the filepath::paths library once there is a fixtype for them.
;; For now, they are strings, which we parse and print back on demand (see
;; comp-db-absolute-path).
(fty::defprod comp-db-entry
  :short "A fixtype for entries parsed from a @(see compilation-database)."
  :long
  (xdoc::topstring-p
    "The @('exec') field is the executable which performs compilation. The
     @('directory') is the working directory in which to compile. The
     @('file') field is the source file being compiled, as it appears in the
     compilation database (it may be relative to @('directory')). Lastly,
     @('arguments') is a list of arguments provided to the compiler.")
  ((exec string)
   (directory string)
   (file string)
   (arguments comp-db-arg-list))
  :pred comp-db-entryp)

(defirrelevant irr-comp-db-entry
  :short "An irrelevant @(see comp-db-entry)."
  :type comp-db-entryp
  :body (make-comp-db-entry :exec "" :directory "" :file "" :arguments nil))

(encapsulate ()
  (local (set-induction-depth-limit 1))

  (fty::defalist comp-db
    :short "A fixtype for parsed @(see compilation-database)s."
    :long
    (xdoc::topstring
      (xdoc::p
        "This type is an alist associating outputs to "
        (xdoc::seetopic "comp-db-entry" "entries")
        ", in the order in which the entries appear in the compilation
         database. An output is the file produced by the compilation step, as
         it appears in the compilation database or as determined by "
        (xdoc::seetopic "comp-db-implicit-output" "the compiler's defaults")
        " when the database does not record it. It may be relative to the
         entry's directory, and it is @('nil') if the step produces no
         file.")
      (xdoc::p
        "Note that an output may be associated with "
        (xdoc::i "multiple")
        " entries. This may happen if, for instance, a single command compiles
         and links several source files: the compilation database then holds
         an entry for each source file, each with the linked program as its
         output."))
    :key-type acl2::string-option
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
  :short "C flags whose value follows after a white-space separator."
  '("-o" "-include" "-idirafter" "-imacros" "-imultilib" "-iprefix" "-iquote"
    "-isysroot" "-isystem" "-iwithprefix" "-iwithprefixbefore"
    ;; NOTE: `-I` is accepted as both space-separated and a conventional short
    ;;  argument. I.e., both `-I <dir>` and `-I<dir` are accepted.
    "-I"))

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
  :returns (mv (er? maybe-msgp) (file stringp))
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
                           JSON compilation database entry. ~
                           Found ~x0 instead."
                          (json::value-kind value)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db-get-output
  ((entry json::valuep))
  :guard (eq (json::value-kind entry) :object)
  :returns (mv (er? maybe-msgp) (output? string-optionp))
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
                           JSON compilation database entry. ~
                           Found ~x0 instead."
                         (json::value-kind value)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db-get-directory
  ((entry json::valuep))
  :guard (eq (json::value-kind entry) :object)
  :returns (mv (er? maybe-msgp) (directory stringp))
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
                           of JSON compilation database entry. ~
                           Found ~x0 instead."
                         (json::value-kind value)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db-try-parse-short-option
  ((argument stringp))
  :returns (mv erp (argument$ comp-db-argp))
  :short "Try to parse a short option."
  :long
  (xdoc::topstring-p
    "A short option is a dash, followed by a single uppercase letter, followed
     by a value. For instance, @('-I/usr/include').")
  (b* (((reterr) (irr-comp-db-arg))
       (argument (mbe :logic (acl2::str-fix argument) :exec argument)))
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
  (xdoc::topstring-p
    "For instance, @('-std=c17').")
  (b* (((reterr) (irr-comp-db-arg))
       (argument (mbe :logic (acl2::str-fix argument) :exec argument))
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
  :returns (mv (er? maybe-msgp) (arguments$ comp-db-arg-listp))
  :short "Parse an argument list into structured, name/value arguments."
  (b* (((reterr) nil)
       (arguments (json::value-list-fix arguments))
       ((when (endp arguments))
        (retok nil))
       (name-value? (first arguments))
       ((unless (eq (json::value-kind name-value?) :string))
        (retmsg$ "Expected string type in \"arguments\" array of ~
                  JSON compilation database entry. ~
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
                        JSON compilation database entry. ~
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
  :hints (("Goal" :in-theory (enable json::value-list-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db-exec-and-arguments
  ((arguments json::value-listp))
  :returns (mv (er? maybe-msgp) (exec stringp) (arguments$ comp-db-arg-listp))
  (b* (((reterr) "" nil)
       (arguments (json::value-list-fix arguments))
       ((when (endp arguments))
        (reterr "The arguments array should have at least one element ~
                 for the name of the executable."))
       (exec (first arguments))
       ((unless (eq (json::value-kind exec) :string))
        (retmsg$ "Expected string type in \"arguments\" array of ~
                  JSON compilation database entry. ~
                  Found ~x0 instead."
                 (json::value-kind exec)))
       (exec-str (json::value-string->get exec))
       ((erp arguments$) (json-to-comp-db-arguments (rest arguments))))
    (retok exec-str arguments$)))

(define json-to-comp-db-get-exec-and-arguments
  ((entry json::valuep))
  :guard (equal (json::value-kind entry) :object)
  :returns (mv (er? maybe-msgp) (exec stringp) (arguments$ comp-db-arg-listp))
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
                           of JSON compilation database entry. ~
                           Found ~x0 instead."
                         (json::value-kind value)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define comp-db-arguments-last-output
  ((arguments comp-db-arg-listp))
  :returns (output? acl2::string-optionp)
  :short "The value of the last @('-o') argument, if any."
  (b* (((when (endp arguments))
        nil)
       (output? (comp-db-arguments-last-output (rest arguments)))
       ((when output?)
        output?)
       ((comp-db-arg argument) (first arguments)))
    (and (equal argument.name "-o")
         argument.value)))

(define comp-db-default-output-name
  ((file stringp)
   (suffix stringp))
  :returns (name stringp)
  :short "The name a compiler gives an output file
          when there is no @('-o') argument."
  :long
  (xdoc::topstring-p
    "GCC and Clang name the output after the source file, without its
     directory, with the suffix of the source file (if any) replaced by
     @('suffix'). For instance, the source file @('lib/foo.c') and the
     suffix @('\".o\"') yield @('foo.o'). The output is placed in the working
     directory of the compilation, not in the directory of the source
     file.")
  (b* ((file (mbe :logic (acl2::str-fix file) :exec file))
       ((mv slashp - base) (acl2::split-string-last file #\/))
       (base (if slashp base file))
       ((mv - stem -) (acl2::split-string-last base #\.)))
    (concatenate 'string stem suffix)))

(define comp-db-implicit-output
  ((file stringp)
   (arguments comp-db-arg-listp))
  :returns (output? acl2::string-optionp)
  :short "The output of a compilation step, as determined by its arguments."
  :long
  (xdoc::topstring-p
    "This determines the output of @(see compilation-database) entries
     which have no @('output') member, following the behavior of GCC and
     Clang. With @('-fsyntax-only'), no file is produced, even with an
     @('-o') argument. Otherwise, the last @('-o') argument names the
     output. Without @('-o'), @('-E'), @('-M'), and @('-MM') write to
     standard output, while @('-S') and @('-c') produce an assembly and an
     object file, respectively, "
    (xdoc::seetopic "comp-db-default-output-name" "named after the source
                     file")
    ". With none of these flags, the compiler links a program named
     @('a.out').")
  (b* ((flags (comp-db-arg-list-to-string-list arguments))
       ((when (member-equal "-fsyntax-only" flags))
        nil)
       (output? (comp-db-arguments-last-output arguments))
       ((when output?)
        output?)
       ((when (or (member-equal "-E" flags)
                  (member-equal "-M" flags)
                  (member-equal "-MM" flags)))
        nil)
       ((when (member-equal "-S" flags))
        (comp-db-default-output-name file ".s"))
       ((when (member-equal "-c" flags))
        (comp-db-default-output-name file ".o")))
    "a.out"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db-entry
  ((entry json::valuep))
  :returns (mv (er? maybe-msgp)
               (output acl2::string-optionp)
               (entry$ comp-db-entryp))
  (b* (((reterr) nil (irr-comp-db-entry)))
    (json::value-case
      entry
      :object
      (b* (((erp file) (json-to-comp-db-get-file entry))
           ((erp output) (json-to-comp-db-get-output entry))
           ((erp directory) (json-to-comp-db-get-directory entry))
           ((erp exec arguments) (json-to-comp-db-get-exec-and-arguments entry))
           (output (or output (comp-db-implicit-output file arguments))))
        (retok output
               (make-comp-db-entry :exec exec
                                   :directory directory
                                   :file file
                                   :arguments arguments)))
      :otherwise (retmsg$ "Expected object type in ~
                           JSON compilation database entry. ~
                           Found ~x0 instead."
                          (json::value-kind entry)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db-entry-list
  ((entries json::value-listp))
  :returns (mv (er? maybe-msgp)
               (db comp-dbp))
  (b* (((reterr) nil)
       ((when (endp entries))
        (retok nil))
       ((erp output entry) (json-to-comp-db-entry (first entries)))
       ((erp db) (json-to-comp-db-entry-list (rest entries))))
    (retok (acons output entry db)))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable alistp-when-comp-dbp-rewrite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-comp-db
  ((value json::valuep))
  :returns (mv (er? maybe-msgp)
               (db comp-dbp))
  (b* (((reterr) nil))
    (json::value-case
      value
      :array (json-to-comp-db-entry-list value.elements)
      :otherwise
      (retmsg$ "Expected array type at ~
                top level of JSON compilation database. ~
                Found ~x0 instead."
               (json::value-kind value)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-comp-db
  ((filename stringp)
   state)
  :returns (mv erp
               (db comp-dbp)
               state)
  :short "Parse a @(see compilation-database) from a file."
  (b* (((reterr) nil state)
       (filename (mbe :logic (acl2::str-fix filename) :exec filename))
       ((erp parsed state)
        (acl2::parse-file-as-json filename state))
       ((erp value) (json::parsed-to-value parsed))
       ((erp db) (json-to-comp-db value)))
    (retok db state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define comp-db-drop-non-c
  ((db comp-dbp))
  :returns (db$ comp-dbp)
  :short "Drop @(see compilation-database) entries which do not apply to
          @('.c') file or which don't include a @('-c') flag."
  (b* ((db (comp-db-fix db))
       ((when (endp db))
        nil)
       (output (car (first db)))
       (entry (comp-db-entry-fix (cdr (first db))))
       (keep (and (str::strsuffixp ".c" (comp-db-entry->file entry))
                  (member-equal (make-comp-db-arg :name "-c"
                                                  :separator ""
                                                  :value nil)
                                (comp-db-entry->arguments entry)))))
    (if keep
        (acons output
               entry
               (comp-db-drop-non-c (rest db)))
      (comp-db-drop-non-c (rest db))))
  :measure (acl2-count (comp-db-fix db))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable alistp-when-comp-dbp-rewrite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: why is the fix hook of this function taking a little long?
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
          (comp-db-arguments-keep-only-preprocessor-args (rest arguments)))))

(define comp-db-keep-only-preprocessor-args
  ((db comp-dbp))
  :returns (db$ comp-dbp)
  :short "Filter out @(see compilation-database) arguments which are disruptive
          or irrelevant to preprocessing."
  :long
  (xdoc::topstring-p
    "Generally, it seems easier to blacklist arguments which are disruptive to
     preprocessing than it is to whitelist the preprocessing-relevant
     arguments. Most flags do not prevent us from preprocessing, and some are
     surprisingly relevant to preprocessing (for instance, the @('-fPIE') flag
     indicates a code-generation strategy, but it also causes two macros to be
     defined: @('__pie__') and @('__PIE__')).")
  (b* ((db (comp-db-fix db))
       ((when (endp db))
        nil)
       (output (car (first db)))
       (entry (cdr (first db)))
       (arguments (comp-db-arguments-keep-only-preprocessor-args
                    (comp-db-entry->arguments entry)))
       (entry (change-comp-db-entry entry :arguments arguments)))
    (acons output
           entry
           (comp-db-keep-only-preprocessor-args (rest db))))
  :measure (acl2-count (comp-db-fix db))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable alistp-when-comp-dbp-rewrite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define comp-db-absolute-path
  ((directory stringp)
   (path stringp))
  :returns (path$ stringp)
  :short "Make a path absolute, relative to a directory."
  :long
  (xdoc::topstring-p
    "This is purely syntactic: using the @(see filepath::paths) library, we
     resolve @('path') against @('directory') and remove @('.') and @('..')
     segments. Symbolic links are not followed, since the compiler names a
     file (for instance in quoted @('#include') directives and in
     @('__FILE__')) by the path it was given.")
  (b* ((directory (mbe :logic (acl2::str-fix directory) :exec directory))
       (path (mbe :logic (acl2::str-fix path) :exec path)))
    (filepath::path-to-string
      (filepath::normalize-path
        (filepath::resolve (filepath::parse-path directory)
                           (filepath::parse-path path))))))

(define comp-db-arguments-absolute-dirs
  ((directory stringp)
   (arguments comp-db-arg-listp))
  :returns (arguments$ comp-db-arg-listp)
  (b* ((directory (acl2::str-fix directory))
       (arguments (comp-db-arg-list-fix arguments))
       ((when (endp arguments))
        nil)
       (argument (first arguments))
       ((comp-db-arg argument) argument)
       ((unless (member-equal argument.name *cc-options-dir*))
        (cons (comp-db-arg-fix argument)
              (comp-db-arguments-absolute-dirs directory (rest arguments))))
       (value (and argument.value
                   (comp-db-absolute-path directory argument.value))))
    (cons (change-comp-db-arg argument :value value)
          (comp-db-arguments-absolute-dirs directory (rest arguments))))
  :measure (acl2-count (comp-db-arg-list-fix arguments))
  :hints (("Goal" :in-theory (enable comp-db-arg-list-fix))))

(define comp-db-absolute-paths
  ((db comp-dbp))
  :returns (db$ comp-dbp)
  :short "Make relative paths absolute in a @(see compilation-database)."
  :long
  (xdoc::topstring-p
    "The outputs, source files, and directory-valued arguments of each entry
     are made absolute "
    (xdoc::seetopic "comp-db-absolute-path" "relative to")
    " the entry's directory.")
  (b* ((db (comp-db-fix db))
       ((when (endp db))
        nil)
       (output (car (first db)))
       ((comp-db-entry entry) (cdr (first db)))
       (output (and output (comp-db-absolute-path entry.directory output)))
       (file (comp-db-absolute-path entry.directory entry.file))
       (arguments (comp-db-arguments-absolute-dirs entry.directory
                                                   entry.arguments))
       (entry (change-comp-db-entry entry :file file :arguments arguments)))
    (acons output
           entry
           (comp-db-absolute-paths (rest db))))
  :measure (acl2-count (comp-db-fix db))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable alistp-when-comp-dbp-rewrite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define comp-db-absolute-path-list
  ((directory stringp)
   (paths string-listp))
  :returns (paths$ string-listp)
  :short "Lift @(tsee comp-db-absolute-path) to lists."
  (if (endp paths)
      nil
    (cons (comp-db-absolute-path directory (first paths))
          (comp-db-absolute-path-list directory (rest paths)))))

(define comp-db-entries-with-output
  ((output stringp)
   (db comp-dbp))
  :returns (db$ comp-dbp)
  :short "The entries of a @(see compilation-database) with a given output."
  (b* ((output (mbe :logic (acl2::str-fix output) :exec output))
       (db (comp-db-fix db))
       ((when (endp db))
        nil)
       (rest-db (comp-db-entries-with-output output (rest db))))
    (if (equal (car (first db)) output)
        (cons (first db) rest-db)
      rest-db))
  :measure (acl2-count (comp-db-fix db)))

(define comp-db-entries-agree-p
  ((entry comp-db-entryp)
   (db comp-dbp))
  :returns (yes/no booleanp)
  :short "Check whether all entries of a @(see compilation-database) have the
          same source file and arguments as a given entry."
  (b* ((db (comp-db-fix db))
       ((when (endp db))
        t)
       ((comp-db-entry entry) entry)
       ((comp-db-entry other) (cdr (first db))))
    (and (equal other.file entry.file)
         (equal other.arguments entry.arguments)
         (comp-db-entries-agree-p entry (rest db))))
  :measure (acl2-count (comp-db-fix db)))

(define comp-db-select-outputs
  ((outputs string-listp)
   (db comp-dbp))
  :returns (mv (db$ comp-dbp)
               (missing string-listp)
               (ambiguous string-listp)
               (non-c string-listp))
  :short "Select the @(see compilation-database) entries
          which produce the given outputs."
  :long
  (xdoc::topstring-p
    "Besides the selected entries, we return the outputs which no entry
     produces, the outputs which several entries with different source files
     or arguments produce, and the outputs which are produced from source
     files other than @('.c') files. None of these outputs are selected.")
  (b* (((when (endp outputs))
        (mv nil nil nil nil))
       (output (acl2::str-fix (first outputs)))
       ((mv db$ missing ambiguous non-c)
        (comp-db-select-outputs (rest outputs) db))
       (entries (comp-db-entries-with-output output db))
       ((when (endp entries))
        (mv db$ (cons output missing) ambiguous non-c))
       (entry (cdr (first entries)))
       ((unless (comp-db-entries-agree-p entry (rest entries)))
        (mv db$ missing (cons output ambiguous) non-c))
       ((unless (str::strsuffixp ".c" (comp-db-entry->file entry)))
        (mv db$ missing ambiguous (cons output non-c))))
    (mv (acons output entry db$) missing ambiguous non-c))
  :verify-guards :after-returns
  :guard-hints
  (("Goal" :in-theory (enable alistp-when-comp-dbp-rewrite
                              acl2::consp-of-car-when-alistp-alt))))

(define comp-db-select
  ((db comp-dbp)
   (objects string-listp)
   (path stringp))
  :returns (mv (er? maybe-msgp)
               (db$ comp-dbp)
               (warnings acl2::msg-listp))
  :short "Select the @(see compilation-database) entries
          which produce the given object files."
  :long
  (xdoc::topstring
   (xdoc::p
     "The objects are typically the inputs of a link step, which compilation
      databases do not record. Relative object paths are taken relative to
      @('path'). Like the outputs of the compilation database (see @(tsee
      comp-db-absolute-paths)), they are made absolute syntactically.")
   (xdoc::p
     "It is an error if an object is produced by no entry, or by several
      entries which differ in their source files or arguments. In the latter
      case, we cannot know which of the entries produced the object being
      linked. Several entries may produce the same object if, for instance,
      the object was rebuilt while the compilation database was recorded, or
      if the build reuses an object file name. Entries which agree are
      collapsed into one.")
   (xdoc::p
     "Objects which are compiled from source files other than @('.c') files
      (e.g. assembly files) are not selected, with a warning."))
  (b* (((reterr) nil nil)
       (outputs (remove-duplicates-equal
                  (comp-db-absolute-path-list path objects)))
       ((mv db$ missing ambiguous non-c)
        (comp-db-select-outputs outputs db))
       (missing-msg
         (msg$ "No compilation database entry produces the object~#0~[~/s~] ~
                ~&0. The compilation database may be incomplete: for ~
                instance, it may have been recorded from a build which did ~
                not recompile every object, in which case a clean build may ~
                help."
               missing))
       (ambiguous-msg
         (msg$ "Several compilation database entries with different source ~
                files or arguments produce the object~#0~[~/s~] ~&0, so it ~
                cannot be determined how ~#0~[it was~/they were~] built."
               ambiguous))
       ((when (and missing ambiguous))
        (retmsg$ "~@0~%~%~@1" missing-msg ambiguous-msg))
       ((when missing)
        (reterr missing-msg))
       ((when ambiguous)
        (reterr ambiguous-msg))
       (warnings (and non-c
                      (list (msg$ "The object~#0~[~/s~] ~&0 ~#0~[is~/are~] not ~
                                   compiled from C source files, so ~
                                   ~#0~[it is~/they are~] not selected."
                                  non-c)))))
    (retok db$ warnings)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: support paths which are not contained within base
;; (i.e., allow ".." to backtrack higher up the base path as necessary).
(define comp-db-relativize-files
  ((db comp-dbp)
   (path stringp))
  :returns (mv (er? maybe-msgp)
               (db$ comp-dbp))
  (b* ((db (comp-db-fix db))
       ((reterr) db)
       (path (mbe :logic (acl2::str-fix path) :exec path))
       ((when (endp db))
        (retok nil))
       (output (car (first db)))
       ((comp-db-entry entry) (cdr (first db)))
       (base (filepath::parse-path path))
       (file (filepath::parse-path entry.file))
       ((unless (filepath::path-prefixp base file))
        (retmsg$ "Cannot make file path ~x0 relative to base path ~x1."
                 entry.file
                 path))
       (file (filepath::path-to-string (filepath::relativize-path base file)))
       ((erp rest-db)
        (comp-db-relativize-files (rest db) path)))
    (retok (cons (cons output (change-comp-db-entry entry :file file))
                 rest-db)))
  :measure (acl2-count (comp-db-fix db)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-escape-for-shell
  ((str stringp))
  :returns (str$ stringp)
  :short "Escape characters interpreted specially by the shell."
  (b* ((str (mbe :logic (acl2::str-fix str) :exec str))
       (str (str::strsubst "\\" "\\\\" str))
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
  :hints (("Goal" :in-theory (enable comp-db-arg-list-fix))))

(define comp-db-escape-for-shell
  ((db comp-dbp))
  :returns (db$ comp-dbp)
  :short "Escape strings in arguments of a @(see compilation-database) for use
          in the shell."
  (b* ((db (comp-db-fix db))
       ((when (endp db))
        nil)
       (output (car (first db)))
       ((comp-db-entry entry) (cdr (first db)))
       (arguments
         (comp-db-arguments-escape-for-shell entry.arguments))
       (entry (change-comp-db-entry entry :arguments arguments)))
    (acons output
           entry
           (comp-db-escape-for-shell (rest db))))
  :measure (acl2-count (comp-db-fix db))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable alistp-when-comp-dbp-rewrite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define to-preprocess-db
  ((db comp-dbp)
   (path stringp)
   state)
  :returns (mv (er? maybe-msgp)
               (db$ comp-dbp))
  :short "Transform a @(see compilation-database) to prepare for use in
          preprocessing."
  (b* (((reterr) (comp-db-fix db))
       (path (mbe :logic (acl2::str-fix path) :exec path))
       ((unless (canonical-pathname path t state))
        (retmsg$ "The specified path does not exist or is not a directory: ~x0"
                 path))
       (path (comp-db-absolute-path (acl2::str-fix (cbd)) path))
       (db (comp-db-drop-non-c db))
       (db (comp-db-keep-only-preprocessor-args db))
       (db (comp-db-absolute-paths db))
       ((erp db) (comp-db-relativize-files db path))
       (db (comp-db-escape-for-shell db)))
    (retok db)))

(define preprocess-db-to-map
  ((db comp-dbp))
  :returns (map acl2::string-stringlist-mapp)
  (b* ((db (comp-db-fix db))
       ((when (endp db))
        nil)
       ((comp-db-entry entry) (cdr (first db))))
    (omap::update entry.file
                  (comp-db-arg-list-to-string-list entry.arguments)
                  (preprocess-db-to-map (rest db))))
  :measure (acl2-count (comp-db-fix db))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable alistp-when-comp-dbp-rewrite))))

(define to-preprocess-map
  ((db comp-dbp)
   (path stringp)
   state)
  :returns (mv (er? maybe-msgp)
               (map acl2::string-stringlist-mapp))
  (b* (((reterr) nil)
       ((erp db$)
        (to-preprocess-db db path state)))
    (retok (preprocess-db-to-map db$))))

(define preprocess-map-from-comp-file
  ((filename stringp)
   (path stringp)
   (warnings acl2::msg-listp)
   state)
  :returns (mv erp
               (map acl2::string-stringlist-mapp)
               (warnings acl2::msg-listp)
               state)
  (b* ((warnings (mbe :logic (if (acl2::msg-listp warnings) warnings nil)
                      :exec warnings))
       ((reterr) nil warnings state)
       ((erp db state)
        (parse-comp-db filename state))
       ((erp map)
        (to-preprocess-map db path state)))
    (retok map warnings state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define show-warnings
  ((warnings acl2::msg-listp))
  (if (endp warnings)
      nil
    (prog2$ (cw "[Warning] ~@0~%" (first warnings))
            (show-warnings (rest warnings)))))

(define defpreprocess-map-fn
  ((const-name symbolp)
   (filename stringp)
   (path stringp)
   (show-warnings booleanp)
   state)
  :returns (mv erp event state)
  (b* ((const-name (mbe :logic (acl2::symbol-fix const-name) :exec const-name))
       ((mv erp map warnings state)
        (preprocess-map-from-comp-file filename
                                       path
                                       nil
                                       state))
       (- (if show-warnings
              (show-warnings warnings)
            nil))
       ((when erp)
        (mv erp nil state)))
    (acl2::value
      `(defconst ,const-name
         ',map))))

(defmacro defpreprocess-map
  (name
   &key
   file
   (path '".")
   (show-warnings 't))
  `(make-event
     (defpreprocess-map-fn
       ',name ',file ',path ',show-warnings state)))
