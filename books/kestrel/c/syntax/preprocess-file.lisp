; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "file-paths")
(include-book "files")

(include-book "centaur/misc/tshell" :dir :system)
(include-book "kestrel/file-io-light/read-file-into-byte-list" :dir :system)
(include-book "kestrel/strings-light/split-string-last" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "oslib/dirname" :dir :system)
(include-book "oslib/mkdir" :dir :system)
(include-book "oslib/rmtree" :dir :system)
(include-book "oslib/tempfile" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

(local (include-book "kestrel/typed-lists-light/string-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (in-theory (disable acl2::error1+)))
(local (in-theory (disable (:e acl2::tshell-call))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessing
  :parents (syntax-for-tools)
  :short "An interface to C preprocessors."
  :long
  (xdoc::topstring
   (xdoc::p
     "A collection of tools to invoke an external C preprocessor.")
   (xdoc::p
     "These tools appeal to a configurable C preprocessor, and the prerequisite
      dependencies may not be present on all systems. For books which use the
      default preprocessor \"cpp\", certification may be controlled with
      the @(see build::uses-cpp) @(see build::cert_param) flag.")
   (xdoc::p
     "The community books Makefile will autodetect whether \"cpp\" is
      available, and exclude books appropriately. Certification of such books
      may be suppressed by manually undefining the Makefile variable
      \"OS_HAS_CPP\". E.g., to run a regression excluding books calling cpp:")
   (xdoc::code
     "OS_HAS_CPP= make regression")
   (xdoc::p
     "Further @(see build::cert_param) flags may need to be defined if using a
      C preprocessor other than \"cpp\"."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; byte-listp rules

(defruledl byte-listp-becomes-unsigned-byte-listp-8
  (equal (byte-listp x)
         (unsigned-byte-listp 8 x))
  :enable (unsigned-byte-listp
           byte-listp
           bytep)
  :induct (byte-listp x))

(defrulel byte-listp-of-read-file-into-byte-list
  (byte-listp (mv-nth 1 (acl2::read-file-into-byte-list filename state)))
  :enable (byte-listp-becomes-unsigned-byte-listp-8))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; filepath-setp rules

(defrulel filepath-setp-of-cdr-when-filepath-setp-cheap
  (implies (filepath-setp setp)
           (filepath-setp (cdr setp)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable (filepath-setp))

(defrulel filepath-setp-compound-recognizer
  (implies (filepath-setp files)
           (true-listp files))
  :rule-classes :compound-recognizer)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro er-soft-with (val str &rest str-args)
  `(acl2::er-soft+ __function__ t ,val ,str ,@str-args))

(defrulel mv-nth-0-of-error1+
  (equal (mv-nth 0 (acl2::error1+ ctx erp val str alist state))
         erp)
  :enable (acl2::error1+))

(defrulel mv-nth-1-of-error1+
  (equal (mv-nth 1 (acl2::error1+ ctx erp val str alist state))
         val)
  :enable (acl2::error1+))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define preprocess-file
  ((file filepathp
         "The C file to preprocess.")
   &key
   ((out (or (not out)
             (stringp out))
         "This specifies the output file to which the preprocessed file is
          saved. If @('nil'), a file will be created with a name and directory
          typical of temporary files (see @(see oslib::tempfile)).")
    'nil)
   ((save "If @('t'), the output file is saved. If @('nil'), the file is
           removed after reading it in. If @(':auto'), the default value, the
           file will be saved only if an explicilty @('out') value is
           provided.")
    ':auto)
   ((read "If @('t'), the output file will be read and returned. If you want
           the output file to be created but not read, pass @('nil'). The
           default is @('t').")
    't)
   ((preprocessor stringp
                  "The preprocessor executable to use. The default is
                   \"cpp\". Other reasonable values might be \"gcc\",
                   \"clang\", \"cc\", etc.")
    '"cpp")
   ((extra-args string-listp
                "Arguments to pass to the C preprocessor, in addition to
                 \"-E\". The default value is @('(list \"-P\")') (the flag
                 @('\"-P\"') suppresses the generation of linemarkers).")
    ''("-P"))
   (state 'state))
  :returns (mv erp
               (pair "A pair whose first value is the output file (if it is
                      saved, @('nil') otherwise), and whose second value is the
                      preprocessed @(see filedata) (if read, @('nil')
                      otherwise).")
               state)
  :parents (preprocessing)
  :short "Preprocess a single file."
  :long
  (xdoc::topstring
   (xdoc::p
     "This function preprocesses a @(see filepathp) using the system's C
      preprocessor. See @(see preprocess-files) for a simlilar utility which
      handles a set of files.")
   (xdoc::p
     "By default, we pass the @('\"-P\"') flag to the preprocessor to disable
      linemarkers. This behavior may be overriden by explicitly providing a
      @(':extra-args') value."))
  (macrolet
   ((iferr () '(cons "" (filepath nil))))
   (b* ((filename (filepath->unwrap file))
        ((unless (stringp filename))
         (er-soft-with (iferr)
                       "Filepath is not a string: ~x0"
                       filename))
        (- (acl2::tshell-ensure))
        (save (if (eq :auto save)
                  (and out t)
                save))
        ((er out :iferr (iferr))
         (if out
             (value (mbe :exec out
                         :logic (if (stringp out) out "")))
           (b* (((mv temp state)
                 (oslib::tempfile filename)))
             (if temp
                 (value temp)
               (er-soft-with (iferr)
                             "Could not create temporary file for ~x0"
                             filename)))))
        ((er out-dirname :iferr (iferr))
         (oslib::dirname out))
        ((er -)
         (b* (((mv success state)
               (oslib::mkdir out-dirname)))
           (if success
               (value nil)
             (er-soft-with (iferr)
                           "Could not make directory: ~x0" out-dirname))))
        (preprocess-cmd
          (str::join (append (list* preprocessor "-E" extra-args)
                             (list filename ">" out))
                     " "))
        ((mv exit-status -)
         (acl2::tshell-call preprocess-cmd :print nil :save nil))
        ((unless (int= 0 exit-status))
         (er-soft-with
           (iferr)
           "Preprocessing command ~x0 failed with nonzero exit status: ~x1"
           preprocess-cmd
           exit-status))
        ((er bytes :iferr (iferr))
         (if read
             (acl2::read-file-into-byte-list out state)
           (value nil)))
        ((when (stringp bytes))
         (er-soft-with
           (iferr)
           "Error reading output file ~x0: ~x1"
           out
           bytes))
        ((er - :iferr (iferr))
         (if save
             (value nil)
           (b* (((mv success state)
                 (oslib::rmtree out)))
             (if success
                 (value nil)
               (er-soft-with (iferr)
                             "Could not remove output file: ~x0"
                             out))))))
     (value (cons (and save out)
                  (and read (filedata bytes))))))

  ///

  (defrule consp-of-mv-nth-1-of-preprocess-file
    (consp (mv-nth 1 (preprocess-file-fn filename
                                         save
                                         out
                                         read
                                         preprocessor
                                         extra-args
                                         state)))
    :rule-classes ((:rewrite) (:type-prescription))
    :enable (preprocess-file-fn))

  (defrule stringp-of-car-of-mv-nth-1-of-preprocess-file
    (implies (and out save)
             (stringp (car (mv-nth 1 (preprocess-file-fn filename
                                                         save
                                                         out
                                                         read
                                                         preprocessor
                                                         extra-args
                                                         state)))))
    :rule-classes ((:rewrite) (:type-prescription))
    :enable (preprocess-file-fn))

  (defrule filedatap-of-cdr-of-mv-nth-1-of-preprocess-file
    (implies read
             (filedatap (cdr (mv-nth 1 (preprocess-file-fn filename
                                                           save
                                                           out
                                                           read
                                                           preprocessor
                                                           extra-args
                                                           state)))))
    :enable (preprocess-file-fn)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define preprocess-files
  ((files filepath-setp
          "The set of C files to preprocess.")
   &key
   ((out-dir (or (not out-dir)
                 (stringp out-dir))
             "This specifies the directory that preprocessed output files are
              saved to with posfix \".i\". If @('nil'), temporary files will be
              created (see @(see oslib::tempfile))).")
    'nil)
   ((save "If @('t'), the output files are saved. If @('nil'), the files are
           removed after reading them in. If @(':auto'), the default value,
           files will be saved only if an explicilty @('out-dir') value is
           provided.")
    ':auto)
   ((preprocessor stringp
                  "The preprocessor executable to use. The default is
                   \"cpp\". Other reasonable values might be \"gcc\",
                   \"clang\", \"cc\", etc.")
    '"cpp")
   ((extra-args string-listp
                "Arguments to pass to the C preprocessor, in addition to
                 \"-E\". The default value is @('(list \"-P\")') (the flag
                 @('\"-P\"') suppresses the generation of linemarkers).")
    ''("-P"))
   (state 'state))
  :returns (mv erp
               (map filesetp
                    "The map from filepaths to preprocessed filedata.")
               state)
  :parents (preprocessing preprocess-file)
  :short "Preprocess a set of files."
  :long
  (xdoc::topstring
   (xdoc::p
     "This function preprocesses a @(see filepath-setp). See @(see
      preprocess-file) for a similar utility which operates on individuals
      files."))
  (b* (((when (emptyp files))
        (value (fileset nil)))
       (out (and out-dir
                 (b* ((filename (filepath->unwrap (head files))))
                   (and (stringp filename)
                        (concatenate 'string
                                     out-dir
                                     "/"
                                     filename
                                     ".i")))))
       ((er (cons - filedata) :iferr (fileset nil))
        (preprocess-file (head files)
                         :out out
                         :save save
                         :preprocessor preprocessor
                         :extra-args extra-args
                         :state state))
       ((er (fileset fileset) :iferr (fileset nil))
        (preprocess-files (rest files)
                          :out-dir out-dir
                          :save save
                          :preprocessor preprocessor
                          :extra-args extra-args
                          :state state)))
    (value (fileset (omap::update (head files)
                                  filedata
                                  fileset.unwrap))))
  :hints (("Goal" :in-theory (enable o< o-finp emptyp)))
  :verify-guards :after-returns)
