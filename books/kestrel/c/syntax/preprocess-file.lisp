; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "files")

(include-book "centaur/misc/tshell" :dir :system)
(include-book "kestrel/file-io-light/read-file-into-byte-list" :dir :system)
(include-book "kestrel/strings-light/split-string-last" :dir :system)
(include-book "oslib/dirname" :dir :system)
(include-book "oslib/mkdir" :dir :system)
(include-book "oslib/rmtree" :dir :system)
(include-book "oslib/tempfile" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "kestrel/typed-lists-light/string-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

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

(define preprocess-file
  ((file stringp
         "The file path of the C file to preprocess.")
   &key
   ((out (or (not out)
             (stringp out))
         "This specifies the output file to which the preprocessed file is
          saved. If @('nil'), a file will be created with a name and directory
          typical of temporary files (see @(see oslib::tempfile)).")
    'nil)
   ((save "If @('t'), the output file is saved. If @('nil'), the file is
           removed after reading it in. If @(':auto'), the default value, the
           file will be saved only if an explicit @('out') value is
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
                 \"-E\". The default value is @('(list \"-P\" \"-std=c17\")').
                 (The flag @('\"-P\"') suppresses the generation of
                 linemarkers and @('\"-std=c17\"') instructs the preprocessor
                 to use the C17 standard.)")
    ''("-P" "-std=c17"))
   (state 'state))
  :returns (mv (erp "@('nil') if successful, or the error @('msgp')
                     otherwise.")
               (filename stringp
                         "The output filename if it is saved, or @('\"\"')
                          otherwise.")
               (filedata filedatap
                         "The preprocessed @(see filedata) if read, or
                          @('(filedata nil)') otherwise.")
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
  (b* (((reterr) "" (filedata nil) state)
       (filename (canonical-pathname file nil state))
       ((unless (stringp filename))
        (reterr (msg "Filepath does not exist: ~x0"
                     file)))
       (- (acl2::tshell-ensure))
       (save (if (eq :auto save)
                 (and out t)
               save))
       ((erp out state)
        (b* (((reterr) nil state)
             ((when out)
              (retok (mbe :exec out
                          :logic (if (stringp out) out ""))
                     state))
             ((mv temp state)
              (oslib::tempfile filename))
             ((unless temp)
              (reterr (msg "Could not create temporary file for ~x0"
                           filename))))
          (retok temp state)))
       ((erp out-dirname state)
        (oslib::dirname out))
       ((erp state)
        (b* (((reterr) state)
             ((mv success state)
              (oslib::mkdir out-dirname))
             ((unless success)
              (reterr (msg "Could not make directory: ~x0"
                           out-dirname))))
          (retok state)))
       (preprocess-cmd
         (str::join (append (list* preprocessor "-E" extra-args)
                            (list filename ">" out))
                    " "))
       ((mv exit-status lines state)
        (acl2::tshell-call preprocess-cmd :print nil))
       ((unless (int= 0 exit-status))
        (reterr
          (msg
            "Preprocessing command ~x0 failed with nonzero exit status: ~x1~%~x2"
            preprocess-cmd
            exit-status
            (str::join lines
                       (string #\Newline)))))
       ((erp bytes state)
        (b* (((unless read)
              (retok nil state)))
          (acl2::read-file-into-byte-list out state)))
       ((when (stringp bytes))
        (reterr (msg "Error reading output file ~x0: ~x1"
                     out
                     bytes)))
       ((erp state)
        (b* (((reterr) state)
             ((when save)
              (retok state))
             ((mv success state)
              (oslib::rmtree out))
             ((unless success)
              (reterr (msg "Could not remove output file: ~x0"
                           out))))
          (retok state))))
    (retok (if save
               out
             "")
           (filedata (and read bytes))
           state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define preprocess-files
  ((files string-listp
          "The file path list specifying C file to preprocess.")
   &key
   ((path stringp
          "The base path to which @('files') are relative. By default, the
           value is @('\".\"') (the current working directory).")
    '".")
   ((out-dir (or (not out-dir)
                 (stringp out-dir))
             "This specifies the directory that preprocessed output files are
              saved to with posfix @('\".i\"'). If @('nil'), temporary files
              will be created (see @(see oslib::tempfile)).")
    'nil)
   ((save "If @('t'), the output files are saved. If @('nil'), the files are
           removed after reading them in. If @(':auto'), the default value,
           files will be saved only if an explicit @('out-dir') value is
           provided.")
    ':auto)
   ((preprocessor stringp
                  "The preprocessor executable to use. The default is
                   \"cpp\". Other reasonable values might be \"gcc\",
                   \"clang\", \"cc\", etc.")
    '"cpp")
   ((extra-args string-listp
                "Arguments to pass to the C preprocessor, in addition to
                 \"-E\". The default value is @('(list \"-P\" \"-std=c17\")').
                 (The flag @('\"-P\"') suppresses the generation of
                 linemarkers and @('\"-std=c17\"') instructs the preprocessor
                 to use the C17 standard.)")
    ''("-P" "-std=c17"))
   (state 'state))
  :returns (mv (erp "@('nil') if successful, or the first error @('msgp')
                     otherwise.")
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
  (b* (((reterr) (irr-fileset) state)
       ((when (endp files))
        (retok (fileset nil) state))
       (out (and out-dir
                 (b* ((filename (first files)))
                   (and (stringp filename)
                        (concatenate 'string
                                     out-dir
                                     "/"
                                     filename
                                     ".i")))))
       (filename (concatenate 'string path "/" (first files)))
       ((erp - filedata state)
        (preprocess-file filename
                         :out out
                         :save save
                         :preprocessor preprocessor
                         :extra-args extra-args
                         :state state))
       ((erp (fileset fileset) state)
        (preprocess-files (rest files)
                          :path path
                          :out-dir out-dir
                          :save save
                          :preprocessor preprocessor
                          :extra-args extra-args
                          :state state)))
    (retok (fileset (omap::update (filepath (first files))
                                  filedata
                                  fileset.unwrap))
           state))
  :hints (("Goal" :in-theory (enable o< o-finp emptyp)))
  :verify-guards :after-returns)
