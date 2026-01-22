; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "preprocessor-lexemes")
(include-book "macro-tables")
(include-book "preprocessor-states")
(include-book "preprocessor-messages")
(include-book "preprocessor-reader")
(include-book "preprocessor-lexer")
(include-book "preprocessor-printer")
(include-book "files")

(include-book "kestrel/file-io-light/read-file-into-byte-list" :dir :system)
(include-book "std/strings/strpos" :dir :system)
(include-book "std/strings/strrpos" :dir :system)

(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor
  :parents (preprocessing)
  :short "A preprocessor for C."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide a preprocessor for C that, unlike typical preprocessors,
     preserves the information about the @('#include') directives
     under conditions that should be often satisfied in practical code.
     That is, it does not replace such directives
     with the (preprocessed) contents of the referenced files,
     but it otherwise performs the rest of the preprocessing.
     This is only done under certain conditions;
     in general, the C preprocessor operates at a low lexical level,
     making it difficult to preserve code structure in general
     (in those cases, our preprocessor expands the included files in place,
     like typical preprocessors).")
   (xdoc::p
    "Our preprocessor maps a list of file paths
     to a file set (see @(see files)):
     it preprocesses all the files with the given file paths,
     as well as all the files directly and indirectly included.
     The resulting file set contains entries
     for all the files with the given file paths,
     as well as for zero or more @(see self-contained) files
     that are included directly or indirectly by the given list of files.")
   (xdoc::p
    "The input to our preprocessor is similar to @(tsee input-files),
     in the sense that the files to preprocess are specified by
     (1) a base directory path and (2) a list of file paths.
     The base directory path may be absolute,
     or relative to the "
    (xdoc::seetopic "cbd" "connected book directory")
    ". The file paths in the list are relative to the base directory.")
   (xdoc::p
    "The file set output of our preprocessor has keys
     that are either absolute or relative paths.
     The latter are relative to the base directory (1),
     and they are used not only for the files listed in (2),
     but also for any additional files that are directly or indirectly included
     via @('#include') directives with double quotes only (not angle brackets):
     our preprocessor's search strategy
     for @('#include') directives with double quotes,
     in line with GCC "
    (xdoc::ahref "https://gcc.gnu.org/onlinedocs/cpp/Search-Path.html"
                 "[CPPM:2.3]")
    ", resolves the included files relative to
     the directory of the including file;
     in the output file set,
     the keys for these additional files are
     the paths of the files relative to the base directory.
     In contrast, absolute path keys in the output file set are for
     files included via @('#include') directives with angle brackets,
     which our preprocessor searches in certain directories,
     unrelated to the base directory.
     [C17:6.10.2] gives leeway in how included file are resolved;
     our preprocessor uses an approch similar to GCC [CPPM:2.3].
     The directories where to search files included with angle brackets
     are passed as an additional input to our preprocessor.")
   (xdoc::p
    "Our preprocessor
     reads characters from files,
     lexes them into lexemes,
     and parses the lexemes while executing the preprocessing directives.
     The resulting sequences of lexemes is then turned into characters
     that are written (printed) to files.
     The resulting file set is amenable to our parser
     (more precisely, it will be, once we have extended our parser
     to accept @('#include') directives in certain places).
     Our preprocessor preserves white space and comments when possible,
     but some layout (i.e. white space) changes are inherent to preprocessing,
     some comments may be impossible to preserve
     (e.g. if they occur within macro parameters),
     and some preserved comments may no longer apply to preprocessed code
     (e.g. comments talking about macros).")
   (xdoc::p
    "Currently some of this preprocessor's code duplicates, at some level,
     some of the code in the @(see parser)
     (including the @(see lexer) and the @(see reader)).
     At some point we should integrate the preprocessor with the parser.")
   (xdoc::p
    "This preprocessor is still work in progress."))
  :order-subtopics (preprocessor-lexemes
                    macro-tables
                    preprocessor-states
                    preprocessor-messages
                    preprocessor-reader
                    preprocessor-lexer
                    preprocessor-printer
                    t)
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc self-contained
  :short "Notion of self-contained file in our preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "In our preprocessor, a self-contained file is one that,
     when included by another file, is not expanded in place;
     that is, it is left as an @('#include').
     This is not always possible,
     because the semantics of @('#include')
     is to replace the directive with the file and continue preprocessing:
     nothing prevents the replacement from referencing previous macros.")
   (xdoc::p
    "For instance, consider a file of the form")
   (xdoc::codeblock
    "..."
    "#define M ..."
    "..."
    "#include FILE"
    "...")
   (xdoc::p
    "Where we intentionally wrote @('FILE'),
     without double quotes or angle brackets, and without extensions,
     because those details do not matter here.")
   (xdoc::p
    "Since @('#include') is substitution in place,
     it is possible for @('FILE') to reference @('M')
     in a way that needs @('M') to be defined.
     This means that @('FILE') would not be legal if preprocessed alone,
     but the including file is legal.
     Indeed, the result of preprocessing @('#include FILE')
     depends on where that directive occurs;
     different occurrences may result in
     possibly very different replacements,
     e.g. if @('M') affects conditional inclusion [C17:6.10.1].")
   (xdoc::p
    "However, the situation above is not a common case.
     In particular, if @('FILE') is part of a library,
     it would not even know about @('M').
     Thus, the result of preprocessing @('FILE')
     is often independent from where it occurs,
     and it always results in the same replacement
     (but we discuss include guards below).
     That is, @('FILE') is ``self-contained''.")
   (xdoc::p
    "In such common cases,
     our preprocessor avoids expanding the inclusion in place,
     and instead adds the result of preprocessing @('FILE')
     to the file set returned as result of preprocessing a list of files
     (see @(see preprocessor)).
     This is why, in addition to one element for each specified file,
     our preprocessor also returns zero or more additional elements,
     in the file set resulting from the preprocessor.")
   (xdoc::p
    "The files explicitly specified to the preprocessor
     are always self-contained files,
     because they are preprocessed from the top level of our preprocessor,
     not via a direct or indirect @('#include').")
   (xdoc::p
    "The notion of self-contained file described above
     has to be relaxed slightly for include guards,
     i.e. when @('FILE') has a form like")
   (xdoc::codeblock
    "#ifndef FILE_H"
    "#define FILE_H"
    "..."
    "#endif")
   (xdoc::p
    "This is a well-known pattern to avoid
     including the same file multiple times.
     In this case, strictly speaking @('FILE') depends on
     a macro that may be externally defined, i.e. @('FILE_H'),
     but in a way that makes @('FILE') nonetheless self-contained.")
   (xdoc::p
    "The precise notion of self-contained file,
     and how our preprocessor checks it,
     particularly in the face of include guards,
     is still work in progress.
     It will be described more precisely as we advance the implementation.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod scfile
  :short "Fixtype of self-contained files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures the result of preprocessing a @(see self-contained) file:
     the list of lexemes that forms the file after preprocessing
     (which can be printed to bytes into a file in the file system),
     and the macros defined by the file (bundled into a single scope alist)."))
  ((lexemes plexeme-listp)
   (macros macro-scopep))
  :pred scfilep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-scfile
  :short "An irrelevant self-contained file."
  :type scfilep
  :body (scfile nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist string-scfile-alist
  :short "Fixtype of alists from strings to self-contained files."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use these alists to keep track of which files
     have been already preprocessed and are @(see self-contained).")
   (xdoc::p
    "These alists always have unique keys, i.e. there are no shadowed pairs;
     this is not enforced in this fixtype.
     The keys are file paths,
     either absolute,
     or relative to the base directory passed to the @(see preprocessor).")
   (xdoc::p
    "When all the files have been preprocessed,
     this alist contains all the results from the preprocessing,
     which is turned into a file set.
     The non-@(see self-contained) files are not part of this alist,
     because they have been expanded in place."))
  :key-type string
  :val-type scfile
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred string-scfile-alistp
  :prepwork ((set-induction-depth-limit 1))

  ///

  (defruled scfilep-of-cdr-of-assoc-equal-when-string-scfile-alistp
    (implies (and (string-scfile-alistp alist)
                  (assoc-equal key alist))
             (scfilep (cdr (assoc-equal key alist))))
    :induct t
    :enable assoc-equal)

  (defrule len-of-string-scfile-alist-fix-upper-bound
    (<= (len (string-scfile-alist-fix alist))
        (len alist))
    :rule-classes :linear
    :induct t
    :enable (len string-scfile-alist-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-scfile-alist-to-filepath-filedata-map
  ((alist string-scfile-alistp))
  :returns (map filepath-filedata-mapp)
  :short "Turn (1) an alist from string to self-contained files
          into (2) a map from file paths to file data."
  :long
  (xdoc::topstring
   (xdoc::p
    "The strings are wrapped into file paths;
     as mentioned in @(tsee string-scfile-alist),
     the alist has unique keys, so the order of the alist is immaterial.
     The lists of lexemes are printed to bytes,
     obtaining the file datas.")
   (xdoc::p
    "This is called on the alist at the end of the preprocessing."))
  (b* (((when (endp alist)) nil)
       ((cons string scfile) (car (string-scfile-alist-fix alist)))
       (bytes (plexemes-to-bytes (scfile->lexemes scfile)))
       (filepath (filepath string))
       (filedata (filedata bytes))
       (map (string-scfile-alist-to-filepath-filedata-map (cdr alist))))
    (omap::update filepath filedata map))
  :verify-guards :after-returns
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum macrep-mode
  :short "Fixtype of macro replacement modes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Among other things,
     the preprocessor goes through a sequence of lexemes,
     expanding the macros in them
     (including rescanning and further replacement [C17:6.10.3.4]),
     until a stopping criterion is met.
     The details of the stopping criterion,
     and of some aspects of macro replacement,
     vary depending on the situation.
     We capture these different modes of operations via this fixtype:")
   (xdoc::ul
    (xdoc::li
     "The @(':text') mode is for text lines (see ABNF grammar),
      as well as for the rest of the lines of certain directives.
      The stopping criterion is the end of the line,
      and macro replacement is the normal one.")
    (xdoc::li
     "The @(':expr') mode is for the lines that must form constant expressions,
      just after @('#if') or @('#elif').
      The stopping criterion is the end of the line,
      and macro replacement is modified
      to handle the @('defined') operator [C17:6.10.1/1]
      and to replace identifiers with 0 [C17:6.10.1/4].")
    (xdoc::li
     "The @(':arg-nonlast'), @(':arg-last'), and @(':arg-dots') modes
      are for arguments of function-like macros [C17:6.10.3/10],
      where macro replacement is the normal one,
      and the stopping criterion is
      a comma for @(':arg-nonlast'),
      and a right parenthesis for @(':arg-last') and @(':arg-dots').
      For a macro without the ellipsis,
      all the arguments except the last one
      are handled in the @(':arg-nonlast') mode,
      while the last argument is handled in the @(':arg-last') mode;
      if the macro has no parameters, there are no arguments to handle.
      For a macro with the ellipsis,
      all the arguments corresponding to named parameters
      are handled in the @(':arg-nonlast') mode,
      while the remaining argument/arguments (corresponding to the ellipsis)
      is/are handled in the @(':arg-dots') mode.
      The distinction between @(':arg-last') and @(':arg-dots') is that
      the former signals an error if a comma is encountered,
      while the latter does not,
      because the comma is part of the arguments associated to @('__VA_ARGS__')
      [C17:
      (The right parentheses and commas mentioned here are the ones
      outside nested matching parentheses [C17:6.10.3/10] [C17:6.10.3/11].)"))
   (xdoc::p
    "In situations in which the preprocessor goes through lexemes
     with a certain stopping criterion but without macro replacements,
     we do not use any of the modes defined by this fixtype.
     Instead, we use simpler functions that
     recursively go through lexemes until the stopping criterion.
     An example is when collecting the replacement list of a macro
     in a @('#define') directive."))
  (:line ())
  (:expr ())
  (:arg-nonlast ())
  (:arg-last ())
  (:arg-dots ())
  :pred macrep-modep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum groupend
  :short "Fixtype of endings of groups."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here by `group' we mean the preprocessing notion
     captured by the @('group') nonterminal in the ABNF grammar.
     More accurately, the endings formalized here refer to optional groups:
     a group consists of one or more group parts,
     but these endings apply to sequences of zero or more group parts
     (see @(tsee pproc-*-group-part)),
     which are isomorphic to optional groups.")
   (xdoc::p
    "Looking at the grammar, an (optional) group may end:
     with the end of file, for the top-level group;
     or with one of the directives @('#elif'), @('#else'), and @('#endif')
     (which are not part of the group itself, but follow it),
     for groups nested in @('#if'), @('#ifdef'), and @('#ifndef') directives.
     This fixtype captures these four possibilities."))
  (:eof ())
  (:elif ())
  (:else ())
  (:endif ())
  :pred groupendp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-groupend
  :short "An irrelevant group ending."
  :type groupendp
  :body (groupend-eof))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption groupend-option
  groupend
  :short "Fixtype of optional endings of groups."
  :pred groupend-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define path-absolutep ((path stringp))
  :returns (yes/no booleanp)
  :short "Check if a path is absolute."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check whether it starts with a slash.
     This is for Unix-like system."))
  (and (> (length path) 0)
       (eql (char path 0) #\/))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define h-char-list-to-string ((hchars h-char-listp))
  :returns (mv erp (string stringp))
  :short "Convert, to an ACL2 string,
          a list of characters usable in header names between angle brackets."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the characters must be ASCII for now, otherwise we return an error."))
  (b* (((reterr) "")
       ((erp chars) (h-char-list-to-char-list hchars)))
    (retok (str::implode chars)))
  :prepwork
  ((define h-char-list-to-char-list ((hchars h-char-listp))
     :returns (mv erp (chars character-listp))
     :parents nil
     (b* (((reterr) nil)
          ((when (endp hchars)) (retok nil))
          (hchar (car hchars))
          (code (h-char->code hchar))
          ((unless (< code 128))
           (reterr (msg "Unsupported header name character with code ~x0."
                        code)))
          (char (code-char code))
          ((erp chars) (h-char-list-to-char-list (cdr hchars))))
       (retok (cons char chars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define q-char-list-to-string ((qchars q-char-listp))
  :returns (mv erp (string stringp))
  :short "Convert, to an ACL2 string,
          a list of characters usable in header names between double quotes."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the characters must be ASCII for now, otherwise we return an error."))
  (b* (((reterr) "")
       ((erp chars) (q-char-list-to-char-list qchars)))
    (retok (str::implode chars)))
  :prepwork
  ((define q-char-list-to-char-list ((qchars q-char-listp))
     :returns (mv erp (chars character-listp))
     :parents nil
     (b* (((reterr) nil)
          ((when (endp qchars)) (retok nil))
          (qchar (car qchars))
          (code (q-char->code qchar))
          ((unless (< code 128))
           (reterr (msg "Unsupported header name character with code ~x0."
                        code)))
          (char (code-char code))
          ((erp chars) (q-char-list-to-char-list (cdr qchars))))
       (retok (cons char chars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define resolve-included-file ((including-file stringp)
                               (included-file header-namep)
                               (base-dir stringp)
                               (include-dirs string-listp)
                               state)
  :returns (mv erp
               (resolved-included-file stringp)
               (file-bytes byte-listp)
               state)
  :short "Resolve a header name to a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when the file at path @('including-file')
     contains an @('#include') directive with header name @('included-file'),
     to resolve the latter to a path, which is returned by this function,
     along with the bytes obtained by reading the resolved file.
     The @('including-file') path is either absolute,
     or relative to the base directory @('base-dir') passed as input,
     which is passed as input to the @(see preprocessor).
     The list @('include-dirs') is a list of absolute paths
     to search for included files,
     generally unrelated to @('base-dir'), and used, in particular,
     to specify where the C standard library headers are
     (this list of directories is another input to the @(see preprocessor)).")
   (xdoc::p
    "There are three cases:")
   (xdoc::ol
    (xdoc::li
     "If @('included-file') has angle brackets,
      the header name is converted to an ASCII path
      relative to one of the directories in @('include-dirs'),
      which are tried in order until a file can be read.
      If a file can be read,
      its absolute path is returned as the @('resolved-included-file') result,
      along with the bytes that form the file.
      Otherwise, we return an error: file resolution failed.")
    (xdoc::li
     "If @('included-file') has double quotes
      and @('including-file') is absolute,
      the header name is converted to an ASCII path
      relative to the directory of @('including-file').
      If a file can be read there,
      its absolute path is returned as the @('resolved-included-file') result,
      along with the bytes that form the file.
      Otherwise, the ASCII path is searched
      relative to the directories in @('include-dirs'), in order,
      and things proceed as in the previous case,
      as if the header name had angle brackets [C17:6.10.2/3].")
    (xdoc::li
     "If @('included-file') has double quotes
      and @('including-file') is relative (to @('base-dir')),
      the header name is converted to an ASCII path
      relative to the directory of @('including-file').
      If a file can be read there,
      we refactor its path into the @('base-dir') prefix and the rest
      (we give a clarifying example shortly)
      and return the rest as the @('resolved-included-file') result,
      along with the bytes that form the file.
      For example, assume that
      @('base-dir') is @('/one/two'),
      @('including-file') is @('three/including.c'), and
      @('included-file') is @('four/included.h').
      Then the directory of the including file is @('/one/two/three'),
      the included file is @('/one/two/three/four/included.h'),
      and its path is refactored into @('/one/two') (i.e. @('base-dir'))
      and the rest @('three/four/included.h').
      Note that, since @('including-file') is relative to @('base-dir'),
      @('base-dir') must be a prefix (proper or not) of
      the directory of @('including-file').
      In other words, the path of the included file
      is relativized to @('base-dir').
      However, if the file cannot be read,
      the ASCII path is searched
      relative to the directories in @('include-dirs'), in order,
      and things proceed as in the first case,
      as if the header name had angle brackets [C17:6.10.2/3]."))
   (xdoc::p
    "To find the directory @('dir-of-including-file') of the including file,
     we see whether @('including-file') contains at least a slash.
     It it does, we keep the characters up and including the last slash.
     If it does not, it means that @('including-file')
     cannot be an absolute path (because otherwise it would start with slash),
     and thus it must be relative to @('base-dir'),
     so the latter is the directory of the including file.")
   (xdoc::p
    "The following examples may be helpful to follow the code:")
   (xdoc::codeblock
    "// base-dir = base (absolute or relative)"
    ""
    "/absolute/including.c:  // dir-of-including-file = /absolute/"
    "#include \"file.h\"     // included-file-path = /absolute/file.h"
    "#include \"sub/file.h\" // included-file-path = /absolute/sub/file.h"
    ""
    "relative/including.c:   // dir-of-including-file = base/relative/"
    "#include \"file.h\"     // included-file-path = base/relative/file.h"
    "#include \"sub/file.h\" // included-file-path = base/relative/sub/file.h"
    ""
    "including.c:            // dir-of-including-file = base/"
    "#include \"file.h\"     // included-file-path = base/file.h"
    "#include \"sub/file.h\" // included-file-path = base/sub/file.h"))
  (declare (ignore include-dirs))
  (b* (((reterr) "" nil state)
       ((when (header-name-case included-file :angles))
        (reterr (msg "Angle-bracket #include not yet supported."))) ; TODO
       ((erp included-file-ascii)
        (q-char-list-to-string (header-name-quotes->chars included-file)))
       (base-dir/ (str::cat base-dir "/"))
       (dir-of-including-file
        (b* ((last-slash-position (str::strrpos "/" including-file)))
          (if last-slash-position
              (if (path-absolutep including-file)
                  (subseq including-file 0 (1+ last-slash-position))
                (str::cat base-dir/
                          (subseq including-file 0 (1+ last-slash-position))))
            base-dir/)))
       (included-file-path (str::cat dir-of-including-file included-file-ascii))
       (resolved-included-file
        (if (path-absolutep including-file)
            included-file-path
          (b* ((must-be-0
                (str::strpos base-dir/ included-file-path))
               ((unless (eql must-be-0 0))
                (raise "Internal error: ~x0 does not start with ~x1."
                       included-file-path base-dir/)
                ""))
            (subseq included-file-path (length base-dir/) nil))))
       ((mv erp bytes state)
        (acl2::read-file-into-byte-list included-file-path state))
       ;; TODO: search INCLUDE-DIRS if ERP
       ((when erp)
        (reterr (msg "Cannot read file ~x0." included-file-path))))
    (retok resolved-included-file bytes state))
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable length string-append)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-lexeme ((headerp booleanp) (ppstate ppstatep))
  :returns (mv erp
               (lexeme? plexeme-optionp)
               (span spanp)
               (new-ppstate ppstatep))
  :short "Read a lexeme during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there are pending lexmarks,
     we return the first one if it is a lexeme;
     we throw an error if it is a marker,
     because that should never happen when this function is called.
     If there are no pending lexmarks,
     we call @(tsee plex-lexeme) to lex a lexeme from the input.")
   (xdoc::p
    "The @('headerp') flag is passed to @(tsee plex-lexeme),
     if we find no pending lexmark.
     It is an invariant that pending lexmarks are never header names;
     thus, in this case the @('headerp') flag is irrelevant."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil (irr-span) ppstate)
       (lexmarks (ppstate->lexmarks ppstate))
       (size (ppstate->size ppstate))
       ((when (consp lexmarks))
        (b* ((lexmark (car lexmarks))
             ((unless (lexmark-case lexmark :lexeme))
              (raise "Internal error: unexpected marker ~x0." lexmark)
              (reterr t))
             (lexeme (lexmark-lexeme->lexeme lexmark))
             (span (lexmark-lexeme->span lexmark))
             ((unless (> size 0))
              (raise "Internal error: size is 0 but there are pending lexemes.")
              (reterr t))
             (ppstate (update-ppstate->size (1- size) ppstate))
             (ppstate (update-ppstate->lexmarks (cdr lexmarks) ppstate)))
          (retok lexeme span ppstate)))
       ((erp lexeme? span ppstate) (plex-lexeme headerp ppstate))
       ((when (not lexeme?)) (retok nil span ppstate))
       (lexeme lexeme?))
    (retok lexeme span ppstate))
  :no-function nil

  ///

  (defret ppstate->size-of-read-lexeme-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable nfix))))

  (defret ppstate->size-of-read-lexeme-cond
    (implies (and (not erp)
                  lexeme?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-lexeme ((lexeme plexemep) (span spanp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Unread a lexeme."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add the lexeme to the list of pending lexmarks.
     See @(tsee ppstate)."))
  (push-lexmark (make-lexmark-lexeme :lexeme lexeme :span span) ppstate)

  ///

  (defret ppstate->size-of-unread-lexeme
    (equal (ppstate->size new-ppstate)
           (1+ (ppstate->size ppstate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-lexmark ((ppstate ppstatep))
  :returns (mv erp
               (lexmark? lexmark-optionp)
               (new-ppstate ppstatep))
  :short "Read a lexmark during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there are pending lexmarks, we return the first one.
     If there are no pending lexmarks,
     we call @(tsee plex-lexeme) to lex a lexeme from the input,
     and we return the lexmark obtained by combining lexeme and span."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil ppstate)
       (lexmarks (ppstate->lexmarks ppstate))
       (size (ppstate->size ppstate))
       ((when (consp lexmarks))
        (b* ((lexmark (car lexmarks))
             ((unless (> size 0))
              (raise "Internal error: ~
                      size is 0 but there are pending lexmarks.")
              (reterr t))
             (ppstate (update-ppstate->size (1- size) ppstate))
             (ppstate (update-ppstate->lexmarks (cdr lexmarks) ppstate)))
          (retok lexmark ppstate)))
       ((erp lexeme? span ppstate) (plex-lexeme nil ppstate))
       ((when (not lexeme?)) (retok nil ppstate)))
    (retok (make-lexmark-lexeme :lexeme lexeme? :span span) ppstate))
  :no-function nil

  ///

  (defret ppstate->size-of-read-lexmark-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable nfix))))

  (defret ppstate->size-of-read-lexmark-cond
    (implies (and (not erp)
                  lexmark?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-token-handling-markers ((stop-at-newline-p booleanp)
                                     (disabled ident-listp)
                                     (ppstate ppstatep))
  :returns (mv erp
               (token plexemep)
               (span spanp)
               (new-disabled ident-listp)
               (new-ppstate ppstatep))
  :short "Read a token, handling any markers along the way."
  :long
  (xdoc::topstring
   (xdoc::p
    "We skip over comments and white space,
     where white space excludes/includes new lines
     according to whether @('stop-at-newline-p') is @('t')/@('nil').
     We handle any markers encountered along the way,
     as in @(tsee pproc-lexemes).
     We must find a token, which we return;
     otherwise this fails.")
   (xdoc::p
    "This is used only in @(tsee pproc-lexemes).
     The multiset (modeled as a list) of disabled macro names
     is taken as input and returned as output."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) (irr-plexeme) (irr-span) nil ppstate)
       ((erp lexmark ppstate) (read-lexmark ppstate)))
    (cond
     ((not lexmark) ; EOF
      (reterr-msg :where (position-to-msg (ppstate->position ppstate))
                  :expected "a lexmark"
                  :found "end of file"))
     ((lexmark-case lexmark :start) ; start(M)
      (b* ((name (lexmark-start->macro lexmark))
           (disabled (cons name disabled)))
        (read-token-handling-markers stop-at-newline-p disabled ppstate)))
     ((lexmark-case lexmark :end) ; end(M)
      (b* ((name (lexmark-end->macro lexmark))
           (disabled (remove1-equal name (ident-list-fix disabled))))
        (read-token-handling-markers stop-at-newline-p disabled ppstate)))
     (t ; lexeme
      (b* ((lexeme (lexmark-lexeme->lexeme lexmark))
           (span (lexmark-lexeme->span lexmark)))
        (cond
         ((and stop-at-newline-p
               (plexeme-case lexeme :newline)) ; EOL
          (reterr-msg :where (position-to-msg (span->start span))
                      :expected "a comment or ~
                                 non-new-line white space or ~
                                 a token"
                      :found (plexeme-to-msg lexeme)))
         ((plexeme-tokenp lexeme) ; token
          (retok lexeme span (ident-list-fix disabled) ppstate))
         (t ; comment or white space
          (read-token-handling-markers stop-at-newline-p disabled ppstate)))))))
  :no-function nil
  :measure (ppstate->size ppstate)

  ///

  (defret plexeme-tokenp-of-read-token-handling-markers
    (plexeme-tokenp token)
    :hints (("Goal" :induct t :in-theory (enable irr-plexeme))))

  (defret ppstate->size-of-read-punctuator-handling-markers-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-read-punctuator-handling-markers-cond
    (implies (not erp)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-ptoken ((ppstate ppstatep))
  :returns (mv erp
               (nontokens plexeme-listp)
               (token? plexeme-optionp)
               (token-span spanp)
               (new-ppstate ppstatep))
  :short "Read a token during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "We lex zero or more non-tokens, until we find a token.
     We return the list of non-tokens, and the token with its span.
     If we reach the end of file, we return @('nil') as the token,
     and a span consisting of just the current position."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil nil (irr-span) ppstate)
       ((erp lexeme span ppstate) (read-lexeme nil ppstate))
       ((when (not lexeme)) (retok nil nil span ppstate))
       ((when (plexeme-tokenp lexeme)) (retok nil lexeme span ppstate))
       ((erp nontokens token token-span ppstate) (read-ptoken ppstate)))
    (retok (cons lexeme nontokens) token token-span ppstate))
  :measure (ppstate->size ppstate)

  ///

  (defret plexeme-list-not-tokenp-of-read-ptoken
    (plexeme-list-not-tokenp nontokens)
    :hints (("Goal" :induct t)))

  (defret plexeme-tokenp-of-read-ptoken
    (implies token?
             (plexeme-tokenp token?))
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-read-ptoken-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-read-ptoken-cond
    (implies (and (not erp)
                  token?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-token/newline-header? ((headerp booleanp) (ppstate ppstatep))
  :returns (mv erp
               (nontoknls plexeme-listp)
               (toknl? plexeme-optionp)
               (toknl-span spanp)
               (new-ppstate ppstatep))
  :short "Read a token or new line during preprocessing,
          with the option of recognizing a header name or not."
  :long
  (xdoc::topstring
   (xdoc::p
    "New lines are significant in most situations during preprocessing,
     i.e. they are not just white space to skip over.
     In such situations,
     we need to skip over non-new-line white space and comments,
     but stop when we encounter either a new line or a token.")
   (xdoc::p
    "This is always called through one of its wrappers,
     @(tsee read-token/newline) and @(tsee read-token/newline-after-include).
     The former is used in almost all situations (hence the shorter name),
     while the latter is use just in one situation."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil nil (irr-span) ppstate)
       ((erp lexeme span ppstate) (read-lexeme headerp ppstate))
       ((when (not lexeme)) (retok nil nil span ppstate))
       ((when (plexeme-token/newline-p lexeme)) (retok nil lexeme span ppstate))
       ((erp nontoknls toknl toknl-span ppstate)
        (read-token/newline-header? headerp ppstate)))
    (retok (cons lexeme nontoknls)
           toknl
           toknl-span
           ppstate))
  :measure (ppstate->size ppstate)

  ///

  (defret plexeme-list-not-token/newline-p-of-read-token/newline-header?
    (plexeme-list-not-token/newline-p nontoknls)
    :hints (("Goal" :induct t)))

  (defret plexeme-token/newline-p-of-read-token/newline-header?
    (implies token?
             (plexeme-token/newline-p toknl?))
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-read-token/newline-header?-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-read-token/newline-header?-cond
    (implies (and (not erp)
                  toknl?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-token/newline ((ppstate ppstatep))
  :returns (mv erp
               (nontoknls plexeme-listp)
               (toknl? plexeme-optionp)
               (toknl-span spanp)
               (new-ppstate ppstatep))
  :short "Read a token or new line during preprocessing,
          in most situations."
  :long
  (xdoc::topstring
   (xdoc::p
    "In most situations, we are not looking for a header name,
     so we pass @('nil') as flag to @(tsee read-token/newline-header?)."))
  (read-token/newline-header? nil ppstate)

  ///

  (defret plexeme-list-not-token/newline-p-of-read-token/newline
    (plexeme-list-not-token/newline-p nontoknls))

  (defret plexeme-token/newline-p-of-read-token/newline
    (implies toknl?
             (plexeme-token/newline-p toknl?)))

  (defret ppstate->size-of-read-token/newline-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear)

  (defret ppstate->size-of-read-token/newline-cond
    (implies (and (not erp)
                  toknl?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-token/newline-after-include ((ppstate ppstatep))
  :returns (mv erp
               (nontoknls plexeme-listp)
               (toknl? plexeme-optionp)
               (toknl-span spanp)
               (new-ppstate ppstatep))
  :short "Read a token or new line during preprocessing,
          just after reading a @('#include')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Just after reading a @('#inclue'),
     is the only situation in which we are looking for a header name."))
  (read-token/newline-header? t ppstate)

  ///

  (defret plexeme-list-not-token/newline-p-of-read-token/newline-after-include
    (plexeme-list-not-token/newline-p nontoknls))

  (defret plexeme-token/newline-p-of-read-token/newline-after-include
    (implies token?
             (plexeme-token/newline-p toknl?)))

  (defret ppstate->size-of-read-token/newline-after-include-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear)

  (defret ppstate->size-of-read-token/newline-after-include-cond
    (implies (and (not erp)
                  toknl?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-macro-params ((ppstate ppstatep))
  :returns (mv erp
               (params ident-listp)
               (ellipsis booleanp)
               (new-ppstate ppstatep))
  :short "Read the parameters of a function-like macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called just after reading the left parenthesis,
     and it consumes the right parenthesis if successful.
     If successful, this function returns the list of named parameters,
     and a boolean indicating whether there is an ellipsis parameter or not.")
   (xdoc::p
    "We could not find, in [C17], any particular prohibition
     on the identifiers used as named parameters.
     Clang even accepts @('__VA_ARGS__'),
     regardless of whether the macro has ellipsis or not;
     if it has ellipsis,
     the @('__VA_ARGS__') used as named parameter takes precedence,
     in the sense that, when the macro is instantiated,
     all the occurrences of @('__VA_ARGS__') in the macro's replacement list
     are replaced with the argument for the named parameter @('__VA_ARGS__'),
     and not with the argument(s) for the ellipsis parameter.
     However, for now we prefer to prohibit @('__VA_ARGS__')
     as a named parameter, in case [C17] somehow intends that.")
   (xdoc::p
    "We read the next token or new line, skipping white space and comments.
     If we find a right parenthesis, there are no parameters.
     If we find an ellipsis, that is the only parameter;
     we ensure there is a right parenthesis just after, consuming it.
     If we find an identifier, it is the first named parameter;
     we use an auxiliary recursive function to read any following parameters,
     which consumes the right parenthesis,
     and we combine those with the first parameter.")
   (xdoc::p
    "We also ensure that the parameters have distinct names [C17:6.10.3/6]."))
  (b* ((ppstate (ppstate-fix ppstate)) ; # define name (
       ((reterr) nil nil ppstate)
       ((erp & token span ppstate) (read-token/newline ppstate)))
    (cond
     ((and token ; # define name ( )
           (plexeme-punctuatorp token ")"))
      (retok nil nil ppstate))
     ((and token ; # define name ( ...
           (plexeme-punctuatorp token "..."))
      (b* (((erp & token2 span2 ppstate) (read-token/newline ppstate))
           ((unless (and token2 ; # define name ( ... )
                         (plexeme-punctuatorp token2 ")")))
            (reterr-msg :where (position-to-msg (span->start span2))
                        :expected "a right parenthesis"
                        :found (plexeme-to-msg token2))))
        (retok nil t ppstate)))
     ((and token
           (plexeme-case token :ident)) ; # define name ( param
      (b* ((param (plexeme-ident->ident token))
           ((when (equal param (ident "__VA_ARGS__")))
            (reterr (msg "Disallowed macro parameter '__VA_ARGS__' at ~x0."
                         (span-to-msg span))))
           ((erp params ellipsis ppstate) ; # define ( params[...] )
            (read-macro-params-rest ppstate))
           ((when (member-equal param params))
            (reterr (msg "Duplicate macro parameter ~x0 at ~x1."
                         param (span-to-msg span)))))
        (retok (cons param params) ellipsis ppstate)))
     (t ; # define name ( EOF/other
      (reterr-msg :where (position-to-msg (span->start span))
                  :expected "a right parenthesis or ~
                             an ellipsis or ~
                             an identifer"
                  :found (plexeme-to-msg token)))))
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable true-listp-when-ident-listp)))

  :prepwork
  ((define read-macro-params-rest ((ppstate ppstatep))
     :returns (mv erp
                  (params ident-listp)
                  (ellipsis booleanp)
                  (new-ppstate ppstatep))
     :parents nil
     (b* ((ppstate (ppstate-fix ppstate)) ; # define name ( 1stparam
          ((reterr) nil nil ppstate)
          ((erp & token span ppstate) (read-token/newline ppstate)))
       (cond
        ((and token ; # define name ( 1stparam ,
              (plexeme-punctuatorp token ","))
         (b* (((erp & token2 span2 ppstate) (read-token/newline ppstate)))
           (cond
            ((and token2 ; # define name ( 1stparam , ...
                  (plexeme-punctuatorp token2 "..."))
             (b* (((erp & token3 span3 ppstate) (read-token/newline ppstate))
                  ((unless (and token3 ; # define name ( 1stparam , ... )
                                (plexeme-punctuatorp token3 ")")))
                   (reterr-msg :where (position-to-msg (span->start span3))
                               :expected "a right parenthesis"
                               :found (plexeme-to-msg token2))))
               (retok nil t ppstate)))
            ((and token2 ; # define name ( 1stparam , param
                  (plexeme-case token2 :ident))
             (b* ((param (plexeme-ident->ident token2))
                  ((when (equal param (ident "__VA_ARGS__")))
                   (reterr (msg "Disallowed macro parameter ~
                                 '__VA_ARGS__' at ~x0."
                                (span-to-msg span2))))
                  ((erp params ellipsis ppstate)
                   (read-macro-params-rest ppstate))
                  ;; # define name ( 1stparam , param params[...] )
                  ((when (member-equal param params))
                   (reterr (msg "Duplicate macro parameter ~x0 at ~x1."
                                param (span-to-msg span2)))))
               (retok (cons param params) ellipsis ppstate)))
            (t ; # define name ( 1stparam , EOF/other
             (reterr-msg :where (position-to-msg (span->start span2))
                         :expected "an ellipsis or an identifier"
                         :found (plexeme-to-msg token2))))))
        ((and token ; # define name ( 1stparam )
              (plexeme-punctuatorp token ")"))
         (retok nil nil ppstate))
        (t ; # define name ( 1stparam EOF/other
         (reterr-msg :where (position-to-msg (span->start span))
                     :expected "a comma or a right parenthesis"
                     :found (plexeme-to-msg token)))))
     :no-function nil
     :measure (ppstate->size ppstate)
     :verify-guards :after-returns
     :guard-hints (("Goal" :in-theory (enable true-listp-when-ident-listp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-macro-object-replist ((name identp) (ppstate ppstatep))
  :returns (mv erp
               (replist plexeme-listp)
               (new-ppstate ppstatep))
  :short "Read the replacement list of an object-like macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the lexemes,
     collecting tokens,
     normalizing white space and comments to single spaces,
     and stopping at new line.
     We use a flag, initially @('t') and then always @('nil'),
     to exclude any initial white space and comments,
     which are not part of the replacement list [C17:6.10.3/7].
     We ensure that @('##') does not occur
     at the start or end of the replacement list [C17:6.10.3.3/1]."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil ppstate)
       ((erp replist ppstate) (read-macro-object-replist-loop t ppstate))
       ((when (and (consp replist)
                   (or (plexeme-hashhashp (car replist))
                       (plexeme-hashhashp (car (last replist))))))
        (reterr (msg "The replacement list of ~x0 starts or ends with ##."
                     (ident-fix name)))))
    (retok replist ppstate))

  :prepwork
  ((define read-macro-object-replist-loop ((startp booleanp) (ppstate ppstatep))
     :returns (mv erp
                  (replist plexeme-listp)
                  (new-ppstate ppstatep))
     :parents nil
     (b* ((ppstate (ppstate-fix ppstate))
          ((reterr) nil ppstate)
          ((erp nontoknls toknl span ppstate) (read-token/newline ppstate)))
       (cond
        ((not toknl) ; EOF
         (reterr-msg :where (position-to-msg (span->start span))
                     :expected "a token or ~
                                a comment or ~
                                a new line or ~
                                other white space"
                     :found (plexeme-to-msg toknl)))
        ((plexeme-case toknl :newline) ; EOL
         (retok nil ppstate))
        (t ; token
         (b* (((erp replist ppstate) ; token replist
               (read-macro-object-replist-loop nil ppstate))
              (replist (cons toknl replist))
              (replist (if (and nontoknls
                                (not startp))
                           (cons (plexeme-spaces 1) replist)
                         replist)))
           (retok replist ppstate)))))
     :no-function nil
     :measure (ppstate->size ppstate)

     ///

     (defret plexeme-list-token/space-p-of-read-macro-object-replist-loop
       (plexeme-list-token/space-p replist)
       :hints
       (("Goal"
         :induct t
         :in-theory (e/d (plexeme-token/space-p
                          plexeme-tokenp
                          plexeme-token/newline-p)
                         (plexeme-token/newline-p-of-read-token/newline)))
        '(:use plexeme-token/newline-p-of-read-token/newline)))))

  ///

  (defret plexeme-list-token/space-p-of-read-macro-object-replist
    (plexeme-list-token/space-p replist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-macro-function-replist ((name identp)
                                     (params ident-listp)
                                     (ellipsis booleanp)
                                     (ppstate ppstatep))
  :returns (mv erp
               (replist plexeme-listp)
               (hash-params ident-listp)
               (new-ppstate ppstatep))
  :short "Read the replacement list of a function-like macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Similarly to @(tsee read-macro-object-replist),
     we go through the list,
     collecting tokens,
     normalizing white space and comments to single spaces,
     and stopping at new line.
     We keep track, in the @('previous') input of the recursive function,
     of the previous token, initially @('nil').
     We use this for various purposes:")
   (xdoc::ul
    (xdoc::li
     "To determine when a macro parameter
      is immediately preceded by @('#') or @('##')
      or immediately followed by @('##'),
      in which case we add it to the @('hash-params') result.
      If the macro has an ellipsis parameter,
      we include @('__VA_ARGS__') in this check against @('#') and @('##').")
    (xdoc::li
     "To discard white space and comments before the first token,
      which are not part of the replacement list [C17:6.10.3/7].")
    (xdoc::li
     "To ensure that @('#') is followed by a parameter [C17:6.10.3.1/1],
      possibly including @('__VA_ARGS__') if the macro has ellipsis.")
    (xdoc::li
     "To ensure that @('##') does not occur
      at the start or end of the replacement list [C17:6.10.3.3/1]."))
   (xdoc::p
    "We also ensure that @('__VA_ARGS__') occurs in the replacement list
     only if the macro has ellipsis."))
  (read-macro-function-replist-loop name nil params ellipsis ppstate)

  :prepwork
  ((define read-macro-function-replist-loop ((name identp)
                                             (previous plexeme-optionp)
                                             (params ident-listp)
                                             (ellipsis booleanp)
                                             (ppstate ppstatep))
     :returns (mv erp
                  (replist plexeme-listp)
                  (hash-params ident-listp)
                  (new-ppstate ppstatep))
     :parents nil
     (b* ((ppstate (ppstate-fix ppstate))
          ((reterr) nil nil ppstate)
          ((erp nontoknls toknl span ppstate) (read-token/newline ppstate)))
       (cond
        ((not toknl) ; EOF
         (reterr-msg :where (position-to-msg (span->start span))
                     :expected "a token or ~
                                a comment or ~
                                a new line or ~
                                other white space"
                     :found (plexeme-to-msg toknl)))
        ((plexeme-case toknl :newline) ; EOL
         (b* (((when (and previous
                          (plexeme-hashp previous))) ; # EOL
               (reterr (msg "The replacement list of ~x0 must not end with #."
                            (ident-fix name))))
              ((when (and previous
                          (plexeme-hashhashp previous))) ; ## EOL
               (reterr (msg "The replacement list of ~x0 must not end with ##."
                            (ident-fix name)))))
           (retok nil nil ppstate)))
        ((plexeme-case toknl :ident) ; ident
         (b* ((ident (plexeme-ident->ident toknl))
              ((when (and (equal ident (ident "__VA_ARGS__"))
                          (not ellipsis)))
               (reterr (msg "The replacement list of ~x0 ~
                             must not contain '__VA_ARGS__', ~
                             because it has no ellipsis."
                            (ident-fix name))))
              (paramp (or (member-equal ident (ident-list-fix params))
                          (and (equal (ident->unwrap ident) "__VA_ARGS__")
                               ellipsis)))
              ((when (and previous
                          (plexeme-hashp previous) ; # ident
                          (not paramp)))
               (reterr (msg "The replacement list of ~x0 ~
                             must not contain a # ~
                             not immediately followed by a parameter."
                            (ident-fix name))))
              ((erp replist hash-params ppstate)
               (read-macro-function-replist-loop name
                                                 toknl
                                                 params
                                                 ellipsis
                                                 ppstate))
              (hash-params
               (if (and previous
                        (or (plexeme-hashp previous) ; # ident (PARAMP = T)
                            (and (plexeme-hashhashp previous) ; ## ident
                                 paramp)))
                   (add-to-set-equal ident hash-params)
                 hash-params))
              (replist (cons toknl replist))
              (replist (if (and previous nontoknls)
                           (cons (plexeme-spaces 1) replist)
                         replist)))
           (retok replist hash-params ppstate)))
        ((plexeme-hashhashp toknl) ; ##
         (b* (((when (not previous)) ; nothing ##
               (reterr
                (msg "The replacement list of ~x0 must not start with ##."
                     (ident-fix name))))
              ((when (and previous
                          (plexeme-hashp previous))) ; # ##
               (reterr (msg "The replacement list of ~x0 ~
                             must not contain a # ~
                             not immediately followed by a parameter."
                            (ident-fix name))))
              ((erp replist hash-params ppstate)
               (read-macro-function-replist-loop name
                                                 toknl
                                                 params
                                                 ellipsis
                                                 ppstate))
              (hash-params
               (if (plexeme-case previous :ident) ; ident ##
                   (b* ((ident (plexeme-ident->ident previous)))
                     (if (or (member-equal ident (ident-list-fix params))
                             (and (equal (ident->unwrap ident) "__VA_ARGS__")
                                  ellipsis)) ; param ##
                         (add-to-set-equal ident hash-params)
                       hash-params))
                 hash-params))
              (replist (cons toknl replist))
              (replist (if nontoknls
                           (cons (plexeme-spaces 1) replist)
                         replist)))
           (retok replist hash-params ppstate)))
        (t ; other token
         (b* (((when (and previous
                          (plexeme-hashp previous))) ; # token
               (reterr (msg "The replacement list of ~x0 ~
                             must not contain a # ~
                             not immediately followed by a parameter."
                            (ident-fix name))))
              ((erp replist hash-params ppstate)
               (read-macro-function-replist-loop name
                                                 toknl
                                                 params
                                                 ellipsis
                                                 ppstate))
              (replist (cons toknl replist))
              (replist (if (and previous nontoknls)
                           (cons (plexeme-spaces 1) replist)
                         replist)))
           (retok replist hash-params ppstate)))))
     :no-function nil
     :measure (ppstate->size ppstate)
     :verify-guards :after-returns
     :guard-hints (("Goal" :in-theory (enable true-listp-when-ident-listp)))

     ///

     (defret plexeme-list-token/space-p-of-read-macro-function-replist-loop
       (plexeme-list-token/space-p replist)
       :hints
       (("Goal"
         :induct t
         :in-theory (e/d (plexeme-token/space-p
                          plexeme-tokenp
                          plexeme-token/newline-p)
                         (plexeme-token/newline-p-of-read-token/newline)))
        '(:use plexeme-token/newline-p-of-read-token/newline)))

     (defret read-macro-function-replist-loop-subsetp-when-ellipsis
       (subsetp-equal hash-params
                      (cons (ident "__VA_ARGS__") params))
       :hyp (and ellipsis
                 (ident-listp params))
       :hints (("Goal" :induct t :in-theory (disable (:e ident)))))

     (defret read-macro-function-replist-loop-subsetp-when-not-ellipsis
       (subsetp-equal hash-params params)
       :hyp (and (not ellipsis)
                 (ident-listp params))
       :hints (("Goal" :induct t)))))

  ///

  (defret plexeme-list-token/space-p-of-read-macro-function-replist
    (plexeme-list-token/space-p replist))

  (defret read-macro-replist-subsetp-when-ellipsis
    (subsetp-equal hash-params
                   (cons (ident "__VA_ARGS__") params))
    :hyp (and ellipsis
              (ident-listp params))
    :hints (("Goal" :in-theory (disable (:e ident)))))

  (defret read-macro-replist-subsetp-when-not-ellipsis
    (subsetp-equal hash-params params)
    :hyp (and (not ellipsis)
              (ident-listp params))
    :hints (("Goal" :in-theory (disable (:e ident))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pproc-define ((ppstate ppstatep))
  :returns (mv erp (new-ppstate ppstatep))
  :short "Preprocess a @('#define') directive."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called just after the @('define') identifier has been parsed.
     We do not pass the comments and white space before and after the @('#'),
     because we make no use of them, at lest for now.")
   (xdoc::p
    "We read an identifier, which is the name of the macro.
     This name must not be the @('defined') identifier [C17:6.10.8/2].
     This name must be also distinct from
     the names of the predefined macros [C17:6.10/8];
     Clang warns about but allows defining predefined macros,
     so we may need to optionally relax this restriction at some point.")
   (xdoc::p
    "After the name, we read the next lexeme,
     via @(tsee read-lexeme) instead of the usual @(tsee read-token/newline),
     because white space and comments matter here:
     white space is required between the name and replacement list
     of an object like macro definition [C17:6.10.3/3];
     and white space is prohibited between the name and left parenthesis
     of a function-like macro definition,
     according to the grammar rule for <i>lparen</i> in [C17:6.10/1].
     [C17:5.1.1.2/1] in phase 3
     (which precedes preprocessing, i.e. phase 4)
     requires comments to be replaced by spaces.
     Although we do not do that to preserve comments, we must act as if we did:
     thus, for the purpose of enforcing
     these white-space-related restrictions in macro definitions,
     we need to treat comments the same as white space.
     Although [C17:6.10.3/5] only allows space and horizontal tab in directives,
     [C17:5.1.1.2/1] in phase 3 allows
     vertical tabs and form feeds to be replaced with spaces;
     so we allow vertical tabs and form feeds as white space here too.")
   (xdoc::p
    "If the next lexeme is a new line,
     we have an object-like macro definition with an empty replacement list.
     [C17:6.10.3/3] requires white space
     between the name and the replacement list,
     without making an exception for an empty replacement list.
     However, Clang readily accepts it (although it could be a Clang extension),
     and the example in [C17:6.10/8] about @('EMPTY') suggests
     that it is legal according to the standard.
     [C17:6.10.3/3] could be interpreted with
     the addition of something like ``unless the replacement list is empty''.
     We try to add the macro definition to the macro table.")
   (xdoc::p
    "If the next lexeme is a comment or (non-new-line) white space,
     we have an object-like macro definition.
     We use a separate function to obtain the replacement list;
     that function consumes the final new line.
     We try to add the macro definition to the macro table.")
   (xdoc::p
    "If the next lexeme is a left parenthesis,
     we have a function-like macro definition.
     We use a separate functions to obtain the parameters;
     that function consumed the right parenthesis.
     We use a separate function to obtain the replacement list;
     that function consumes the final new line.
     We try to add the macro definition to the macro table.")
   (xdoc::p
    "If the next lexeme is absent, or anything else than the above,
     the macro definition is syntactically incorrect."))
  (b* ((ppstate (ppstate-fix ppstate)) ; # define
       ((reterr) ppstate)
       ((erp & name name-span ppstate) (read-token/newline ppstate))
       ((unless (and name (plexeme-case name :ident))) ; # define name
        (reterr-msg :where (position-to-msg (span->start name-span))
                    :expected "an identifier"
                    :found (plexeme-to-msg name)))
       (name (plexeme-ident->ident name))
       ((when (equal name (ident "defined")))
        (reterr (msg "Cannot define macro with name 'defined'.")))
       ((when (assoc-equal name
                           (macro-table->predefined (ppstate->macros ppstate))))
        (reterr (msg "Cannot define macro with predefined name '~s0'."
                     (ident->unwrap name))))
       ((erp lexeme lexeme-span ppstate) (read-lexeme nil ppstate)))
    (cond
     ((and lexeme
           (plexeme-case lexeme :newline)) ; # define name EOL
      (b* ((macros (ppstate->macros ppstate))
           (info (make-macro-info-object :replist nil))
           ((erp new-macros) (macro-add name info macros))
           (ppstate (update-ppstate->macros new-macros ppstate)))
        (retok ppstate)))
     ((and lexeme
           (not (plexeme-token/newline-p lexeme))) ; # define name WSC
      (b* (((erp replist ppstate) ; # define name WSC REPLIST
            (read-macro-object-replist name ppstate))
           (macros (ppstate->macros ppstate))
           (info (make-macro-info-object :replist replist))
           ((erp new-macros) (macro-add name info macros))
           (ppstate (update-ppstate->macros new-macros ppstate)))
        (retok ppstate)))
     ((and lexeme
           (plexeme-equiv lexeme (plexeme-punctuator "("))) ; # define (
      (b* (((erp params ellipsis ppstate) ; # define ( params )
            (read-macro-params ppstate))
           ((erp replist hash-params ppstate) ; # define ( params ) replist
            (read-macro-function-replist name params ellipsis ppstate))
           (macros (ppstate->macros ppstate))
           (info (make-macro-info-function :params params
                                           :ellipsis ellipsis
                                           :replist replist
                                           :hash-params hash-params))
           ((erp new-macros) (macro-add name info macros))
           (ppstate (update-ppstate->macros new-macros ppstate)))
        (retok ppstate)))
     (t ; # define EOF/other
      (reterr-msg :where (position-to-msg (span->start lexeme-span))
                  :expected "a left parenthesis or ~
                             a comment or ~
                             a new line or ~
                             other white space"
                  :found (plexeme-to-msg lexeme)))))
  :no-function nil
  :guard-simplify :limited ; to stop (:E IDENT)
  :guard-hints (("Goal" :in-theory (e/d (alistp-when-macro-scopep-rewrite)
                                        ((:e ident))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pproc-undef ((ppstate ppstatep))
  :returns (mv erp (new-ppstate ppstatep))
  :short "Preprocess a @('#undef') directive."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called just after the @('define') identifier has been parsed.
     We do not pass the comments and white space before and after the @('#'),
     because we make no use of them, at lest for now.")
   (xdoc::p
    "We read an identifier, which is the name of the macro.
     The name must not be the @('defined') identifier [C17:6.10.8/2].
     We also ensure that we find a new line after the name,
     possibly with some white space and comments in between.")
   (xdoc::p
    "We remove the macro from the table.
     Note that @(tsee macro-remove) takes care of
     ensuring that the macro is not a predefined one."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) ppstate)
       ((erp & name? name?-span ppstate) (read-token/newline ppstate))
       ((unless (and name?
                     (plexeme-case name? :ident))) ; # undef name
        (reterr-msg :where (position-to-msg (span->start name?-span))
                    :expected "an identifier"
                    :found (plexeme-to-msg name?)))
       (name (plexeme-ident->ident name?))
       ((when (equal name (ident "defined")))
        (reterr (msg "Cannot undefine macro with name 'defined'.")))
       ((erp & newline? newline?-span ppstate) (read-token/newline ppstate))
       ((unless (and newline?
                     (plexeme-case newline? :newline))) ; # undef name EOL
        (reterr-msg :where (position-to-msg (span->start newline?-span))
                    :expected "a new line"
                    :found (plexeme-to-msg newline?)))
       (macros (ppstate->macros ppstate))
       ((erp new-macros) (macro-remove name macros))
       (ppstate (update-ppstate->macros new-macros ppstate)))
    (retok ppstate))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist ident-plexeme-list-alist
  :short "Fixtype of alists from identifiers to lists of preprocessing lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used to model the mapping of macro parameters
     to the corresponding macro arguments."))
  :key-type ident
  :val-type plexeme-list
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t
  :pred ident-plexeme-list-alistp
  :prepwork ((set-induction-depth-limit 1))

  ///

  (defruled plexeme-listp-of-cdr-of-assoc-equal-when-ident-plexeme-list-alistp
    (implies (and (ident-plexeme-list-alistp alist)
                  (assoc-equal key alist))
             (plexeme-listp (cdr (assoc-equal key alist))))
    :induct t
    :enable assoc-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define replist-next-token ((replist plexeme-listp))
  :guard (and (plexeme-list-token/space-p replist)
              (consp replist))
  :returns (mv (spacep booleanp) (token plexemep) (replist-rest plexeme-listp))
  :short "Obtain the next token from a replacement list,
          indicating whether it was preceded by space or not."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the next lexeme in the replacement list is a token, we return it,
     indicating that it has no preceding space.
     Otherwise, the lexeme must be a space (because of the guard),
     and so there must be another lexeme, which must be a token,
     and we return it, indicating that it was preceded by a space.")
   (xdoc::p
    "We also return the rest of the replacement list."))
  (b* (((cons lexeme replist) replist)
       ((when (plexeme-tokenp lexeme))
        (mv nil (plexeme-fix lexeme) (plexeme-list-fix replist)))
       ((when (endp replist))
        (raise "Internal error: replacement list ends with space.")
        (mv nil (irr-plexeme) nil))
       ((cons token replist) replist)
       ((unless (plexeme-tokenp token))
        (raise "Internal error: replacement list has two consecutive spaces.")
        (mv nil (irr-plexeme) nil)))
    (mv t (plexeme-fix token) (plexeme-list-fix replist)))
  :no-function nil
  :prepwork ((local (in-theory (enable cdr-of-plexeme-list-fix))))

  ///

  (defret plexeme-tokenp-of-replist-next-token
    (plexeme-tokenp token)
    :hints (("Goal" :in-theory (enable irr-plexeme))))

  (defret plexeme-list-token/space-p-of-replist-next-token
    (plexeme-list-token/space-p replist-rest)
    :hyp (plexeme-list-token/space-p replist))

  (defret len-of-replist-next-token-decreases
    (< (len replist-rest)
       (len replist))
    :hyp (consp replist)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-lexemes ((lexemes plexeme-listp))
  :returns (stringlit stringlitp)
  :short "Stringize a list of lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This implements the semantics of the @('#') operator [C17:6.10.3.2/2].
     The term `stringize' and `destringize' occur in [C17]."))
  (declare (ignore lexemes))
  (irr-stringlit)) ; TODO

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define join-tokens ((token1 plexemep) (token2 plexemep))
  :guard (and (plexeme-tokenp token1)
              (plexeme-tokenp token2))
  :returns (token plexemep)
  :short "Join two tokens into one."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to implement the @('##') operator [C17:6.10.3.3]."))
  (declare (ignore token1 token2))
  (irr-plexeme) ; TODO
  :prepwork ((local (in-theory (enable irr-plexeme))))

  ///

  (defret plexeme-tokenp-of-join-tokens
    (plexeme-tokenp token)
    :hyp (and (plexeme-tokenp token1)
              (plexeme-tokenp token2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define join-optional-tokens ((token1? plexeme-optionp)
                              (token2? plexeme-optionp))
  :guard (and (or (not token1?) (plexeme-tokenp token1?))
              (or (not token2?) (plexeme-tokenp token2?)))
  :returns (token? plexeme-optionp)
  ;; TODO
  (if (or token1? token2?)
      (irr-plexeme)
    nil)
  :prepwork ((local (in-theory (enable irr-plexeme))))

  ///

  (defret plexeme-tokenp-of-join-optional-tokens
    (implies token?
             (plexeme-tokenp token?))
    :hyp (and (implies token1? (plexeme-tokenp token1?))
              (implies token2? (plexeme-tokenp token2?))))

  (defret join-optional-tokens-iff-first-or-second
    (iff token? (or token1? token2?))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-first-token ((lexemes plexeme-listp))
  :returns (mv (nontokens plexeme-listp)
               (token? plexeme-optionp)
               (lexemes-rest plexeme-listp))
  :short "Find the first token in a list of lexemes, if any."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is no token, we return @('nil').
     We also return the non-tokens that precede the token;
     if there is no token, these are all the lexemes passed as input.
     We also return the remaining lexemes."))
  (b* (((when (endp lexemes)) (mv nil nil nil))
       (lexeme (plexeme-fix (car lexemes)))
       ((when (plexeme-tokenp lexeme))
        (mv nil lexeme (plexeme-list-fix (cdr lexemes))))
       ((mv nontokens token? lexemes-rest) (find-first-token (cdr lexemes))))
    (mv (cons lexeme nontokens) token? lexemes-rest))

  ///

  (defret plexeme-tokenp-of-find-first-token
    (implies token?
             (plexeme-tokenp token?))
    :hints (("Goal" :induct t)))

  (defret plexeme-list-not-tokenp-of-find-first-token
    (plexeme-list-not-tokenp nontokens)
    :hints (("Goal" :induct t)))

  (defret len-of-find-first-token
    (implies token?
             (< (len lexemes-rest)
                (len lexemes)))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define normalize-macro-arg ((arg plexeme-listp))
  :returns (norm-arg plexeme-listp)
  :short "Normalize a macro argument,
          turning comments and white space (including new lines)
          into single spaces between tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "When we calculate the arguments of a macro call,
     each argument is a list of zero or more lexemes;
     the calculation involves macro expansion within the arguments themselves,
     unless the corresponding parameters in the macro's replacement list
     are preceded by @('#') or @('##') or followed by @('##')
     [C17:6.10.3.1/1].
     Each calculated argument needs to replace the correspoding parameter
     in the replacement list in order to realize the macro call
     [C17:6.10.3/10].
     The list of lexemes that forms an argument
     could include comments and white space,
     including new lines [C17:6.10.3/10].
     Since we generally try to preserve comments and white space,
     there might be reasons to preserve comments and white space
     in the arguments passed to a macro;
     but for now, to keep things simple,
     we normalize all those comments and white space
     to single spaces between tokens.
     That is, given the list of lexemes that forms an argument,
     we remove all the white space and comments at the start and end,
     and we join all the contiguous white space and comments
     into single spaces.
     Note that the evaluation of @('#') [C17:6.10.3.2/2]
     requires to normalize comments and white space that separated token
     to single spaces,
     so our normalization is consistent with that.")
   (xdoc::p
    "The resulting of lexemes is a sequence of tokens
     with single spaces between some of the tokens.
     This happens to be the same form in which
     we store replacement lists in the macro table
     (see @(tsee macro-info)),
     but there is no need for them to have the same form.")
   (xdoc::p
    "This function performs this normalization.
     The result satisfies @(tsee plexeme-list-token/space-p),
     which captures some but not all of the constraints on the list."))
  (normalize-macro-arg-loop t arg)

  :prepwork
  ((define normalize-macro-arg-loop ((startp booleanp) (arg plexeme-listp))
     :returns (norm-arg plexeme-listp)
     :parents nil
     (b* (((mv nontokens token arg-rest) (find-first-token arg))
          ((when (not token)) nil)
          (norm-arg-rest (normalize-macro-arg-loop nil arg-rest)))
       (append (if (or startp
                       (not nontokens))
                   nil
                 (list (plexeme-spaces 1)))
               (cons token
                     norm-arg-rest)))
     :measure (len arg)
     :verify-guards :after-returns

     ///

     (defret plexeme-list-token/space-p-of-normalize-macro-arg-loop
       (plexeme-list-token/space-p norm-arg)
       :hints (("Goal"
                :induct t
                :in-theory (enable plexeme-list-token/space-p
                                   plexeme-token/space-p))))))

  ///

  (defret plexeme-list-token/space-p-of-normalize-macro-arg
    (plexeme-list-token/space-p norm-arg)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define replace-macro-args ((replist plexeme-listp)
                            (subst ident-plexeme-list-alistp))
  :guard (plexeme-list-token/space-p replist)
  :returns (replaced-replist plexeme-listp)
  :short "In the replacement list of a function-like macro,
          replace all the parameters with the corresponding arguments,
          and evaluate the @('#') and @('##') operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "The alist @('subst') is calculated elsewhere.
     It consists of the parameter names as keys,
     including @('__VA_ARGS__') if the macro has ellipsis,
     and the corresponding list of lexemes as values.
     The list of lexemes associated to each parameter
     is generally fully replaced [C17:6.10.3.1],
     unless it is preceded by @('#') or @('##') or followed by @('##'),
     in which case the argument lexemes are not replaced.
     Either way, the alist has the appropriate lists of lexemes here.
     Those are already normalized via @(tsee normalize-macro-arg).")
   (xdoc::p
    "We go through the replacement list.
     When we encounter a parameter of the macro,
     we replace it with the corresponding argument in @('subst')
     [C17:6.10.3.1].
     When we encounter @('#'),
     which must be followed by a parameter,
     we stringize the argument corresponding to the parameter
     [C17:6.10.3.2].
     When we encounter @('##'),
     which must be followed and preceded by a token,
     we combine those tokens into one [C17:6.10.3.3].")
   (xdoc::p
    "For @('##'), while the token that follows
     is accessible in the rest of @('replist'),
     the preceding token is tracked via
     the @('last-token/placemarker') parameter of the loop function.
     But instead of a token, this may indicate a placemarker [C17:6.10.3.3],
     which we model as @('nil').
     We also @('nil') at the beginning of the replacement list,
     in this case to indicate no token or placemarker;
     since @('##') cannot start the replacement list,
     there is no ambiguity in the use of @('nil') for these two purposes.")
   (xdoc::p
    "When we encounter a token in @('replist'),
     it could be followed by @('##') or not.
     If there is a @('##'),
     the recursive call of the loop function,
     which is passed the token as @('last-token/placemarker'),
     joins that token with the one after the @('##');
     thus, after calling the recursive loop function,
     we must not add the token to the output list.
     To handle this uniformly,
     we must always leave to the recursive call
     the responsibility of adding @('last-token/placemarker') if appropriate,
     namely if it is not followed by @('##').
     This makes the code a bit ore complicated.")
   (xdoc::p
    "Another complication arises from the treatment of
     parameters adjacent to @('##'),
     which are replaced with the tokens of the corresponding arguments,
     which may be zero or more.
     If zero, they are treated like placemarkers.
     If non-zero, we need to take the last one (if before @('##'))
     or the first one (if after @('##')),
     as the operands of @('##').
     For argument tokens following @('##'),
     @('last-token/placemarker') becomes its last token,
     unless the argument is a singleton list,
     in which case @('last-token/placemarker') is the combined token.")
   (xdoc::p
    "Note that only the @('##') operators that occur in @('replist'),
     and not any coming from the arguments in @('subst'),
     are evaluated [C17:6.10.3.3/3]."))
  (replace-macro-args-loop nil
                           (plexeme-list-fix replist)
                           (ident-plexeme-list-alist-fix subst))

  :prepwork
  ((define replace-macro-args-loop ((last-token/placemarker plexeme-optionp)
                                    (replist plexeme-listp)
                                    (subst ident-plexeme-list-alistp))
     :guard (and (plexeme-list-token/space-p replist)
                 (or (not last-token/placemarker)
                     (plexeme-tokenp last-token/placemarker)))
     :returns (replaced-replist plexeme-listp)
     :parents nil
     (b* ((last-token/placemarker (plexeme-option-fix last-token/placemarker))
          ((when (endp replist))
           ;; If we reach the end of REPLIST and we have a previous token,
           ;; we must add it to the output, because the caller does not.
           (and last-token/placemarker
                (list (plexeme-fix last-token/placemarker))))
          ((mv spacep token replist) (replist-next-token replist)))
       (cond
        ((plexeme-hashp token) ; #
         (b* (;; REPLIST cannot end with #.
              ((unless (consp replist))
               (raise "Internal error: replacement list ends with #."))
              ((mv & param replist) (replist-next-token replist))
              ;; The following token must be a parameter.
              ((unless (plexeme-case param :ident)) ; # param
               (raise "Internal error: # is followed by non-identifier ~x0."
                      param))
              (param (plexeme-ident->ident param))
              (param+arg (assoc-equal param
                                      (ident-plexeme-list-alist-fix subst)))
              ((unless param+arg)
               (raise "Internal error: # is followed by a non-parameter ~x0."
                      param))
              (arg (cdr param+arg))
              ;; Combine # and ARG into TOKEN.
              (stringlit (stringize-lexemes arg))
              (token (plexeme-string stringlit)))
           ;; Do not add TOKEN to the output here,
           ;; because it might be followed by ##;
           ;; let the recursive call handle TOKEN.
           ;; But add LAST-TOKEN/PLACEMARKER if non NIL,
           ;; because it is not followed by ##.
           (append (and last-token/placemarker
                        (list (plexeme-fix last-token/placemarker)))
                   (and spacep (list (plexeme-spaces 1)))
                   (replace-macro-args-loop token replist subst))))
        ((plexeme-hashhashp token) ; ##
         (b* (;; REPLIST cannot end with ##.
              ((unless (consp replist))
               (raise "Internal error: replacement list ends with ##."))
              ((mv & token2 replist) (replist-next-token replist)))
           (if (and (plexeme-case token2 :ident) ; ## param
                    (assoc-equal (plexeme-ident->ident token2)
                                 (ident-plexeme-list-alist-fix subst)))
               ;; If the token after ## is a parameter,
               ;; consider its corresponding argument ARG from SUBST.
               (b* ((arg
                     (cdr (assoc-equal (plexeme-ident->ident token2)
                                       (ident-plexeme-list-alist-fix subst))))
                    ;; The right operand of ## is
                    ;; a placemarker if ARG is empty,
                    ;; otherwise it is its first token.
                    ((mv next-token/placemarker rest-arg)
                     (if (consp arg)
                         (mv (car arg) (cdr arg))
                       (mv nil nil)))
                    ((unless (or (not next-token/placemarker)
                                 (plexeme-tokenp next-token/placemarker)))
                     (raise "Internal error: ~x0 is not token."
                            next-token/placemarker))
                    ;; The left operand of ## is always
                    ;; the LAST-TOKEN/PLACEMARKER value,
                    ;; either NIL (placemarker) or a token.
                    (token? (join-optional-tokens last-token/placemarker
                                                  next-token/placemarker))
                    ;; The LAST-TOKEN/PLACEMARKER to pass to the recursive call
                    ;; is calculated as follows.
                    ;; If both the left and right operands of ##
                    ;; are placemarkers (NIL),
                    ;; the result TOKEN? of ## is a placemarker,
                    ;; and that is the new LAST-TOKEN/PLACEMARKER.
                    ;; If the left operand of ## is a token
                    ;; and the right one is a placemarker,
                    ;; the result TOKEN? is the left operand,
                    ;; and since ARG (and REST-ARG) is empty,
                    ;; LAST-TOKEN/PLACEMARKER is the left operand.
                    ;; If the left operand is a placemarker
                    ;; and the right operand is a token (the first of ARG),
                    ;; the result is that token;
                    ;; if ARG only consists of that token,
                    ;; the token also becomes LAST-TOKEN/PLACEMARKER,
                    ;; otherwise we take the last token of REST-ARG.
                    ;; If both left and right operands are tokens,
                    ;; TOKEN? is their combination,
                    ;; and LAST-TOKEN/PLACEMARKER is as in the previous case.
                    (last-token/placemarker
                     (if token?
                         (if (consp rest-arg)
                             (car (last rest-arg))
                           token?)
                       nil))
                    ((unless (or (not last-token/placemarker)
                                 (plexeme-tokenp last-token/placemarker)))
                     (raise "Internal error: ~x0 is not a token."
                            last-token/placemarker)))
                 ;; The recursive call takes care of LAST-TOKEN/PLACEMARKER,
                 ;; but if ARG has two or more tokens
                 ;; (which is the case exactly when REST-ARG is not NIL),
                 ;; here we need to add to the output
                 ;; all but the last token of ARG.
                 (append (and spacep (list (plexeme-spaces 1)))
                         (and (consp rest-arg) (butlast arg 1))
                         (replace-macro-args-loop last-token/placemarker
                                                  replist
                                                  subst)))
             ;; If the token after ## is not a parameter,
             ;; we combine it with LAST-TOKEN/PLACEMARKER,
             ;; which always gives us a token because TOKEN2 is a token,
             ;; and that resulting token is passed to the recursive call.
             (b* ((token (join-optional-tokens last-token/placemarker token2)))
               (append (and spacep (list (plexeme-spaces 1)))
                       (replace-macro-args-loop token replist subst))))))
        ((plexeme-case token :ident) ; ident (param or not)
         (b* ((ident (plexeme-ident->ident token))
              (ident+arg (assoc-equal ident
                                      (ident-plexeme-list-alist-fix subst)))
              ((when (not ident+arg))
               ;; If the token is an identifier but not a parameter,
               ;; it becomes the next LAST-TOKEN/PLACEMARKER.
               ;; We add the previous LAST-TOKEN/PLACEMARKER if not NIL,
               ;; because it is not followed by ##.
               (append (and last-token/placemarker
                            (list (plexeme-fix last-token/placemarker)))
                       (and spacep (list (plexeme-spaces 1)))
                       (replace-macro-args-loop token replist subst)))
              ;; If the token is a parameter,
              ;; consider its correspoding argument ARG.
              ;; If it is NIL, it is a placemarker passed to the recursive call.
              ;; Otherwise, we pass its last token as LAST-TOKEN/PLACEMARKER
              ;; to the recursive call.
              ;; But the previous LAST-TOKEN/PLACEMARKER, if not NIL,
              ;; must be added to the output,
              ;; because it is not followed by ##.
              (arg (cdr ident+arg))
              ((mv arg-but-last arg-last)
               (if (consp arg)
                   (mv (butlast arg 1) (car (last arg)))
                 (mv nil nil)))
              ((unless (or (not arg-last)
                           (plexeme-tokenp arg-last)))
               (raise "Internal error: ~x0 is not a token." arg-last)))
           (append (and last-token/placemarker
                        (list (plexeme-fix last-token/placemarker)))
                   (and spacep (list (plexeme-spaces 1)))
                   arg-but-last
                   (replace-macro-args-loop arg-last replist subst))))
        (t ; other token
         ;; This case is the same as that above
         ;; of an identifier that is not a parameter.
         (append (and last-token/placemarker
                      (list (plexeme-fix last-token/placemarker)))
                 (and spacep (list (plexeme-spaces 1)))
                 (replace-macro-args-loop token replist subst)))))
     :no-function nil
     :measure (len replist)
     :guard-hints
     (("Goal" :in-theory (enable
                          alistp-when-ident-plexeme-list-alistp-rewrite
                          plexeme-tokenp
                          true-listp-when-plexeme-listp
                          listp)))
     :prepwork ((local (in-theory (disable acl2::member-of-cons))))
     :hooks nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pproc-lexemes/macroargs
  :short "Preprocess lexemes and macro arguments, expanding macros."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the preprocessing that applies to
     most of the lexemes in the files being preprocessed.")
   (xdoc::p
    "The main function is @(tsee pproc-lexemes),
     which goes through the lexemes applying macro replacement,
     returning the resulting lexemes.
     The companion recursive function is used to preprocess the lexemes
     that form arguments of function-like macros.
     This companion function performs a recursion over the macro parameters,
     but since arguments need to be preprocessed as well,
     and may contain further macro calls,
     the recursion is mutual.")
   (xdoc::p
    "Both functions take a list of identifiers
     that consists of the names of the macros that are ``disabled'',
     in the sense that they must not be expanded.
     The order in the list is unimportant, but the repetitions are:
     the list represents a multiset of macro names.
     Every time we encounter a @(':start') marker (see @(tsee macrep-mode)),
     we add the macro name to the multiset;
     every time we encounter a @(':end') marker (see @(tsee macrep-mode)),
     we remove the macro name from the multiset.
     Each expansion of the macro is surrounded by
     a @(':start') and @(':end') marker for that macro name:
     this way, when the expansion is added in front of the input,
     the macro will not be re-expanded until we go past its expansion
     [C17:6.10.3.4].
     The reason why we need a multiset is that, for instance,
     the argument of a function-like macro @('F')
     could contain a call of @('F') itself.
     The argument is macro-expanded before the (outer) call is expanded,
     which therefore involves expanding the inner call.
     The expansion of the inner call is surrounded by the markers.
     Then, when we expand the outer call,
     that expansion is also surrounded by the markers.
     This gives rise to nested markers for the same macro,
     but reaching an inner closing marker should not re-enable the expansion,
     which is re-enabled only after the outer closing marker.
     Thus, we need to keep track of how many disablements and re-enablements
     each macro goes through, i.e. we need a multiset.
     Only if the multiset contains no occurrences at all of a macro,
     that macro is enabled, otherwise it stays disabled.")
   (xdoc::p
    "Both functions take a flag saying whether
     we are preprocessing a directive [C17:6.10/2] or not.
     This affects the treatment of new lines within macro arguments.")
   (xdoc::p
    "As in @(tsee pproc-files/groups/etc),
     we use an artificial limit to ensure termination.
     There should be a termination argument,
     but it is a bit more complicated than
     decreasing the size of the preprocessing state,
     because when macros get expanded,
     their replacement lists are added in front of the input lexemes,
     making the input larger.
     The termination argument should rely on the fact that
     macros are not recursively expanded,
     and thus, when a macro is expanded,
     it can contribute to decreasing a suitable measure."))

  (define pproc-lexemes ((mode macrep-modep)
                         (rev-lexemes plexeme-listp)
                         (paren-level natp)
                         (no-expandp booleanp)
                         (disabled ident-listp)
                         (directivep booleanp)
                         (ppstate ppstatep)
                         (limit natp))
    :returns (mv erp
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep))
    :parents (preprocessor pproc-lexemes/macroargs)
    :short "Preprocess lexemes."
    :long
    (xdoc::topstring
     (xdoc::p
      "As explained in @(tsee macrep-mode),
       there are different macro replacement modes in different situations.
       This function takes the mode as an input.")
     (xdoc::p
      "This function takes and returns the lexemes generated so far,
       in reverse order for efficiency.")
     (xdoc::p
      "This function takes a parenthesis level (@('paren-level')),
       which indicates the nexting of parentheses.
       Initially 0,
       it is incremented by a left parenthesis
       and decremented by a right parenthesis.
       This is used to skip commas and right parenthesis
       within inner parentheses [C17:6.10.3/10] [C17:6.10.3/11]:
       only when the parenthesis level is 0,
       a comma or right parenthesis counts as ending macro arguments.
       This parenthesis level is only used in the @(':arg-...') modes;
       it is always 0 in the @(':line') and @(':expr') modes.")
     (xdoc::p
      "The @('no-expandp') flag is @('t') exactly when
       the mode is among @(':arg-nonlast'), @(':arg-last'), and @(':arg-dots')
       and the macro parameter corresponding to the argument being preprocessed
       is preceded by @('#') or @('##') or followed by @('##').
       The flag inhibits macro expansion [C17:6.10.3.1/1].")
     (xdoc::p
      "This function starting by reading the next lexmark,
       and then it dispatches based on it.")
     (xdoc::p
      "If there is no next lexmark, it is an error.
       In every mode, the stopping criterion is never end of file;
       see @(tsee macrep-mode).")
     (xdoc::p
      "If the next lexmark is a @(':start') marker,
       we add the macro name to the multiset,
       and continue preprocessing.
       If the next lexmark is a @(':end') marker,
       we remove the macro name (once) from the multiset
       and continue preprocessing.
       That multiset is discusssed in @(tsee pproc-lexemes/macroargs).")
     (xdoc::p
      "If tne next lexmark is a new line,
       it is always added to the reversed lexemes.
       In the @(':line') and @(':expr') modes,
       the new line is the stopping criterion,
       so we end the recursive preprocessing of lexemes.
       In the other modes, which are all for macro arguments,
       new line is treated like other white space [C17:6.10.3/10],
       so we continue the recursive preprocessing of lexemes,
       unless we are in a directive:
       in the latter case, the new line ends with directive [C17:6.10/2],
       but if we are in the middle of a macro argument,
       it means that we have an error.")
     (xdoc::p
      "If the next lexmark is a comma,
       it is the stopping criterion for the @(':arg-nonlast') mode,
       but only if the parenthesis level is 0;
       in this case, we do not add the comma to the reversed lexemes,
       because those are meant to contain the argument we are preprocessing,
       and the comma is not part of the argument.
       However, if the mode is @(':arg-last') and the parenthesis level is 0,
       it means that a comma was found where a right parenthesis was needed,
       because there must be no other macro arguments;
       so we return an error in this case.
       In all other cases, the comma is treated like a normal lexeme,
       i.e. it is added to the reversed list and preprocessing continues:
       this is clearly the case for the @(':line') and @(':expr') modes;
       it is also the case for the @(':arg-dots') mode,
       where commas separating multiple arguments
       that correspond to the ellipsis parameter
       are considered all together and associated to @('__VA_ARGS__')
       [C17:6.10.3/12];
       and it is also the case for the @(':arg-nonlast') and @(':arg-last') modes
       when the parenthesis level is not 0.")
     (xdoc::p
      "If the next lexmark is an open parenthesis,
       we add it to the list of reversed lexemes and we continue preprocessing.
       We increment the parenthesis level if we are in an @(':arg-...') mode.")
     (xdoc::p
      "If the next lexmark is a closed parenthesis,
       it is the stopping criterion for
       the @(':arg-last') and @(':arg-dots') modes,
       but only if the parenthesis level is 0;
       in this case, we do not add the parenthesis to the reversed lexemes,
       because those are meant to contain the argument we are preprocessing,
       and the parenthesis is not part of the argument.
       If the parenthesis level is not 0,
       we just decrement the level and continue.
       In the @(':arg-nonlast') mode, if the parenthesis level is 0,
       it it an error, because the macro call is ending prematurely:
       we are expecting a comma to end the current argument.
       If the parenthesis level is not 0 in the @(':arg-nonlast') mode,
       we just decrement the level and continue.
       In the @(':line') and @(':expr') modes,
       a closed parenthesis has no special significance.")
     (xdoc::p
      "If the next lexmark is an identifier, there are several cases.
       If we are in the @(':expr') mode and the identifier is @('defined'),
       it is the operator described in [C17:6.10.1/1],
       which must be followed by another identifier, possibly parenthesized.
       If the macro is found in the macro table,
       we add the lexeme @('1') to the reversed lexemes;
       otherwise, we add the lexeme @('0') to the reversed lexemes.
       That is, we evaluate the operator.
       And we continue preprocessing.")
     (xdoc::p
      "If the next lexmark is an identifier different from @('defined'),
       or if we are not in the @(':expr') mode,
       then we look up the identifier in the macro table,
       unless it is in the disabled multiset,
       and unless macro expansion is inhibited.
       If it is not found in the macro table,
       it is just added to the reversed lexemes,
       and we continue preprocessing.
       If it is found but neither in the innermost nor in the predefined scope,
       the file is not self-contained,
       and we return an exception to that effect.
       If we find an object-like macro,
       we leave the reversed lexemes unchanged,
       and push the replacement list of the macro onto the pending lexmarks,
       surrounded by markers to disable that macro;
       that is, we replace the macro with its expansion,
       and we continue preprocessing the replacement,
       realizing the rescanning and further replacement [C17:6.10.3.4].
       If we find a function-like macro,
       the next token after comments and non-new-line white space
       must be a left parenthesis.
       After that, we call the companion recursive function
       to obtain the arguments of the macro call,
       which are returned as the values of an alist
       that maps the macro parameters to the arguments;
       the companion function consumes the final right parenthesis.
       We call a separate function to replace the parameters with the arguments
       in the macro's replacement list,
       and then we add the resulting lexemes to the pending lexmarks,
       surrounded by the markers for the macro.")
     (xdoc::p
      "In all other cases, the lexeme is added to the reversed list,
       and we continue the recursive preprocessing."))
    (b* ((ppstate (ppstate-fix ppstate))
         ((reterr) nil ppstate)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         ((erp lexmark ppstate) (read-lexmark ppstate)))
      (cond
       ((not lexmark) ; EOF
        (reterr-msg :where (position-to-msg (ppstate->position ppstate))
                    :expected "a lexmark"
                    :found "end of file"))
       ((lexmark-case lexmark :start) ; start(M)
        (b* ((name (lexmark-start->macro lexmark))
             (disabled (cons name (ident-list-fix disabled))))
          (pproc-lexemes mode
                         rev-lexemes
                         paren-level
                         no-expandp
                         disabled
                         directivep
                         ppstate
                         (1- limit))))
       ((lexmark-case lexmark :end) ; end(M)
        (b* ((name (lexmark-end->macro lexmark))
             (disabled (remove1-equal name (ident-list-fix disabled))))
          (pproc-lexemes mode
                         rev-lexemes
                         paren-level
                         no-expandp
                         disabled
                         directivep
                         ppstate
                         (1- limit))))
       (t ; lexeme
        (b* ((lexeme (lexmark-lexeme->lexeme lexmark))
             (span (lexmark-lexeme->span lexmark)))
          (cond
           ((plexeme-case lexeme :newline) ; EOL
            (case (macrep-mode-kind mode)
              ((:line :expr)
               (retok (cons lexeme (plexeme-list-fix rev-lexemes)) ppstate))
              ((:arg-nonlast :arg-last :arg-dots)
               (if directivep
                   (reterr-msg :where (position-to-msg (span->start span))
                               :expected "the completion of a macro call"
                               :found "new line (which ends the directive)")
                 (pproc-lexemes mode
                                (cons lexeme rev-lexemes)
                                paren-level
                                no-expandp
                                disabled
                                directivep
                                ppstate
                                (1- limit))))
              (t (prog2$ (impossible) (reterr :impossible)))))
           ((plexeme-punctuatorp lexeme ",") ; ,
            (cond ((and (macrep-mode-case mode :arg-nonlast)
                        (zp paren-level))
                   (retok (plexeme-list-fix rev-lexemes) ppstate))
                  ((and (macrep-mode-case mode :arg-last)
                        (zp paren-level))
                   (reterr-msg :where (position-to-msg (span->start span))
                               :expected "a closed parenthesis"
                               :found "a comma"))
                  (t (pproc-lexemes mode
                                    (cons lexeme rev-lexemes)
                                    paren-level
                                    no-expandp
                                    disabled
                                    directivep
                                    ppstate
                                    (1- limit)))))
           ((plexeme-punctuatorp lexeme "(") ; (
            (pproc-lexemes mode
                           (cons lexeme rev-lexemes)
                           (if (member-eq (macrep-mode-kind mode)
                                          '(:arg-nonlast :arg-last :arg-dots))
                               (1+ (lnfix paren-level))
                             paren-level)
                           no-expandp
                           disabled
                           directivep
                           ppstate
                           (1- limit)))
           ((plexeme-punctuatorp lexeme ")") ; )
            (case (macrep-mode-kind mode)
              ((:line :expr)
               (pproc-lexemes mode
                              (cons lexeme rev-lexemes)
                              paren-level
                              no-expandp
                              disabled
                              directivep
                              ppstate
                              (1- limit)))
              (:arg-nonlast
               (if (zp paren-level)
                   (reterr-msg :where (position-to-msg (span->start span))
                               :expected "a comma"
                               :found "a closed parenthesis")
                 (pproc-lexemes mode
                                (cons lexeme rev-lexemes)
                                (1- paren-level)
                                no-expandp
                                disabled
                                directivep
                                ppstate
                                (1- limit))))
              ((:arg-last :arg-dots)
               (if (zp paren-level)
                   (retok (plexeme-list-fix rev-lexemes) ppstate)
                 (pproc-lexemes mode
                                (cons lexeme rev-lexemes)
                                (1- paren-level)
                                no-expandp
                                disabled
                                directivep
                                ppstate
                                (1- limit))))
              (t (prog2$ (impossible) (reterr :impossible)))))
           ((plexeme-case lexeme :ident) ; ident
            (b* ((ident (plexeme-ident->ident lexeme))
                 ((when (and (macrep-mode-case mode :expr)
                             (equal (ident->unwrap ident) "defined"))) ; defined
                  (b* (((erp macro-name disabled ppstate)
                        (b* (((reterr) (irr-ident) nil ppstate)
                             ((erp token span2 disabled ppstate)
                              (read-token-handling-markers directivep
                                                           disabled
                                                           ppstate)))
                          (cond
                           ((plexeme-case token :ident) ; defined ident
                            (b* ((macro-name (plexeme-ident->ident token)))
                              (retok macro-name disabled ppstate)))
                           ((plexeme-punctuatorp token "(") ; defined (
                            (b* (((erp token span3 disabled ppstate)
                                  (read-token-handling-markers directivep
                                                               disabled
                                                               ppstate))
                                 ((unless (plexeme-case token :ident))
                                  ;; defined ( ident
                                  (reterr-msg :where (position-to-msg
                                                      (span->start span3))
                                              :expected "an identifier"
                                              :found (plexeme-to-msg token)))
                                 (macro-name (plexeme-ident->ident token))
                                 ((erp token span4 disabled ppstate)
                                  (read-token-handling-markers directivep
                                                               disabled
                                                               ppstate))
                                 ((unless (plexeme-punctuatorp token ")"))
                                  ;; defined ( ident )
                                  (reterr-msg :where (position-to-msg
                                                      (span->start span4))
                                              :expected "a right parenthesis"
                                              :found (plexeme-to-msg token))))
                              (retok macro-name disabled ppstate)))
                           (t ; defined EOF-or-not-ident-and-not-(
                            (reterr-msg :where (position-to-msg
                                                (span->start span2))
                                        :expected "an identifier or ~
                                                   a left parenthesis"
                                        :found (plexeme-to-msg token))))))
                       ((mv info? & &)
                        (macro-lookup macro-name (ppstate->macros ppstate)))
                       (lexeme (if info?
                                   (plexeme-number (pnumber-digit #\1))
                                 (plexeme-number (pnumber-digit #\0)))))
                    (pproc-lexemes mode
                                   (cons lexeme rev-lexemes)
                                   paren-level
                                   no-expandp
                                   disabled
                                   directivep
                                   ppstate
                                   (1- limit))))
                 ((when (or no-expandp
                            (member-equal ident (ident-list-fix disabled))))
                  (pproc-lexemes mode
                                 (cons lexeme rev-lexemes)
                                 paren-level
                                 no-expandp
                                 disabled
                                 directivep
                                 ppstate
                                 (1- limit)))
                 ((mv info innermostp predefinedp)
                  (macro-lookup ident (ppstate->macros ppstate)))
                 ((unless info)
                  (pproc-lexemes mode
                                 (cons lexeme rev-lexemes)
                                 paren-level
                                 no-expandp
                                 disabled
                                 directivep
                                 ppstate
                                 (1- limit)))
                 ((when (and (not innermostp)
                             (not predefinedp)))
                  (reterr :not-self-contained))
                 ;; TODO: special treatment of some predefined macros
                 )
              (macro-info-case
               info
               :object
               (b* ((ppstate (push-lexmark (lexmark-end ident) ppstate))
                    (ppstate (push-lexemes info.replist ppstate))
                    (ppstate (push-lexmark (lexmark-start ident) ppstate)))
                 (pproc-lexemes mode
                                rev-lexemes
                                paren-level
                                no-expandp
                                disabled
                                directivep
                                ppstate
                                (1- limit)))
               :function
               (b* (((erp token span2 disabled ppstate)
                     (read-token-handling-markers directivep
                                                  disabled
                                                  ppstate))
                    ((unless (plexeme-punctuatorp token "(")) ; ident (
                     (reterr-msg :where (position-to-msg (span->start span2))
                                 :expected "an open parenthesis"
                                 :found (plexeme-to-msg token)))
                    ((erp subst disabled ppstate)
                     (b* (((reterr) nil nil ppstate))
                       (if (and (endp info.params)
                                (not info.ellipsis))
                           (b* (((erp token span2 disabled ppstate)
                                 (read-token-handling-markers directivep
                                                              disabled
                                                              ppstate))
                                ((unless (plexeme-punctuatorp token ")"))
                                 (reterr-msg :where (position-to-msg
                                                     (span->start span2))
                                             :expected "a closed parenthesis"
                                             :found (plexeme-to-msg token))))
                             (retok nil disabled ppstate))
                         (b* (((erp subst ppstate)
                               (pproc-macro-args info.params
                                                 info.ellipsis
                                                 info.hash-params
                                                 disabled
                                                 directivep
                                                 ppstate (1- limit))))
                           (retok subst disabled ppstate)))))
                    (replist (replace-macro-args info.replist subst))
                    (ppstate (push-lexmark (lexmark-end ident) ppstate))
                    (ppstate (push-lexemes replist ppstate))
                    (ppstate (push-lexmark (lexmark-start ident) ppstate)))
                 (pproc-lexemes mode
                                rev-lexemes
                                paren-level
                                no-expandp
                                disabled
                                directivep
                                ppstate
                                (1- limit))))))
           (t ; other lexeme
            (pproc-lexemes mode
                           (cons lexeme rev-lexemes)
                           paren-level
                           no-expandp
                           disabled
                           directivep
                           ppstate
                           (1- limit))))))))
    :no-function nil
    :measure (nfix limit))

  (define pproc-macro-args ((params ident-listp)
                            (ellipsis booleanp)
                            (hash-params ident-listp)
                            (disabled ident-listp)
                            (directivep booleanp)
                            (ppstate ppstatep)
                            (limit natp))
    :returns (mv erp
                 (subst ident-plexeme-list-alistp)
                 (new-ppstate ppstatep))
    :parents (preprocessor pproc-lexemes/macroargs)
    :short "Preprocess macro arguments."
    :long
    (xdoc::topstring
     (xdoc::p
      "This function takes as arguments
       the parameters whose corresponding arguments
       still need to be identified and preprocessed.
       Initially @('params') consists of all the parameters,
       and eventually it becomes @('nil').
       The boolean @('ellipsis') indicates
       whether the macro has an ellipsis parameter.")
     (xdoc::p
      "The @('hash-params') list comes from
       the homonymous component of @(tsee macro-info).
       It is used to decide which arguments are not macro-expanded.")
     (xdoc::p
      "The @(':arg-...') macro replacement mode is based on
       the remaining parameters and whether there is an ellipsis."))
    (b* ((ppstate (ppstate-fix ppstate))
         ((reterr) nil ppstate)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         ((when (endp params))
          (if ellipsis
              (b* ((va-args (ident "__VA_ARGS__"))
                   (mode (macrep-mode-arg-dots))
                   (no-expandp (and (member-equal va-args
                                                  (ident-list-fix hash-params))
                                    t))
                   ((erp rev-arg ppstate)
                    (pproc-lexemes mode
                                   nil ; rev-lexemes
                                   0 ; paren-level
                                   no-expandp
                                   nil ; disabled
                                   directivep
                                   ppstate
                                   (1- limit)))
                   (arg (rev rev-arg))
                   (arg (normalize-macro-arg arg))
                   (subst (acons va-args arg nil)))
                (retok subst ppstate))
            (retok nil ppstate)))
         (param (ident-fix (car params)))
         (mode (if (or (consp (cdr params))
                       ellipsis)
                   (macrep-mode-arg-nonlast)
                 (macrep-mode-arg-dots)))
         (no-expandp (and (member-equal param (ident-list-fix hash-params)) t))
         ((erp rev-arg ppstate)
          (pproc-lexemes mode
                         nil ; rev-lexemes
                         0 ; paren-level
                         no-expandp
                         nil ; disabled
                         directivep
                         ppstate
                         (1- limit)))
         (arg (rev rev-arg))
         (arg (normalize-macro-arg arg))
         ((erp subst ppstate)
          (pproc-macro-args (cdr params)
                            ellipsis
                            hash-params
                            disabled
                            directivep
                            ppstate
                            (1- limit))))
      (retok (acons param arg subst) ppstate))
    :no-function nil
    :measure (nfix limit))

  :prepwork ((local (in-theory (enable acons))))

  :verify-guards :after-returns

  :guard-hints
  (("Goal" :in-theory (enable true-listp-when-ident-listp
                              alistp-when-ident-plexeme-list-alistp-rewrite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pproc-files/groups/etc
  :short "Preprocess files, groups, and some related entities."
  :long
  (xdoc::topstring
   (xdoc::p
    "The top-level function of the clique is @(tsee pproc-file),
     which is called by @(tsee pproc-files) outside the clique.
     But it is also called when encoutering files to be included,
     which is why it is mutually recursive with the other functions.")
   (xdoc::p
    "The functions in the clique have certain common inputs and outputs:")
   (xdoc::ul
    (xdoc::li
     "All the functions take
      the path @('file') of the file being preprocessed,
      along with the base directory @('base-dir')
      and the inclusion directory @('include-dirs').
      The latter two come from @(tsee pproc-files) and never change.
      The @('file') path comes from the list @('files') in @(tsee pproc-files),
      as well as from the resolution of @('#include') directives.")
    (xdoc::li
     "All the functions take and return
      the alist @('preprocessed'), which contain (the results of)
      the (self-contained) files preprocessed so far.
      This starts empty and eventually contains all the preprocessed files.")
    (xdoc::li
     "All the functions take
      the list @('preprocessing') of the files being preprocessed.
      This is used to detect circularities.")
    (xdoc::li
     "All the functions except @(tsee pproc-file) take and return
      the list of lexemes generated so far by the preprocessing.
      These are in reverse order, to make extension efficient.
      The function @(tsee pproc-file) does not take a list of lexemes
      because it initiates the preprocessing of a file;
      instead of a list of lexemes, it returns a @(tsee scfile),
      which contains all the lexemes as well as the macros.")
    (xdoc::li
     "All the functions except @(tsee pproc-file) take and return
      a preprocessing state, for the file being preprocessed.
      The preprocessing state for the file is created, as a local stobj,
      by @(tsee pproc-file).")
    (xdoc::li
     "All the functions take and return the ACL2 state,
      needed to read files in the file system.")
    (xdoc::li
     "All the functions take an artificial limit to ensure termination.
      This is discussed below."))
   (xdoc::p
    "Other inputs and outputs specific to individual functions
     are discussed in the documentation of those functions.")
   (xdoc::p
    "In the absence of explicit checks, preprocessing may not terminate:
     @('file1.h') may include @('file2.h'), which may include @('file3.h'), etc.
     In practice, the file system is finite,
     but nontermination is the default, mathematically speaking.
     It should suffice to impose a limit on
     the number of files being recursively preprocessed,
     like the limit of 200 that
     the GCC preprocessor imposes an @('#include') nesting limit,
     according to "
    (xdoc::ahref "https://gcc.gnu.org/onlinedocs/cpp/Implementation-limits.html"
                 "Section 12.2 of the GNU C Preprocessor Manual")
    ". But fleshing out the termination argument takes a bit of extra work:
     we cannot just use a lexicographic measure consisting of
     the number of recursive files remaining
     followed by the size of the preprocessing state,
     because the latter increases
     when included files are not self-contained and must be expanded in place
     as well as when macros are expanded.
     There should still be a way in which things got suitably smaller.
     In particular, to handle the expansion in place of included file,
     we could probably make a lexicographic measure consisting of
     the number of recursive files remaining
     followed by the list of sizes of the byte lists
     in the array in the @('bytess') component of @(tsee ppstate),
     in the same order,
     so that adding a list of bytes to the array at index @('i+1')
     weighs less than having removed a non-zero number of bytes
     from the list in the array at index @('i'),
     namely the bytes that form the @('#include') directive.
     But we also need to consider the sizes of the unread lexemes,
     which may get larger when macros are expanded.
     Macro expansion is bounded in the C preprocessor,
     to prevent recursive expansion,
     so perhaps one could include, in the measure,
     some indication of which macros have been already expanded.
     All of this is not straightforward,
     and may require explicating invariants about the preprocessing state
     and perhaps other inputs of the functions in the clique.
     So for now we use a simpler approach,
     i.e. a limit on the number of recursive calls in the clique:
     each function first checks whether 0 is reached,
     and if not it calls other functions with the limit reduced by one;
     the limit is then just the measure.
     This is the same approach as in our dynamic semantics of C,
     but it is a necessity there,
     because there is no reason why the execution of C code should terminate.
     For the preprocessor, we should be able to do better,
     by just using a limit on the number of files recursively preprocessed,
     but we defer this to later, since it is not critical for now.")
   (xdoc::p
    "These functions use, like other code, use "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuples")
    " to handle errors arising in (broadly termed) input validation,
     e.g. illegal C code being preprocessed.
     These functions also use the error-value-tuple mechanism
     to signal when the file being preprocessed is not @(see self-contained):
     in that case, the function that detects that
     returns @(':not-self-contained') as the @('erp') output,
     which is eventually returned by @(tsee pproc-file)
     and caught by the caller of @(tsee pproc-file).
     It is indeed a sort of error, but a recoverable one,
     more like an exception in the sense that other languages have."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-file ((bytes byte-listp)
                      (file stringp)
                      (base-dir stringp)
                      (include-dirs string-listp)
                      (preprocessed string-scfile-alistp)
                      (preprocessing string-listp)
                      (macros macro-tablep)
                      (ienv ienvp)
                      state
                      (limit natp))
    :returns (mv erp
                 (scfile scfilep)
                 (new-preprocessed string-scfile-alistp)
                 state)
    :parents (preprocessor pproc-files/groups/etc)
    :short "Preprocess a file."
    :long
    (xdoc::topstring
     (xdoc::p
      "The bytes contained in the file are passed to this function.
       The file itself is read by the callers,
       namely @(tsee pproc-files) and @(tsee pproc-include).")
     (xdoc::p
      "If @('file') is found in the list of the files under preprocessing,
       we stop with an error, because there is a circularity.
       Otherwise, before preprocessing the file,
       we add it to the list of files under preprocessing.")
     (xdoc::p
      "If the file is in the @('preprocessed') alist,
       we avoid re-preprocessing it:
       we leave @('preprocessed') unchanged,
       and we return the @(tsee scfile) from the alist.")
     (xdoc::p
      "The macro table passed as input to this function
       is empty when this function is called by @(tsee pproc-files).
       Otherwise, it is the table for
       the file that contains the @('#include') directive
       that results in this call of @(tsee pproc-file).")
     (xdoc::p
      "We create a local preprocessing state stobj from
       the bytes of the file,
       a file recursion limit of 200 (consistent with GCC),
       the macro table
       (which @(tsee init-ppstate) extends with a new empty scope for the file),
       and the implementation environment.
       The preprocessing of this file may involve
       the recursive preprocessing of more files,
       and the consequent extension of the @('preprocessed') alist.
       If the file is not self-contained,
       @(tsee pproc-*-group-part) returns @(':not-self-contained') as error
       (see @(tsee pproc-files/groups/etc)),
       which this function also returns;
       the caller handles that.
       We ensure that the optional group read by @(tsee pproc-*-group-part)
       ends with the end of the file,
       because we are at the top level,
       not inside a conditional directive.
       If there is no error (and no @(':not-self-contained')),
       a @(tsee scfile) is built and added to @('preprocessed').
       The @(tsee scfile) contains
       the lexemes obtained from the file
       and the macros contributed by the file,
       which are the macros in the innermost scope of the final table.
       The @(tsee scfile) is returned,
       so the caller can use its macros."))
    (b* (((reterr) (irr-scfile) nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         (file (str-fix file))
         (preprocessing (string-list-fix preprocessing))
         (preprocessed (string-scfile-alist-fix preprocessed))
         ((when (member-equal file preprocessing))
          (reterr (msg "Circular file dependencies involving ~&0."
                       preprocessing)))
         (preprocessing (cons file preprocessing))
         (name+scfile (assoc-equal file preprocessed))
         ((when name+scfile) (retok (cdr name+scfile) preprocessed state))
         ((erp lexemes macros preprocessed state)
          (with-local-stobj
            ppstate
            (mv-let (erp rev-lexemes macros ppstate preprocessed state)
                (b* ((ppstate (init-ppstate bytes 200 macros ienv ppstate))
                     ((mv erp groupend rev-lexemes ppstate preprocessed state)
                      (pproc-*-group-part file
                                          base-dir
                                          include-dirs
                                          preprocessed
                                          preprocessing
                                          nil
                                          ppstate
                                          state
                                          (1- limit)))
                     ((unless (groupend-case groupend :eof))
                      (mv (msg "Found directive ~s0 ~
                                without a preceding #if, #ifdef, or #ifndef."
                               (groupend-case
                                groupend
                                :eof (impossible)
                                :elif "#elif"
                                :else "#else"
                                :endif "#endif"))
                          nil (irr-macro-table) ppstate nil state)))
                  (mv erp
                      rev-lexemes
                      (ppstate->macros ppstate)
                      ppstate
                      preprocessed
                      state))
              (mv erp
                  (rev rev-lexemes)
                  (car (macro-table->scopes macros))
                  preprocessed
                  state))))
         (scfile (make-scfile :lexemes lexemes
                              :macros macros))
         (preprocessed (acons file scfile preprocessed)))
      (retok scfile preprocessed state))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-*-group-part ((file stringp)
                              (base-dir stringp)
                              (include-dirs string-listp)
                              (preprocessed string-scfile-alistp)
                              (preprocessing string-listp)
                              (rev-lexemes plexeme-listp)
                              (ppstate ppstatep)
                              state
                              (limit natp))
    :returns (mv erp
                 (groupend groupendp)
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep)
                 (new-preprocessed string-scfile-alistp)
                 state)
    :parents (preprocessor pproc-files/groups/etc)
    :short "Preprocess zero or more group parts."
    :long
    (xdoc::topstring
     (xdoc::p
      "We attempt to preprocess a group part.
       If it is present, we recursively attempt to preprocess more group parts.
       We see whether the group part is present or not
       based on the optional group ending
       returned by @(tsee pproc-?-group-part):
       if it is @('nil'), there was a group part;
       otherwise, there was no group part, and we pass up the group ending."))
    (b* ((ppstate (ppstate-fix ppstate))
         ((reterr) (irr-groupend) nil ppstate nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         ((erp groupend? rev-lexemes ppstate preprocessed state)
          (pproc-?-group-part file
                              base-dir
                              include-dirs
                              preprocessed
                              preprocessing
                              rev-lexemes
                              ppstate
                              state
                              (1- limit)))
         ((when groupend?)
          (retok groupend? rev-lexemes ppstate preprocessed state)))
      (pproc-*-group-part file
                          base-dir
                          include-dirs
                          preprocessed
                          preprocessing
                          rev-lexemes
                          ppstate
                          state
                          (1- limit)))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-?-group-part ((file stringp)
                              (base-dir stringp)
                              (include-dirs string-listp)
                              (preprocessed string-scfile-alistp)
                              (preprocessing string-listp)
                              (rev-lexemes plexeme-listp)
                              (ppstate ppstatep)
                              state
                              (limit natp))
    :returns (mv erp
                 (groupend? groupend-optionp)
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep)
                 (new-preprocessed string-scfile-alistp)
                 state)
    :parents (preprocessor pproc-files/groups/etc)
    :short "Preprocess a group part, if present."
    :long
    (xdoc::topstring
     (xdoc::p
      "If we find a group part, we preprocess it,
       and we return @('nil') as the optional group ending,
       because the group has not ended yet.
       If instead we find no group part,
       we return the group ending that we encounter
       (if we did not encounter a group ending, we would have a group part).")
     (xdoc::p
      "We read the next token or new line,
       skipping over white space and comments.")
     (xdoc::p
      "If we find no token or new line, there are two cases.
       If we found some white space or comments, it is an error,
       because non-empty files must end with new lines [C17:5.2.1.2/2].
       Otherwise, we return the end-of-file group ending.")
     (xdoc::p
      "If we find a hash, we have a directive.
       We read the next token or new line.
       If we find none, it is an error,
       beacuse the file cannot end without a new line [C17:5.2.1.2/2].
       If we find a new line, we have a null directive [C17:6.10.7]:
       we leave the line as is,
       but we wrap the @('#') into a (small) block comment
       (perhaps we could allow a different behavior based on user options).
       If we find an identifier, we dispatch based on the identifier:
       for @('#elif'), @('#else'), and @('#endif'),
       we return the corresponding group ending;
       for other directives, we call separate functions.
       If the identifier is not a directive name,
       or if we do find an identifier,
       we have a non-directive
       (which is a directive, despite the name,
       see footnote 175 in [C17:6.10.3/11]):
       we return an error for now, which is consistent with [C17:6.10/9].")
     (xdoc::p
      "If we do not find a hash, we have a text line.
       We add any preceding white space and comments to the growing lexemes,
       and we call a separate function to handle the rest of the line,
       after putting the non-hash lexeme back.
       In fact, this may preprocess several lines,
       if the line breaks occur within macro arguments.")
     (xdoc::p
      "[C17:6.10.3/5] only allows space and horizontal tab in a directive
       (from just after the @('#') to just before the new line).
       However, [C17:5.1.1.2/1] in phase 3
       (which precedes preprocessing, i.e. phase 4)
       requires comments to be replaced by spaces
       and allows other non-new-line white space to be replaced by spaces.
       Although we do not carry out such replacements,
       we must act as if we did,
       i.e. at least as if we had replaced comments with spaces:
       thus we must accept comments.
       We also choose, as allowed,
       to conceptually replace non-new-line white space
       (i.e. horizontal tab, vertical tab, and form feed)
       with spaces, for maximal liberality.
       Thus, we can accept all white space and comments in a directive,
       as @(tsee read-token/newline) does."))
    (b* ((ppstate (ppstate-fix ppstate))
         ((reterr) nil nil ppstate nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         ((erp nontoknls toknl span ppstate) (read-token/newline ppstate)))
      (cond
       ((not toknl) ; EOF
        (if nontoknls
            (reterr-msg :where (position-to-msg (span->start span))
                        :expected "new line"
                        :found (plexeme-to-msg toknl))
          (retok (groupend-eof)
                 (plexeme-list-fix rev-lexemes)
                 ppstate
                 (string-scfile-alist-fix preprocessed)
                 state)))
       ((plexeme-hashp toknl) ; #
        (b* ((nontoknls-before-hash nontoknls)
             ((erp nontoknls-after-hash toknl2 span2 ppstate)
              (read-token/newline ppstate)))
          (cond
           ((not toknl2) ; # EOF
            (reterr-msg :where (position-to-msg (span->start span2))
                        :expected "a token or new line"
                        :found (plexeme-to-msg toknl2)))
           ((plexeme-case toknl2 :newline) ; # EOL -- null directive
            (b* ((rev-lexemes (plexeme-list-fix rev-lexemes))
                 (rev-lexemes (revappend nontoknls-before-hash rev-lexemes))
                 (rev-lexemes (cons (plexeme-block-comment
                                     (list (char-code #\#)))
                                    rev-lexemes))
                 (rev-lexemes (revappend nontoknls-after-hash rev-lexemes))
                 (rev-lexemes (cons toknl2 ; toknl2 is the new line
                                    rev-lexemes)))
              (retok nil ; no group ending
                     rev-lexemes
                     ppstate
                     (string-scfile-alist-fix preprocessed)
                     state)))
           ((plexeme-case toknl2 :ident) ; # ident
            (b* ((directive (ident->unwrap (plexeme-ident->ident toknl2))))
              (cond
               ((equal directive "elif") ; # elif
                (retok (groupend-elif)
                       (plexeme-list-fix rev-lexemes)
                       ppstate
                       (string-scfile-alist-fix preprocessed)
                       state))
               ((equal directive "else") ; # else
                (retok (groupend-else)
                       (plexeme-list-fix rev-lexemes)
                       ppstate
                       (string-scfile-alist-fix preprocessed)
                       state))
               ((equal directive "endif") ; # endif
                (retok (groupend-endif)
                       (plexeme-list-fix rev-lexemes)
                       ppstate
                       (string-scfile-alist-fix preprocessed)
                       state))
               ((equal directive "if") ; # if
                (reterr (msg "#if directive not yet supported."))) ; TODO
               ((equal directive "ifdef") ; # ifdef
                (reterr (msg "#ifdef directive not yet supported."))) ; TODO
               ((equal directive "ifndef") ; # ifndef
                (reterr (msg "#ifndef directive not yet supported."))) ; TODO
               ((equal directive "include") ; # include
                (b* (((erp rev-lexemes ppstate preprocessed state)
                      (pproc-include nontoknls-before-hash
                                     nontoknls-after-hash
                                     file
                                     base-dir
                                     include-dirs
                                     preprocessed
                                     preprocessing
                                     rev-lexemes
                                     ppstate
                                     state
                                     (1- limit))))
                  (retok nil ; no group ending
                         rev-lexemes
                         ppstate
                         preprocessed
                         state)))
               ((equal directive "define") ; # define
                (b* (((erp ppstate) (pproc-define ppstate)))
                  (retok nil ; no group ending
                         (plexeme-list-fix rev-lexemes)
                         ppstate
                         (string-scfile-alist-fix preprocessed)
                         state)))
               ((equal directive "undef") ; # undef
                (b* (((erp ppstate) (pproc-undef ppstate)))
                  (retok nil ; no group ending
                         (plexeme-list-fix rev-lexemes)
                         ppstate
                         (string-scfile-alist-fix preprocessed)
                         state)))
               ((equal directive "line") ; # line
                (reterr (msg "#line directive not yet supported."))) ; TODO
               ((equal directive "error") ; # error
                (reterr (msg "#error directive not yet supported."))) ; TODO
               ((equal directive "pragma") ; # pragma
                (reterr (msg "#pragma directive not yet supported."))) ; TODO
               (t ;  # other -- non-directive
                (reterr-msg :where (position-to-msg (span->start span2))
                            :expected "a directive name among ~
                                       'if', ~
                                       'ifdef', ~
                                       'ifndef', ~
                                       'elif', ~
                                       'else', ~
                                       'endif', ~
                                       'include', ~
                                       'define', ~
                                       'undef', ~
                                       'line', ~
                                       'error', and ~
                                       'pragma'"
                            :found (msg "the directive name '~s0'"
                                        directive))))))
           (t ;  # non-ident -- non-directive
            (reterr-msg :where (span->start span2)
                        :expected "an identifier"
                        :found (plexeme-to-msg toknl2))))))
       (t ; non-# -- text line
        (b* ((rev-lexemes (revappend nontoknls (plexeme-list-fix rev-lexemes)))
             (ppstate (unread-lexeme toknl span ppstate))
             ((erp rev-new-lexemes ppstate)
              (pproc-lexemes (macrep-mode-line)
                             nil ; rev-lexemes
                             0 ; paren-level
                             nil ; no-expandp
                             nil ; disabled
                             nil ; directivep
                             ppstate
                             limit))) ; unrelated to limit for this clique
          (retok nil ; no group ending
                 (append rev-new-lexemes rev-lexemes)
                 ppstate
                 (string-scfile-alist-fix preprocessed)
                 state)))))
    :measure (nfix limit)
    :no-function nil)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-include ((nontoknls-before-hash plexeme-listp)
                         (nontoknls-after-hash plexeme-listp)
                         (file stringp)
                         (base-dir stringp)
                         (include-dirs string-listp)
                         (preprocessed string-scfile-alistp)
                         (preprocessing string-listp)
                         (rev-lexemes plexeme-listp)
                         (ppstate ppstatep)
                         state
                         (limit natp))
    :returns (mv erp
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep)
                 (new-preprocessed string-scfile-alistp)
                 state)
    :parents (preprocessor pproc-files/groups/etc)
    :short "Preprocess a @('#include') directive."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called just after the @('include') identifier has been parsed.
       We also pass the comments and white space before and after the @('#').")
     (xdoc::p
      "We obtain the next token or new line.
       we pass @('t') as the @('headerp') flag,
       so that we can properly lex header names,
       which would otherwise be lexed as string literals
       or as the puctuator @('<') just for the opening angle bracket.
       String literals and @('<') cannot be
       macro-expanded to a header name,
       so it is always correct to lex with the @('headerp') flag @('t').")
     (xdoc::p
      "If we do not find a token or new line,
       it is an error, because there is no header name,
       and there is no macro that could result in a header name.")
     (xdoc::p
      "If we find a new line,
       it is an error, because there is no header name,
       and there is no macro that could result in a header name.")
     (xdoc::p
      "If we find a header name,
       we ensure that we find a new line without intervening tokens,
       i.e. that there is nothing (of significance) after the directive
       in the line (see grammar).")
     (xdoc::p
      "We resolve the header name to a file,
       and we call @(tsee pproc-file) to preprocess it.
       If the call returns @(':not-self-contained') as @('erp'),
       the included file is not self-contained,
       and we need to expand it in place:
       we put any unread character back into the current input bytes
       (see documentation of @(tsee unread-pchar-to-bytes)),
       and we store the bytes from the file into the stobj
       (see documentation of @(tsee ppstate-add-bytes)).
       If the call of @(tsee pproc-file) returns some other error,
       we pass it up to the caller.
       If the call returns no error,
       we leave the @('#include') directive as is,
       including all the comments and white space.
       We also incorporate the returned macros into
       the top scope of the macros of the current file;
       although we do not expand the file in place,
       in order to process the rest of the including file,
       we need to act as if we had expanded the included file in place,
       i.e. its macros must be available.")
     (xdoc::p
      "Note that @(tsee resolve-included-file)
       always reads the whole file and returns its bytes,
       which is wasteful when the file is found in @('preprocessed').
       We may improve this aspect at some point.")
     (xdoc::p
      "If, after the @('#') and @('include') tokens,
       we find a token that is not a header name,
       for now we return an error,
       but we should preprocess that token and any subsequent tokens,
       and see if they result in a header name."))
    (b* ((ppstate (ppstate-fix ppstate))
         ((reterr) nil ppstate nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         ((erp nontoknls-before-header toknl span ppstate)
          (read-token/newline-after-include ppstate)))
      (cond
       ((not toknl) ; # include EOF
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a token"
                    :found (plexeme-to-msg toknl)))
       ((plexeme-case toknl :newline) ; # include EOL
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a token"
                    :found (plexeme-to-msg toknl)))
       ((plexeme-case toknl :header) ; # include headername
        (b* (((erp nontoknls-after-header toknl2 span2 ppstate)
              (read-token/newline ppstate))
             ((unless (and toknl2 ; # include headername EOL
                           (plexeme-case toknl2 :newline)))
              (reterr-msg :where (position-to-msg (span->start span2))
                          :expected "a new line"
                          :found (plexeme-to-msg toknl2)))
             ((erp resolved-file bytes state)
              (resolve-included-file file
                                     (plexeme-header->name toknl)
                                     base-dir
                                     include-dirs
                                     state))
             ((mv erp scfile preprocessed state)
              (pproc-file bytes
                          resolved-file
                          base-dir
                          include-dirs
                          preprocessed
                          preprocessing
                          (ppstate->macros ppstate)
                          (ppstate->ienv ppstate)
                          state
                          (1- limit)))
             ((when (eq erp :not-self-contained))
              (b* ((ppstate (unread-pchar-to-bytes ppstate))
                   ((erp ppstate) (ppstate-add-bytes bytes ppstate)))
                (retok (plexeme-list-fix rev-lexemes)
                       ppstate
                       (string-scfile-alist-fix preprocessed)
                       state)))
             ((when erp) (reterr erp))
             (ppstate (update-ppstate->macros
                       (macro-table-extend-top
                        (scfile->macros scfile)
                        (ppstate->macros ppstate))
                       ppstate))
             (nontoknls-before-hash (plexeme-list-fix nontoknls-before-hash))
             (nontoknls-after-hash (plexeme-list-fix nontoknls-after-hash))
             (rev-lexemes (plexeme-list-fix rev-lexemes))
             (rev-lexemes (revappend nontoknls-before-hash rev-lexemes))
             (rev-lexemes (cons (plexeme-punctuator "#") rev-lexemes))
             (rev-lexemes (revappend nontoknls-after-hash rev-lexemes))
             (rev-lexemes (cons (plexeme-ident (ident "include")) rev-lexemes))
             (rev-lexemes (revappend nontoknls-before-header rev-lexemes))
             (rev-lexemes (cons toknl rev-lexemes)) ; toknl is header name
             (rev-lexemes (revappend nontoknls-after-header rev-lexemes))
             (rev-lexemes (cons toknl2 ; toknl2 is new line
                                rev-lexemes)))
          (retok rev-lexemes ppstate preprocessed state)))
       (t ; # include token
        (reterr (msg "Non-direct #include not yet supported."))))) ; TODO
    :measure (nfix limit)
    :no-function nil)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :prepwork ((set-bogus-mutual-recursion-ok t) ; TODO: remove eventually
             (local
              (in-theory
               (enable
                acons
                scfilep-of-cdr-of-assoc-equal-when-string-scfile-alistp))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  :guard-hints
  (("Goal" :in-theory (enable alistp-when-string-scfile-alistp-rewrite
                              true-listp-when-plexeme-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pproc-files ((files string-listp)
                     (base-dir stringp)
                     (include-dirs string-listp)
                     (ienv ienvp)
                     state
                     (recursion-limit natp))
  :returns (mv erp (fileset filesetp) state)
  :short "Preprocess zero or more files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level function of the preprocessor.
     The files are identified by the @('files') strings,
     which must be paths relative to the @('base-dir') string path:
     this is the same interface as @(tsee input-files).
     The list @('include-dirs') specifies the directories to search
     for @('#include') directives with angle brackets.")
   (xdoc::p
    "The elements of @('files') are preprocessed in order.
     Each file is read from the file system
     and preprocessed via @(tsee pproc-file).
     Since the starting macro table is empty in these calls,
     @(tsee pproc-file) cannot return @(':not-self-contained') as @('erp'),
     but we double-check it here, throwing a hard error if the check fails.
     We pass any other error up to the caller.
     If there is no error, the returned @(tsee scfile) is discarded,
     because we are at the top level
     and there are no macros to incorporate.
     Note that @(tsee pproc-file) ensures, as a post-condition,
     thet @(tsee scfile) is in the @('preprocessed') alist.")
   (xdoc::p
    "We keep track of the files under preprocessing in a list (initially empty),
     to detect and avoid circularities.")
   (xdoc::p
    "The result of this function is a file set,
     whose paths are generally a superset of the input ones:
     the files specified by @('files') may include, directly or indirectly,
     files whose paths are not in @('files'), e.g. files from the C library.
     The resulting file set is ``closed'' with respect to @('#include'):
     the @(see self-contained) ones are in the file set,
     and the non-@(see self-contained) ones have been expanded.")
   (xdoc::p
    "The recursion limit is discussed in @(tsee pproc-files/groups/etc).
     It seems best to let the user set this limit (outside this function),
     with perhaps a reasonably large default."))
  (b* (((reterr) (irr-fileset) state)
       ((erp preprocessed state)
        (pproc-files-loop files base-dir include-dirs
                          nil nil ienv state recursion-limit)))
    (retok
     (fileset (string-scfile-alist-to-filepath-filedata-map preprocessed))
     state))
  :hooks nil

  :prepwork
  ((define pproc-files-loop ((files string-listp)
                             (base-dir stringp)
                             (include-dirs string-listp)
                             (preprocessed string-scfile-alistp)
                             (preprocessing string-listp)
                             (ienv ienvp)
                             state
                             (recursion-limit natp))
     :returns (mv erp (new-preprocessed string-scfile-alistp) state)
     :parents nil
     (b* (((reterr) nil state)
          ((when (endp files))
           (retok (string-scfile-alist-fix preprocessed) state))
          (file (str-fix (car files)))
          (path-to-read (str::cat base-dir "/" file))
          ((mv erp bytes state)
           (acl2::read-file-into-byte-list path-to-read state))
          ((when erp)
           (reterr (msg "Cannot read file ~x0." path-to-read)))
          ((mv erp & preprocessed state) (pproc-file bytes
                                                     (car files)
                                                     base-dir
                                                     include-dirs
                                                     preprocessed
                                                     preprocessing
                                                     (macro-table-init)
                                                     ienv
                                                     state
                                                     recursion-limit))
          ((when (eq erp :not-self-contained))
           (raise "Internal error: non-self-contained top-level file ~x0." file)
           (reterr t))
          ((when erp) (reterr erp)))
       (pproc-files-loop (cdr files)
                         base-dir
                         include-dirs
                         preprocessed
                         preprocessing
                         ienv
                         state
                         recursion-limit))
     :guard-hints
     (("Goal" :in-theory (enable alistp-when-string-scfile-alistp-rewrite)))
     :no-function nil
     :hooks nil)))
