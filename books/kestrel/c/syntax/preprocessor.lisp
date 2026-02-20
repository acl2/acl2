; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "preprocessor-options")
(include-book "preprocessor-lexemes")
(include-book "preprocessor-files")
(include-book "macro-tables")
(include-book "preprocessor-states")
(include-book "preprocessor-messages")
(include-book "stringization")
(include-book "token-concatenation")
(include-book "preprocessor-evaluator")
(include-book "preprocessor-reader")
(include-book "preprocessor-lexer")
(include-book "preprocessor-printer")
(include-book "preservable-inclusions")
(include-book "files")

(include-book "kestrel/file-io-light/read-file-into-byte-list" :dir :system)
(include-book "std/strings/strpos" :dir :system)
(include-book "std/strings/strrpos" :dir :system)

(local (include-book "kestrel/arithmetic-light/max" :dir :system))
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
     an unless an option for full expansion is selected by the user,
     preserves preprocessing constructs particularly @('#include') directives,
     under conditions that should be often satisfied in practical code.
     That is, instead of expanding @('#include') directives in place,
     i.e. replacing them with the referenced files,
     it leaves them in place, preprocessing the included file separately,
     to preserve the original structure of the code.
     This is only done under certain conditions;
     in general, the C preprocessor operates at the low lexical level,
     making it difficult to preserve code structure in general
     (in those cases, our preprocessor expands the included files in place,
     like typical preprocessors).")
   (xdoc::p
    "The correctness criterion for the preservation of preprocessing constructs
     is that the full preprocessing expansion of the original files
     must be the same as the of the files produced by our preprocessor.
     That is, if we apply full preprocessing,
     i.e. the one done by typical preprocessors,
     to the result of our preprocessor,
     we must obtain the same results as
     applying full preprocessing to the original files.")
   (xdoc::p
    "The input to our preprocessor is similar to @(tsee input-files):
     the files to preprocess are specified by
     (1) a base directory path and (2) a list of file paths.
     The base directory path (1) may be absolute,
     or relative to the "
    (xdoc::seetopic "cbd" "connected book directory")
    ". The file paths in the list (2) are relative to the base directory.")
   (xdoc::p
    "Our preprocessor maps (1) and (2) to a file set (see @(see files)):
     it preprocesses all the files listed in (2),
     as well as all the files directly and indirectly included.
     When a @('#include') directive references a file not in (2)
     (e.g. a header from the standard library),
     if that @('#include') directive is preserved,
     the file set resulting from our preprocessor contains
     an entry for that included file as well.
     The file set resulting from our preprocessor contains entries
     for all the files with the file paths in the given list,
     as well as for zero or more files
     referenced in at least one preserved @('#include').
     These preserved @('#include')s may occur in the files in (2),
     or in files transitively brought in by the additional files.
     The file set returned by our preprocessor
     is closed with respect to the preserved @('#include')s.")
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
     the paths of the files relative to the base directory (1).
     In contrast, absolute path keys in the output file set are for
     files included via @('#include') directives with angle brackets,
     which our preprocessor searches in certain directories,
     unrelated to the base directory.
     Some of these files may actually be included via double quotes,
     so long as they are not found relative to the including file,
     because in that case, according to [C17:6.10.2/3],
     an attempt is made to locate the file as if it had angle brackets.
     [C17:6.10.2] gives leeway in how included file are resolved;
     our preprocessor uses an approch similar to GCC [CPPM:2.3].
     The directories where to search files included with angle brackets
     (and with double quotes when the search from the including file fails)
     are passed as an additional input to our preprocessor.")
   (xdoc::p
    "The exact conditions under which @('#include')s are preserved,
     along with the approach we use to check those conditions,
     are discussed in @(see preservable-inclusions).")
   (xdoc::p
    "Our preprocessor
     reads characters from files,
     lexes them into lexemes,
     and parses the lexemes while executing the preprocessing directives.
     The resulting sequences of lexemes are then turned into characters
     that are written (printed) to files.
     The resulting file set is amenable to our parser,
     but our parser needs a few more extensions to be able to accept
     everything that our preprocessor can generate.
     Our preprocessor preserves white space and comments when possible,
     but some layout (i.e. white space) changes are inherent to preprocessing,
     some comments may be difficult or impossible to preserve
     (e.g. if they occur within macro parameters),
     and some preserved comments may no longer apply to preprocessed code
     (e.g. comments talking about macros).")
   (xdoc::p
    "Currently some of this preprocessor's code duplicates, at some level,
     some of the code in the @(see parser)
     (including the @(see lexer) and the @(see reader)).
     At some point we should integrate the preprocessor with the parser.")
   (xdoc::p
    "Our currently implemented approach
     to limit recursive macro expansion [C17:6.10.3.4/2]
     should work in most cases, but it may not be fully general.
     In some contrived cases, which seem nonetheless legal according to [C17],
     the approach may generate non-balanced start/end markers.
     Some quick experiments show that Clang fails in those cases as well.
     This needs further investigation,
     but we are planning to implement a more general that should always work,
     by avoiding markers altogether,
     instead attaching ``provenance'' information to certain tokens."))
  :order-subtopics (preprocessor-options
                    preprocessor-lexemes
                    preprocessor-files
                    macro-tables
                    preprocessor-states
                    preprocessor-messages
                    stringization
                    token-concatenation
                    preprocessor-evaluator
                    preprocessor-reader
                    preprocessor-lexer
                    preprocessor-printer
                    preservable-inclusions
                    t)
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist string-pfile-alist
  :short "Fixtype of alists from strings to preprocessor files."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use these alists to keep track of which files
     have been already preprocessed.
     The alist is initially empty,
     and eventually contains an entry for each file
     whose path is specified as input to the preprocessor,
     ad well as zero or more additional entries for
     other files references in preserved @('#include')s
     (see @(see preservable-inclusions)).")
   (xdoc::p
    "These alists always have unique keys, i.e. there are no shadowed pairs;
     this is not enforced in this fixtype.
     The keys are file paths,
     either absolute,
     or relative to the base directory passed to the @(see preprocessor).
     The alist has the same keys as the file set returned by our preprocessor;
     see @(tsee string-pfile-alist-to-filepath-filedata-map)."))
  :key-type string
  :val-type pfile
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred string-pfile-alistp
  :prepwork ((set-induction-depth-limit 1))

  ///

  (defruled pfilep-of-cdr-of-assoc-equal-when-string-pfile-alistp
    (implies (and (string-pfile-alistp alist)
                  (assoc-equal key alist))
             (pfilep (cdr (assoc-equal key alist))))
    :induct t
    :enable assoc-equal)

  (defrule len-of-string-pfile-alist-fix-upper-bound
    (<= (len (string-pfile-alist-fix alist))
        (len alist))
    :rule-classes :linear
    :induct t
    :enable (len string-pfile-alist-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-pfile-alist-to-filepath-filedata-map
  ((alist string-pfile-alistp))
  :returns (map filepath-filedata-mapp)
  :short "Turn (1) an alist from string to preprocessor files
          into (2) a map from file paths to file data."
  :long
  (xdoc::topstring
   (xdoc::p
    "The strings are wrapped into file paths;
     as mentioned in @(tsee string-pfile-alist),
     the alist has unique keys, so the order of the alist is immaterial.
     The lists of lexemes are printed to bytes,
     obtaining the file datas.")
   (xdoc::p
    "This is called on the alist at the end of the preprocessing,
     as explained in @(tsee string-pfile-alist)."))
  (b* (((when (endp alist)) nil)
       ((cons string pfile) (car (string-pfile-alist-fix alist)))
       (bytes (pprint-pfile pfile))
       (filepath (filepath string))
       (filedata (filedata bytes))
       (map (string-pfile-alist-to-filepath-filedata-map (cdr alist))))
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
      to replace identifiers with 0 [C17:6.10.1/4].")
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

(define resolve-in-include-dirs ((included-file stringp)
                                 (include-dirs string-listp)
                                 state)
  :returns (mv erp
               (resolved-included-file stringp)
               (file-bytes byte-listp)
               state)
  :short "Resolve a header name (in string form) to a file,
          looking in a list of absolute paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called by @(tsee resolve-included-file),
     when the file must be looked up in a list of absolute paths:
     this is the case for angle-bracket header names,
     as well as for double-quote header names
     that cannot be resolved relative to the including file.")
   (xdoc::p
    "We go through each absolute path in the @('include-dirs') list,
     and we try to read the file there.
     We stop as soon as we find a file.
     We return an error if we cannot find the file."))
  (b* (((reterr) "" nil state)
       ((when (endp include-dirs))
        (reterr (msg "Cannot resolve the file ~s0 in any of ~x1."
                     (str-fix included-file) (string-list-fix include-dirs))))
       (path-to-try (str::cat (car include-dirs) "/" included-file))
       ((mv erp bytes state)
        (acl2::read-file-into-byte-list path-to-try state))
       ((when (not erp)) (retok path-to-try bytes state)))
    (resolve-in-include-dirs included-file (cdr include-dirs) state))
  :hooks nil)

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
      which are tried in order until a file can be read,
      via a separate function.
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
    "#include \"file.h\"       // included-file-path = /absolute/file.h"
    "#include \"sub/file.h\"   // included-file-path = /absolute/sub/file.h"
    ""
    "relative/including.c:   // dir-of-including-file = base/relative/"
    "#include \"file.h\"       // included-file-path = base/relative/file.h"
    "#include \"sub/file.h\"   // included-file-path = base/relative/sub/file.h"
    ""
    "including.c:            // dir-of-including-file = base/"
    "#include \"file.h\"       // included-file-path = base/file.h"
    "#include \"sub/file.h\"   // included-file-path = base/sub/file.h"))
  ;; In each group of three lines above,
  ;; the extra indentation of // in the 2nd and 3rd lines
  ;; compensate for the two \ in the two \" in those lines.
  (b* (((reterr) "" nil state)
       ((when (header-name-case included-file :angles))
        (b* (((erp include-file-ascii)
              (h-char-list-to-string (header-name-angles->chars included-file))))
          (resolve-in-include-dirs include-file-ascii include-dirs state)))
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
       ((when erp)
        (resolve-in-include-dirs included-file-ascii include-dirs state)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(define peek-token/newline ((stop-at-newline-p booleanp) (ppstate ppstatep))
  :returns (mv erp
               (toknl? plexeme-optionp)
               (new-ppstate ppstatep))
  :short "Peek the next token, or optionally new line."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is currently used only in one situation,
     namely to see whether a function-like macro name
     is followed by an open parenthesis or not.
     [C17:6.10.3/10] says that
     every occurrence of the macro name followed by an open parenthesis
     is expanded as a macro call;
     the implication, easily verified in Clang,
     is that an occurrence of the macro not followed by an open parenthesis
     is not an error, but the name is simply treated as an identifier.")
   (xdoc::p
    "If we are in a directive line,
     a new line ends the directive [C17:6.10/2];
     in this case, the @('stop-at-newline-p') flag is @('t').
     If we are not in a directive line,
     an invocation of a function-like macro may include new lines
     [C17:6.10.3/10;
     in this case, the @('stop-at-newline-p') flag is @('nil').
     The flag determines whether we stop at (and return) a new line,
     or whether we skip new lines and just find a token.")
   (xdoc::p
    "We go through lexmarks until we reach the end of file,
     in which case we return @('nil'),
     or until we reach a token or possibly a new line (depending on the flag).
     But none of the lexmarks are consumed:
     they are all pushed back onto the pending lexmarks."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil ppstate)
       ((erp lexmark ppstate) (read-lexmark ppstate)))
    (cond
     ((not lexmark) ; EOF
      (retok nil ppstate))
     ((and (lexmark-case lexmark :lexeme) ; token(/EOL)
           (or (plexeme-tokenp (lexmark-lexeme->lexeme lexmark))
               (and stop-at-newline-p
                    (plexeme-case (lexmark-lexeme->lexeme lexmark) :newline))))
      (b* ((ppstate (push-lexmark lexmark ppstate)))
        (retok (lexmark-lexeme->lexeme lexmark) ppstate)))
     (t ; comment or white space
      (b* (((erp toknl? ppstate) (peek-token/newline stop-at-newline-p ppstate))
           (ppstate (push-lexmark lexmark ppstate)))
        (retok toknl? ppstate)))))
  :measure (ppstate->size ppstate)

  ///

  (defret ppstate->size-of-peek-token/newline
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
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
               (newline plexemep)
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
     at the start or end of the replacement list [C17:6.10.3.3/1].
     We also return the final new line lexeme."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil (irr-plexeme) ppstate)
       ((erp replist newline ppstate)
        (read-macro-object-replist-loop t ppstate))
       ((when (and (consp replist)
                   (or (plexeme-hashhashp (car replist))
                       (plexeme-hashhashp (car (last replist))))))
        (reterr (msg "The replacement list of ~x0 starts or ends with ##."
                     (ident-fix name)))))
    (retok replist newline ppstate))

  :prepwork
  ((define read-macro-object-replist-loop ((startp booleanp) (ppstate ppstatep))
     :returns (mv erp
                  (replist plexeme-listp)
                  (newline plexemep)
                  (new-ppstate ppstatep))
     :parents nil
     (b* ((ppstate (ppstate-fix ppstate))
          ((reterr) nil (irr-plexeme) ppstate)
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
         (retok nil toknl ppstate))
        (t ; token
         (b* (((erp replist newline ppstate) ; token replist
               (read-macro-object-replist-loop nil ppstate))
              (replist (cons toknl replist))
              (replist (if (and nontoknls
                                (not startp))
                           (cons (plexeme-spaces 1) replist)
                         replist)))
           (retok replist newline ppstate)))))
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
        '(:use plexeme-token/newline-p-of-read-token/newline)))

     (defret plexeme-newline-of-read-macro-object-replist-loop
       (implies (not erp)
                (equal (plexeme-kind newline) :newline))
       :hints (("Goal" :induct t)))))

  ///

  (defret plexeme-list-token/space-p-of-read-macro-object-replist
    (plexeme-list-token/space-p replist))

  (defret plexeme-newline-of-read-macro-object-replist
    (implies (not erp)
             (equal (plexeme-kind newline) :newline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-macro-function-replist ((name identp)
                                     (params ident-listp)
                                     (ellipsis booleanp)
                                     (ppstate ppstatep))
  :returns (mv erp
               (replist plexeme-listp)
               (newline plexemep)
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
     only if the macro has ellipsis.")
   (xdoc::p
    "We also return the final new line lexeme."))
  (read-macro-function-replist-loop name nil params ellipsis ppstate)

  :prepwork
  ((define read-macro-function-replist-loop ((name identp)
                                             (previous plexeme-optionp)
                                             (params ident-listp)
                                             (ellipsis booleanp)
                                             (ppstate ppstatep))
     :returns (mv erp
                  (replist plexeme-listp)
                  (newline plexemep)
                  (hash-params ident-listp)
                  (new-ppstate ppstatep))
     :parents nil
     (b* ((ppstate (ppstate-fix ppstate))
          ((reterr) nil (irr-plexeme) nil ppstate)
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
           (retok nil toknl nil ppstate)))
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
              ((erp replist newline hash-params ppstate)
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
           (retok replist newline hash-params ppstate)))
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
              ((erp replist newline hash-params ppstate)
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
           (retok replist newline hash-params ppstate)))
        (t ; other token
         (b* (((when (and previous
                          (plexeme-hashp previous))) ; # token
               (reterr (msg "The replacement list of ~x0 ~
                             must not contain a # ~
                             not immediately followed by a parameter."
                            (ident-fix name))))
              ((erp replist newline hash-params ppstate)
               (read-macro-function-replist-loop name
                                                 toknl
                                                 params
                                                 ellipsis
                                                 ppstate))
              (replist (cons toknl replist))
              (replist (if (and previous nontoknls)
                           (cons (plexeme-spaces 1) replist)
                         replist)))
           (retok replist newline hash-params ppstate)))))
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

     (defret plexeme-newline-of-read-macro-function-replist-loop
       (implies (not erp)
                (equal (plexeme-kind newline) :newline))
       :hints (("Goal" :induct t)))

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

  (defret plexeme-newline-of-read-macro-function-replist
    (implies (not erp)
             (equal (plexeme-kind newline) :newline)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rebuild-define-directive-id ((name identp) (newline-at-end plexemep))
  :returns (lexemes plexeme-listp)
  :short "Rebuild a @('#define') directive from its name,
          defining it as an identity."
  :long
  (xdoc::topstring
   (xdoc::p
    "The rationale for this identity definition
     is explained in @(see preservable-inclusions)."))
  (list (plexeme-punctuator "#")
        (plexeme-ident (ident "define"))
        (plexeme-spaces 1)
        (plexeme-ident name)
        (plexeme-spaces 1)
        (plexeme-ident name)
        (plexeme-fix newline-at-end)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pproc-define ((ppstate ppstatep))
  :returns (mv erp
               (pparts ppart-listp)
               (new-ppstate ppstatep))
  :short "Preprocess a @('#define') directive."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called just after the @('define') identifier has been parsed.
     We do not pass the comments and white space before and after the @('#'),
     because we make no use of them, at least for now.")
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
     the macro definition is syntactically incorrect.")
   (xdoc::p
    "Unless full expansion is required in the options,
     we add to the output a @('#define N N'),
     where @('N') is the name of the macro.
     The rationale is explained in @(see preservable-inclusions).
     But we omit the generation of this @('#define N N')
     if this directive is the one for the header guard,
     i.e. the one that changes the @(tsee hg-state)
     from (':ifndef') to @(':define'),
     because it is already generated in @(tsee all-rev-lexemes)."))
  (b* ((ppstate (ppstate-fix ppstate)) ; # define
       ((reterr) nil ppstate)
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
           ((erp new-macros) (macro-define name info macros))
           (ppstate (update-ppstate->macros new-macros ppstate))
           (ppstate (if (ppoptions->full-expansion (ppstate->options ppstate))
                        ppstate
                      (if (and (hg-state-case (ppstate->hg ppstate) :ifndef)
                               (equal name
                                      (hg-state-ifndef->name
                                       (ppstate->hg ppstate))))
                          ppstate
                        (add-rev-lexemes
                         (rebuild-define-directive-id name lexeme)
                         ppstate))))
           (ppstate (hg-trans-define name t ppstate))
           (pparts (if (ppoptions->full-expansion (ppstate->options ppstate))
                       nil
                     (list (ppart-line
                            (rebuild-define-directive-id name lexeme))))))
        (retok pparts ppstate)))
     ((and lexeme
           (not (plexeme-token/newline-p lexeme))) ; # define name WSC
      (b* (((erp replist newline ppstate) ; # define name WSC REPLIST EOL
            (read-macro-object-replist name ppstate))
           (macros (ppstate->macros ppstate))
           (info (make-macro-info-object :replist replist))
           ((erp new-macros) (macro-define name info macros))
           (ppstate (update-ppstate->macros new-macros ppstate))
           (ppstate (hg-trans-define name (not replist) ppstate))
           (ppstate (if (ppoptions->full-expansion (ppstate->options ppstate))
                        ppstate
                      (add-rev-lexemes
                       (rebuild-define-directive-id name newline) ppstate)))
           (pparts (if (ppoptions->full-expansion (ppstate->options ppstate))
                       nil
                     (list (ppart-line
                            (rebuild-define-directive-id name newline))))))
        (retok pparts ppstate)))
     ((and lexeme
           (plexeme-equiv lexeme (plexeme-punctuator "("))) ; # define (
      (b* (((erp params ellipsis ppstate) ; # define ( params )
            (read-macro-params ppstate))
           ((erp replist newline hash-params ppstate)
            ;; # define ( params ) replist EOL
            (read-macro-function-replist name params ellipsis ppstate))
           (macros (ppstate->macros ppstate))
           (info (make-macro-info-function :params params
                                           :ellipsis ellipsis
                                           :replist replist
                                           :hash-params hash-params))
           ((erp new-macros) (macro-define name info macros))
           (ppstate (update-ppstate->macros new-macros ppstate))
           (ppstate (hg-trans-define name nil ppstate))
           (ppstate (if (ppoptions->full-expansion (ppstate->options ppstate))
                        ppstate
                      (add-rev-lexemes
                       (rebuild-define-directive-id name newline) ppstate)))
           (pparts (if (ppoptions->full-expansion (ppstate->options ppstate))
                       nil
                     (list (ppart-line
                            (rebuild-define-directive-id name newline))))))
        (retok pparts ppstate)))
     (t ; # define EOF/other
      (reterr-msg :where (position-to-msg (span->start lexeme-span))
                  :expected "a left parenthesis or ~
                             a comment or ~
                             a new line or ~
                             other white space"
                  :found (plexeme-to-msg lexeme)))))
  :no-function nil
  :guard-simplify :limited ; to stop (:E IDENT)
  :guard-hints
  (("Goal" :in-theory (e/d (alistp-when-ident-macro-info-alistp-rewrite)
                           ((:e ident))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rebuild-undef-directive ((name identp) (newline-at-end plexemep))
  :returns (lexemes plexeme-listp)
  :short "Rebuild a @('#undef') directive from its name."
  (list (plexeme-punctuator "#")
        (plexeme-ident (ident "undef"))
        (plexeme-spaces 1)
        (plexeme-ident name)
        (plexeme-fix newline-at-end)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pproc-undef ((ppstate ppstatep))
  :returns (mv erp
               (pparts ppart-listp)
               (new-ppstate ppstatep))
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
     Note that @(tsee macro-undefine) takes care of
     ensuring that the macro is not a predefined one.")
   (xdoc::p
    "Unless full expansion is required in the options,
     we add to the output the @('#undef') directive.
     The rationale is explained in @(see preservable-inclusions)."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil ppstate)
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
       ((erp new-macros) (macro-undefine name macros))
       (ppstate (update-ppstate->macros new-macros ppstate))
       (ppstate (hg-trans-non-ifndef/elif/else/define ppstate))
       (ppstate (if (ppoptions->full-expansion (ppstate->options ppstate))
                    ppstate
                  (add-rev-lexemes (rebuild-undef-directive name newline?)
                                   ppstate)))
       (pparts (if (ppoptions->full-expansion (ppstate->options ppstate))
                   nil
                 (list (ppart-line (rebuild-undef-directive name newline?))))))
    (retok pparts ppstate))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist ident-lexmark-list-alist
  :short "Fixtype of alists from identifiers to lists of lexmarks."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used to model the mapping of macro parameters
     to the corresponding macro arguments.
     The macro arguments retain their markers,
     so we have a list of lexmarks and not just of lexemes."))
  :key-type ident
  :val-type lexmark-list
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t
  :pred ident-lexmark-list-alistp
  :prepwork ((set-induction-depth-limit 1))

  ///

  (defruled lexmark-listp-of-cdr-of-assoc-equal-when-ident-lexmark-list-alistp
    (implies (and (ident-lexmark-list-alistp alist)
                  (assoc-equal key alist))
             (lexmark-listp (cdr (assoc-equal key alist))))
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

(define find-first-token/marker ((lexmarks lexmark-listp))
  :returns (mv (wsc lexmark-listp)
               (token/marker? lexmark-optionp)
               (lexmarks-rest lexmark-listp))
  :short "Find the first token or marker in a list of lexmarks, if any."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is no token or marker, we return @('nil').
     If we find a token or marker, we return it,
     and we also return the white space and comments that precede the token;
     if there is no token or marker, these are all the lexemes passed as input.
     We also return the remaining lexmarks."))
  (b* (((when (endp lexmarks)) (mv nil nil nil))
       (lexmark (car lexmarks))
       ((when (or (not (lexmark-case lexmark :lexeme))
                  (plexeme-tokenp (lexmark-lexeme->lexeme lexmark))))
        (mv nil (lexmark-fix lexmark) (lexmark-list-fix (cdr lexmarks))))
       ((mv wsc token/marker? lexmarks) (find-first-token/marker (cdr lexmarks))))
    (mv (cons (lexmark-fix lexmark) wsc) token/marker? lexmarks))

  ///

  (defret len-of-find-first-token/marker
    (implies token/marker?
             (< (len lexmarks-rest)
                (len lexmarks)))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define normalize-macro-arg ((arg lexmark-listp))
  :returns (norm-arg lexmark-listp)
  :short "Normalize a macro argument,
          turning comments and white space (including new lines)
          into single spaces between tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "When we calculate the arguments of a macro call,
     each argument is a list of zero or more lexmarks
     (not just lexemes, because we need to retain the markers);
     the calculation involves macro expansion within the arguments themselves,
     unless the corresponding parameters in the macro's replacement list
     are preceded by @('#') or @('##') or followed by @('##')
     [C17:6.10.3.1/1].
     Each calculated argument needs to replace the correspoding parameter
     in the replacement list in order to realize the macro call
     [C17:6.10.3/10].
     The list of lexmarks that forms an argument
     could include comments and white space,
     including new lines [C17:6.10.3/10].
     Since we generally try to preserve comments and white space,
     there might be reasons to preserve comments and white space
     in the arguments passed to a macro;
     but for now, to keep things simple,
     we normalize all those comments and white space
     to single spaces between tokens.
     That is, given the list of lexmarks that forms an argument,
     we remove all the white space and comments at the start and end,
     and we join all the contiguous white space and comments
     into single spaces.
     Note that the evaluation of @('#') [C17:6.10.3.2/2]
     requires to normalize comments and white space that separate token
     to single spaces,
     so our normalization is consistent with that.")
   (xdoc::p
    "The resulting list of lexemes is a sequence of tokens and markers
     with single spaces between some of the tokens (ignoring markers).")
   (xdoc::p
    "This function performs this normalization."))
  (normalize-macro-arg-loop t arg)

  :prepwork
  ((define normalize-macro-arg-loop ((startp booleanp) (arg lexmark-listp))
     :returns (norm-arg lexmark-listp)
     :parents nil
     (b* (((mv wsc token/marker arg-rest) (find-first-token/marker arg))
          ((when (not token/marker)) nil)
          (norm-arg-rest (normalize-macro-arg-loop nil arg-rest)))
       (append (if (or startp
                       (not wsc))
                   nil
                 (list (make-lexmark-lexeme :lexeme (plexeme-spaces 1)
                                            :span (irr-span))))
               (cons token/marker
                     norm-arg-rest)))
     :measure (len arg)
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define space-lexmark-singleton? ((spacep booleanp))
  :returns (lexmark-singleton? lexmark-listp)
  :short "Return a singleton list containing a single space lexmark
          if the input is @('t'), otherwise return the empty list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee replace-macro-args),
     to optionally add a space in a list of generated lexmarks."))
  (and spacep
       (list (make-lexmark-lexeme :lexeme (plexeme-spaces 1)
                                  :span (irr-span)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define replace-macro-args ((replist plexeme-listp)
                            (subst ident-lexmark-list-alistp))
  :guard (plexeme-list-token/space-p replist)
  :returns (lexmarks/placemarkers lexmark-option-listp)
  :short "In the replacement list of a function-like macro,
          replace all the parameters with the corresponding arguments,
          and evaluate the @('#') and operator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The alist @('subst') is calculated elsewhere.
     It consists of the parameter names as keys,
     including @('__VA_ARGS__') if the macro has ellipsis,
     and the corresponding list of lexmarks as values.
     The list of lexmarks associated to each parameter
     is generally fully replaced [C17:6.10.3.1],
     unless it is preceded by @('#') or @('##') or followed by @('##'),
     in which case the argument lexemes are not replaced.
     Either way, the alist has the appropriate lists of lexmarks here;
     the markers are needed because we need to retain the information about
     which macros have been expanded where in the arguments,
     to prevent re-expansion when we rescan
     the substituted replacement list of the macro.
     Those lexmarks are already normalized via @(tsee normalize-macro-arg).")
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
     we replace with the non-punctuator @('###'),
     which, in @(tsee evaluate-triple-hash),
     we use to evaluate the @('##') operator:
     this is needed to distinguish, after replacement,
     the @('##') that were in the macro's replacement list
     (which we change into @('###')),
     from the ones that occur in arguments,
     which must not be evaluated [C17:6.10.3.3/3].
     Another approach is to evaluate @('##') in this ACL2 function,
     but because of the possible presence of markers,
     this would make the code more complicated
     than doing a separate pass to evaluate the @('##') operators
     that (temporarily) appear as @('###').")
   (xdoc::p
    "A complication arises from the treatment of parameters adjacent to @('##'),
     which are replaced with the tokens of the corresponding arguments,
     which may be zero or more.
     If zero, they are treated like placemarkers [C17:6.10.3.3].
     We represent placemarkers as @('nil'),
     which is why this function returns a list of optional lexmarks.
     In @(tsee evaluate-triple-hash),
     we eliminate all the @('nil') placemarkers,
     according to [C17:6.10.3.3].
     Although placemarkers only play a role when adjacent to @('##'),
     for simplicity we put them everywhere an argument of the macro is empty,
     and @(tsee evaluate-triple-hash) simply discards
     the ones not adjacent to @('###')."))
  (b* (((when (endp replist)) nil)
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
                                   (ident-lexmark-list-alist-fix subst)))
           ((unless param+arg)
            (raise "Internal error: # is followed by a non-parameter ~x0."
                   param))
           (arg (cdr param+arg))
           ;; Combine # and ARG into TOKEN.
           ((mv stringlit markers) (stringize arg))
           (token (plexeme-string stringlit))
           (lexmark (make-lexmark-lexeme :lexeme token :span (irr-span))))
        (append (space-lexmark-singleton? spacep)
                (list lexmark) ; string literal
                markers ; markers collected from the operand of #
                (replace-macro-args replist subst))))
     ((plexeme-hashhashp token) ; ##
      (append (space-lexmark-singleton? spacep)
              ;; Replace ## with ### -- see doc above.
              (list (make-lexmark-lexeme :lexeme (plexeme-punctuator "###")
                                         :span (irr-span)))
              (replace-macro-args replist subst)))
     ((plexeme-case token :ident) ; ident (param or not)
      (b* ((ident (plexeme-ident->ident token))
           (ident+arg (assoc-equal ident (ident-lexmark-list-alist-fix subst)))
           ;; If the token is an identifier but not a parameter,
           ;; it remains unchanged.
           ((when (not ident+arg))
            (append (space-lexmark-singleton? spacep)
                    (list (make-lexmark-lexeme :lexeme token
                                               :span (irr-span)))
                    (replace-macro-args replist subst)))
           ;; If the token is a parameter,
           ;; consider its correspoding argument ARG.
           ;; If it is empty, we add NIL to the output list (see doc above);
           ;; if it is not empty, we add its lexmarks to the output list.
           (arg (cdr ident+arg)))
        (append (space-lexmark-singleton? spacep)
                (or arg (list nil))
                (replace-macro-args replist subst))))
     (t ; other token
      ;; This case is the same as that above
      ;; of an identifier that is not a parameter.
      (append (space-lexmark-singleton? spacep)
              (list (make-lexmark-lexeme :lexeme token
                                         :span (irr-span)))
              (replace-macro-args replist subst)))))
     :no-function nil
     :measure (len replist)
     :guard-hints
     (("Goal" :in-theory (enable
                          alistp-when-ident-lexmark-list-alistp-rewrite
                          true-listp-when-lexmark-listp)))
     :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-first-token/placemarker
  ((lexmarks/placemarkers lexmark-option-listp))
  :returns (mv (foundp booleanp)
               (token/placemarker plexeme-optionp)
               (markers lexmark-listp)
               (lexmarks/placemarkers-rest lexmark-option-listp))
  :short "Find the first token or placemarker, if any,
          in a list of lexmarks and placemarkers."
  :long
  (xdoc::topstring
   (xdoc::p
    "If not found, the first result is @('nil'),
     and so are the (irrelevant) second, third, and fourth results.
     If found, the first result is @('t'),
     the second result is the token or placemarker
     (the latter represented as @('nil')),
     the third result are the markers found along the way,
     and the fourth result are the remaining lexmarks and placemarkers.
     Spaces found along the way are ignored,
     because we use this to find the token concatenation operator
     and its second operand, after having the first operand,
     and thus all those spaces are absorbed into token concatenation."))
  (b* (((when (endp lexmarks/placemarkers)) (mv nil nil nil nil))
       (lexmark/placemarker (car lexmarks/placemarkers))
       ((when (not lexmark/placemarker)) ; placemarker
        (mv t nil nil (lexmark-option-list-fix (cdr lexmarks/placemarkers))))
       (lexmark lexmark/placemarker)
       ((when (not (lexmark-case lexmark :lexeme))) ; marker
        (b* ((marker (lexmark-fix lexmark))
             ((mv foundp token/placemarker markers lexmarks/placemarkers-rest)
              (find-first-token/placemarker (cdr lexmarks/placemarkers))))
          (if foundp
              (mv foundp
                  token/placemarker
                  (cons marker markers)
                  lexmarks/placemarkers-rest)
            (mv nil nil nil nil))))
       (lexeme (lexmark-lexeme->lexeme lexmark))
       ((when (plexeme-tokenp lexeme))
        (mv t lexeme nil
            (lexmark-option-list-fix (cdr lexmarks/placemarkers)))))
    (find-first-token/placemarker (cdr lexmarks/placemarkers)))
  :prepwork ((local (in-theory (enable lexmark-option-fix))))

  ///

  (more-returns
   (lexmarks/placemarkers-rest lexmark-listp
                               :hyp (lexmark-listp lexmarks/placemarkers)
                               :hints (("Goal" :induct t))))

  (defret plexeme-tokenp-of-find-first-token/placemarker
    (implies token/placemarker
             (plexeme-tokenp token/placemarker))
    :hints (("Goal" :induct t)))

  (defret len-of-find-first-token/placemarker-uncond
    (<= (len lexmarks/placemarkers-rest)
        (len lexmarks/placemarkers))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret len-of-find-first-token/placemarker-cond
    (implies foundp
             (< (len lexmarks/placemarkers-rest)
                (len lexmarks/placemarkers)))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evaluate-triple-hash ((lexmarks/placemarkers lexmark-option-listp)
                              (version c::versionp))
  :returns (mv erp (lexmarks lexmark-listp))
  :short "Evaluate the @('##') operator, represented as @('###'),
          in the list produced by @(tsee replace-macro-args)."
  :long
  (xdoc::topstring
   (xdoc::p
    "See the documentation of @(tsee replace-macro-args) for context.")
   (xdoc::p
    "We go through the list of lexmarks and placemarkers.
     When we encounter a marker or a space, we just pass it on.
     When we encounter a token or placemarker, we check whether
     it is followed by a @('###'):
     in this case, the token or placemarker
     is the left operand of token concatenation,
     so we must find the token or placemarker after the @('###').
     We concatenate the two tokens/placemarkers.
     However, there may be another @('###') following,
     meaning that the result of the first concatenation
     is in fact the left operand of another concatenation.
     Thus, we use a recursive auxiliary function
     to find all the @('###') operators,
     so that we can concatenate all the operands together.
     Any markers found within the concatenation(s)
     are put just after the result.
     [C17:6.10.3.2/2] says that the order of evaluation of @('##')
     (here represented as @('###')), as well as of @('#') is unspecified;
     our implementation associates @('###') to the left.
     The companion recursive function just returns the token
     if it is not followed by @('###').
     In any case, the result of the companion recursive function
     is a token or placemarker:
     we discard it if it is a placemarker,
     otherwise (i.e. if it is a token) we pass it on.
     We treat @('##') like any other token,
     because this must come from some macro argument,
     and thus it is not treated as the concatenation operator:
     this is why @(tsee replace-macro-args) uses @('###')
     to distinguish the original @('##') in the macro's replacement list,
     which are the actual concatenation operators."))
  (b* (((reterr) nil)
       ((when (endp lexmarks/placemarkers)) (retok nil))
       (lexmark/placemarker (car lexmarks/placemarkers))
       (lexmarks/placemarkers (cdr lexmarks/placemarkers))
       ;; If the next lexmark or placemarker is a marker or a space,
       ;; pass it on, i.e. continue processing and add it to the output.
       ((when (and lexmark/placemarker
                   (or (lexmark-case lexmark/placemarker :start)
                       (lexmark-case lexmark/placemarker :end)
                       (not (plexeme-tokenp ; i.e. space
                             (lexmark-lexeme->lexeme lexmark/placemarker))))))
        (b* (((erp lexmarks) (evaluate-triple-hash lexmarks/placemarkers
                                                   version)))
          (retok (cons (lexmark-fix lexmark/placemarker) lexmarks))))
       ;; Otherwise, the next lexmark or placemarker
       ;; is either a token or a placemarker.
       ;; Call the recursive companion function to concatenate it
       ;; with any subsequent token with ### in between.
       ((erp token/placemarker markers lexmarks/placemarkers)
        (evaluate-triple-hash-aux (and lexmark/placemarker
                                       (lexmark-lexeme->lexeme
                                        lexmark/placemarker))
                                  nil
                                  lexmarks/placemarkers
                                  version))
       ;; Process the rest of the lexmarks and placemarkers.
       ((erp lexmarks) (evaluate-triple-hash lexmarks/placemarkers version)))
    ;; Add the token from the recursive companion function to the output,
    ;; or otherwise discard the placemarker.
    ;; Also add any markers in between any ### operations.
    (retok (append (and token/placemarker
                        (list (make-lexmark-lexeme :lexeme token/placemarker
                                                   :span (irr-span))))
                   markers
                   lexmarks)))
  :measure (len lexmarks/placemarkers)
  :guard-hints (("Goal" :in-theory (enable true-listp-when-lexmark-listp)))
  :hooks nil

  :prepwork
  ((define evaluate-triple-hash-aux
     ((token/placemarker plexeme-optionp)
      (markers lexmark-listp)
      (lexmarks/placemarkers lexmark-option-listp)
      (version c::versionp))
     :guard (or (not token/placemarker)
                (plexeme-tokenp token/placemarker))
     :returns (mv erp
                  (new-token/placemarker plexeme-optionp)
                  (new-markers lexmark-listp)
                  (new-lexmarks/placemarkers lexmark-option-listp))
     :parents nil
     (b* (((reterr) nil nil nil)
          ;; Find the next token or placemarker, if any.
          ((mv foundp triplehash? markers1 lexmarks/placemarkers-rest)
           (find-first-token/placemarker lexmarks/placemarkers))
          ;; If there is no next token or placemarker,
          ;; or it is not a ### token,
          ;; then return the input token or placemarker unchanged,
          ;; and also the list of lexmarks and placemarker unchanged;
          ;; and also the markers found so far unchanged.
          ((unless (and foundp
                        triplehash?
                        (plexeme-punctuatorp triplehash? "###")))
           (retok (plexeme-option-fix token/placemarker)
                  (lexmark-list-fix markers)
                  (lexmark-option-list-fix lexmarks/placemarkers)))
          ;; Otherwise, there is a ###,
          ;; so we must find another token or placemarker.
          (lexmarks/placemarkers lexmarks/placemarkers-rest)
          ((mv foundp next-token/placemarker markers2 lexmarks/placemarkers)
           (find-first-token/placemarker lexmarks/placemarkers))
          ((unless foundp)
           (raise "Internal error: ~
                   concatenation operator ## found ~
                   at the end of a macro replacement list.")
           (reterr t))
          ;; Combine the next token or placemarker with the input one.
          ((erp token/placemarker)
           (concatenate-tokens/placemarkers token/placemarker
                                            next-token/placemarker
                                            version))
          ;; Join all the markers.
          (markers (append markers markers1 markers2)))
       ;; Recursively combine the new token or placemarker
       ;; with any subsequent ones if there are more ### operators.
       (evaluate-triple-hash-aux token/placemarker
                                 markers
                                 lexmarks/placemarkers
                                 version))
     :no-function nil
     :measure (len lexmarks/placemarkers)
     :guard-hints (("Goal" :in-theory (enable true-listp-when-lexmark-listp)))

     ///

     (defret len-of-evaluate-triple-hash-aux
       (<= (len new-lexmarks/placemarkers)
           (len lexmarks/placemarkers))
       :rule-classes :linear
       :hints (("Goal" :induct t))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evaluate-double-hash ((lexemes plexeme-listp) (version c::versionp))
  :returns (mv erp (new-lexemes plexeme-listp))
  :short "Evaluate the @('##') operator in
          the replacement list of an object-like macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee evaluate-triple-hash),
     but it does not deal with placemarkers and markers,
     because it is used on the replacement list of an object like macro,
     which consists of lexemes.
     Here the @('##') is represented as itself, not as @('###').")
   (xdoc::p
    "Since the replacement list of an object like macro
     consists of tokens with some single spaces between tokens,
     we use simpler code than @(tsee find-first-token/placemarker)
     to find whether the lexeme that we are examining
     is followed by @('##'), possibly with a space before it,
     and also to obtain the lexeme at the right of @('##')."))
  (b* (((reterr) nil)
       ((when (endp lexemes)) (retok nil))
       (lexeme (car lexemes))
       (lexemes (cdr lexemes))
       ;; If the next lexeme is a space,
       ;; pass it on, i.e. continue processing and add it to the output.
       ((when (not (plexeme-tokenp lexeme))) ; i.e. space
        (b* (((erp lexemes) (evaluate-double-hash lexemes version)))
          (retok (cons (plexeme-fix lexeme) lexemes))))
       ;; Otherwise, the next lexeme is a token.
       ;; Call the recursive companion function to concatenate it
       ;; with any subsequent token with ## in between.
       ((erp token lexemes) (evaluate-double-hash-aux lexeme lexemes version))
       ;; Process the rest of the lexemes.
       ((erp lexemes) (evaluate-double-hash lexemes version)))
    ;; Add the token from the recursive companion function to the output.
    (retok (cons token lexemes)))
  :measure (len lexemes)
  :hooks nil

  :prepwork
  ((define evaluate-double-hash-aux ((token plexemep)
                                     (lexemes plexeme-listp)
                                     (version c::versionp))
     :guard (plexeme-tokenp token)
     :returns (mv erp
                  (new-token plexemep)
                  (new-lexemes plexeme-listp))
     :parents nil
     (b* (((reterr) (irr-plexeme) nil)
          ;; Find the next token, if any.
          ((mv foundp lexemes-rest)
           (if (endp lexemes)
               (mv nil nil)
             (if (plexeme-punctuatorp (car lexemes) "##")
                 (mv t (cdr lexemes))
               (if (and (plexeme-case (car lexemes) :spaces)
                        (consp (cdr lexemes))
                        (plexeme-punctuatorp (cadr lexemes) "##"))
                   (mv t (cddr lexemes))
                 (mv nil nil)))))
          ;; If there is no next token, or it is not ##,
          ;; return the token unchanged,
          ;; and also the list of lexemes unchanged.
          ((when (not foundp))
           (retok (plexeme-fix token) (plexeme-list-fix lexemes)))
          ;; Otherwise, there is a ##, so we must find another token.
          (lexemes lexemes-rest)
          ((mv foundp next-token lexemes)
           (if (endp lexemes)
               (mv nil (irr-plexeme) nil)
             (if (plexeme-tokenp (car lexemes))
                 (mv t (car lexemes) (cdr lexemes))
               (if (and (plexeme-case (car lexemes) :spaces)
                        (consp (cdr lexemes))
                        (plexeme-tokenp (cadr lexemes)))
                   (mv t (cadr lexemes) (cddr lexemes))
                 (mv nil (irr-plexeme) nil)))))
          ((unless foundp)
           (raise "Internal error: ~
                   concatenation operator ## found ~
                   at the end of a macro replacement list.")
           (reterr t))
          ;; Combine the next token with the input one.
          ((erp token)
           (concatenate-tokens/placemarkers token next-token version)))
       ;; Recursively combine the new token
       ;; with any subsequent ones if there are more ## operators.
       (evaluate-double-hash-aux token lexemes version))
     :no-function nil
     :measure (len lexemes)
     :hooks nil

     ///

     (defret len-of-evaluate-double-hash-aux
       (<= (len new-lexemes)
           (len lexemes))
       :rule-classes :linear
       :hints (("Goal" :induct t))))))

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
     returning the resulting lexmarks:
     these lexmarks are all lexemes unless
     the function is applied to macro arguments,
     for which we need to retain the markers,
     which are eliminated when the expanded call is rescanned.
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
     their replacement lists are added in front of the input lexmarks,
     making the input larger.
     The termination argument should rely on the fact that
     macros are not recursively expanded,
     and thus, when a macro is expanded,
     it can contribute to decreasing a suitable measure."))

  (define pproc-lexemes ((mode macrep-modep)
                         (rev-lexmarks lexmark-listp)
                         (paren-level natp)
                         (no-expandp booleanp)
                         (disabled ident-listp)
                         (directivep booleanp)
                         (ppstate ppstatep)
                         (limit natp))
    :returns (mv erp
                 (new-rev-lexmarks lexmark-listp)
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
      "This function takes and returns the lexmarks generated so far,
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
      "This function starts by reading the next lexmark,
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
       That multiset is discusssed in @(tsee pproc-lexemes/macroargs).
       In any of the @(':arg-...') modes,
       the marker is also added to the reversed list of lexmarks,
       because markers in arguments must be retained.")
     (xdoc::p
      "If tne next lexmark is a new line,
       it is always added to the reversed lexmarks.
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
       in this case, we do not add the comma to the reversed lexmarks,
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
       we add it to the list of reversed lexmarks and we continue preprocessing.
       We increment the parenthesis level if we are in an @(':arg-...') mode.")
     (xdoc::p
      "If the next lexmark is a closed parenthesis,
       it is the stopping criterion for
       the @(':arg-last') and @(':arg-dots') modes,
       but only if the parenthesis level is 0;
       in this case, we do not add the parenthesis to the reversed lexmarks,
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
       It is important that we leave the argument identifier as is,
       so that it can be parsed as part of the expression;
       in recognizing the identifier, we check that the syntax is correct.")
     (xdoc::p
      "If the next lexmark is an identifier different from @('defined'),
       or if we are not in the @(':expr') mode,
       then we look up the identifier in the macro table,
       unless it is in the disabled multiset,
       and unless macro expansion is inhibited.
       If it is not found in the macro table,
       it is just added to the reversed lexmarks,
       and we continue preprocessing.
       If we find an object-like macro,
       we leave the reversed lexmarks unchanged,
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
                         (if (member-eq (macrep-mode-kind mode)
                                        '(:arg-nonlast :arg-last :arg-dots))
                             (cons lexmark rev-lexmarks)
                           rev-lexmarks)
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
                         (if (member-eq (macrep-mode-kind mode)
                                        '(:arg-nonlast :arg-last :arg-dots))
                             (cons lexmark rev-lexmarks)
                           rev-lexmarks)
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
               (retok (cons lexmark (lexmark-list-fix rev-lexmarks))
                      ppstate))
              ((:arg-nonlast :arg-last :arg-dots)
               (if directivep
                   (reterr-msg :where (position-to-msg (span->start span))
                               :expected "the completion of a macro call"
                               :found "new line (which ends the directive)")
                 (pproc-lexemes mode
                                (cons lexmark rev-lexmarks)
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
                   (retok (lexmark-list-fix rev-lexmarks)
                          ppstate))
                  ((and (macrep-mode-case mode :arg-last)
                        (zp paren-level))
                   (reterr-msg :where (position-to-msg (span->start span))
                               :expected "a closed parenthesis"
                               :found "a comma"))
                  (t (pproc-lexemes mode
                                    (cons lexmark rev-lexmarks)
                                    paren-level
                                    no-expandp
                                    disabled
                                    directivep
                                    ppstate
                                    (1- limit)))))
           ((plexeme-punctuatorp lexeme "(") ; (
            (pproc-lexemes mode
                           (cons lexmark rev-lexmarks)
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
                              (cons lexmark rev-lexmarks)
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
                                (cons lexmark rev-lexmarks)
                                (1- paren-level)
                                no-expandp
                                disabled
                                directivep
                                ppstate
                                (1- limit))))
              ((:arg-last :arg-dots)
               (if (zp paren-level)
                   (retok (lexmark-list-fix rev-lexmarks)
                          ppstate)
                 (pproc-lexemes mode
                                (cons lexmark rev-lexmarks)
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
                  (b* (((erp lexmarks disabled ppstate)
                        (b* (((reterr) nil nil ppstate)
                             ((erp token2 span2 disabled ppstate)
                              (read-token-handling-markers directivep
                                                           disabled
                                                           ppstate)))
                          (cond
                           ((plexeme-case token2 :ident) ; defined ident
                            (retok (list (make-lexmark-lexeme :lexeme token2
                                                              :span (irr-span)))
                                   disabled
                                   ppstate))
                           ((plexeme-punctuatorp token2 "(") ; defined (
                            (b* (((erp token3 span3 disabled ppstate)
                                  (read-token-handling-markers directivep
                                                               disabled
                                                               ppstate))
                                 ((unless (plexeme-case token3 :ident))
                                  ;; defined ( ident
                                  (reterr-msg :where (position-to-msg
                                                      (span->start span3))
                                              :expected "an identifier"
                                              :found (plexeme-to-msg token3)))
                                 ((erp token4 span4 disabled ppstate)
                                  (read-token-handling-markers directivep
                                                               disabled
                                                               ppstate))
                                 ((unless (plexeme-punctuatorp token4 ")"))
                                  ;; defined ( ident )
                                  (reterr-msg :where (position-to-msg
                                                      (span->start span4))
                                              :expected "a right parenthesis"
                                              :found (plexeme-to-msg token4))))
                              (retok (list (make-lexmark-lexeme
                                            :lexeme token2
                                            :span (irr-span))
                                           (make-lexmark-lexeme
                                            :lexeme token3
                                            :span (irr-span))
                                           (make-lexmark-lexeme
                                            :lexeme token4
                                            :span (irr-span)))
                                     disabled
                                     ppstate)))
                           (t ; defined EOF-or-not-ident-and-not-(
                            (reterr-msg :where (position-to-msg
                                                (span->start span2))
                                        :expected "an identifier or ~
                                                   a left parenthesis"
                                        :found (plexeme-to-msg token2)))))))
                    (pproc-lexemes mode
                                   (revappend lexmarks
                                              (cons (make-lexmark-lexeme
                                                     :lexeme (plexeme-ident
                                                              (ident "defined"))
                                                     :span (irr-span))
                                                    rev-lexmarks))
                                   paren-level
                                   no-expandp
                                   disabled
                                   directivep
                                   ppstate
                                   (1- limit))))
                 ((when (or no-expandp
                            (member-equal ident (ident-list-fix disabled))))
                  (pproc-lexemes mode
                                 (cons lexmark rev-lexmarks)
                                 paren-level
                                 no-expandp
                                 disabled
                                 directivep
                                 ppstate
                                 (1- limit)))
                 (info (macro-lookup ident (ppstate->macros ppstate)))
                 ((unless info)
                  (pproc-lexemes mode
                                 (cons lexmark rev-lexmarks)
                                 paren-level
                                 no-expandp
                                 disabled
                                 directivep
                                 ppstate
                                 (1- limit))))
              (macro-info-case
               info
               :object
               (b* (((erp replist) (evaluate-double-hash info.replist
                                                         (ienv->version
                                                          (ppstate->ienv
                                                           ppstate))))
                    (ppstate (push-lexmark (lexmark-end ident) ppstate))
                    (ppstate (push-lexemes replist ppstate))
                    (ppstate (push-lexmark (lexmark-start ident) ppstate)))
                 (pproc-lexemes mode
                                rev-lexmarks
                                paren-level
                                no-expandp
                                disabled
                                directivep
                                ppstate
                                (1- limit)))
               :function
               (b* (((erp toknl ppstate)
                     (peek-token/newline directivep ppstate))
                    ((unless (and toknl
                                  (plexeme-punctuatorp toknl "(")))
                     (pproc-lexemes mode
                                    (cons lexmark rev-lexmarks)
                                    paren-level
                                    no-expandp
                                    disabled
                                    directivep
                                    ppstate
                                    (1- limit)))
                    ((erp token span2 disabled ppstate)
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
                             (retok nil ; subst
                                    disabled
                                    ppstate))
                         (b* (((erp subst ppstate)
                               (pproc-macro-args info.params
                                                 info.ellipsis
                                                 info.hash-params
                                                 disabled
                                                 directivep
                                                 ppstate
                                                 (1- limit))))
                           (retok subst disabled ppstate)))))
                    (replist (replace-macro-args info.replist subst))
                    ((erp replist) (evaluate-triple-hash replist
                                                         (ienv->version
                                                          (ppstate->ienv
                                                           ppstate))))
                    (ppstate (push-lexmark (lexmark-end ident) ppstate))
                    (ppstate (push-lexmarks replist ppstate))
                    (ppstate (push-lexmark (lexmark-start ident) ppstate)))
                 (pproc-lexemes mode
                                rev-lexmarks
                                paren-level
                                no-expandp
                                disabled
                                directivep
                                ppstate
                                (1- limit))))))
           (t ; other lexeme
            (pproc-lexemes mode
                           (cons lexmark rev-lexmarks)
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
                 (subst ident-lexmark-list-alistp)
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
                                   nil ; rev-lexmarks
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
            (retok nil ; subst
                   ppstate)))
         (param (ident-fix (car params)))
         (mode (if (or (consp (cdr params))
                       ellipsis)
                   (macrep-mode-arg-nonlast)
                 (macrep-mode-arg-dots)))
         (no-expandp (and (member-equal param (ident-list-fix hash-params)) t))
         ((erp rev-arg ppstate)
          (pproc-lexemes mode
                         nil ; rev-lexmarks
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
  (("Goal" :in-theory (enable ifix
                              true-listp-when-ident-listp
                              alistp-when-ident-lexmark-list-alistp-rewrite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pproc-const-expr ((ppstate ppstatep))
  :returns (mv erp
               (expr pexprp)
               (result booleanp)
               (new-ppstate ppstatep))
  :short "Preprocess a constant expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called just after reading a @('#if') or @('#elif'),
     which, according to the grammar,
     must be followed by a constant expression [C17:6.10/1],
     which takes the rest of the line of the directive.")
   (xdoc::p
    "We use @(tsee pproc-lexemes), in the @(':expr') mode,
     to read the lexemes that form the constant expression;
     that function consumes (and returns) the final new line.
     The resulting lexmarks are all lexemes;
     since currently we do not have that fact statically available,
     we double-check it here and throw a hard error in case the check fails.
     The lexemes are reversed back to their order of occurrence.")
   (xdoc::p
    "Then we must parse and evaluate those lexemes, obtaining a boolean,
     which this function returns as the value of the expression.
     We also return the expression itself,
     so that we can incorporate that into the @(tsee pfile)."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) (irr-pexpr) nil ppstate)
       ((erp rev-lexmarks ppstate)
        (pproc-lexemes (macrep-mode-expr)
                       nil ; rev-lexmarks
                       0 ; paren-level
                       nil ; no-expandp
                       nil ; disabled
                       t ; directivep
                       ppstate
                       1000000000)) ; limit
       ((unless (lexmark-list-case-lexeme-p rev-lexmarks))
        (raise "Internal error: ~x0 contains markers.")
        (reterr t))
       (rev-lexemes (lexmark-list-to-lexeme-list rev-lexmarks))
       (lexemes (rev rev-lexemes))
       ((erp expr) (pparse-const-expr lexemes))
       ((erp pval) (peval-expr expr
                               (ppstate->macros ppstate)
                               (ppstate->ienv ppstate)))
       (result (not (= (pvalue->integer pval) 0))))
    (retok expr result ppstate))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define skip-to-end-of-line ((ppstate ppstatep))
  :returns (mv erp (new-ppstate ppstatep))
  :short "Skip lexemes up to (including) the next new line."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when preprocessing
     code in @('if-section')s that is skipped.")
   (xdoc::p
    "We read lexemes until we read a new line.
     All the lexemes are discarded.
     It is an error if we reach end of file.")
   (xdoc::p
    "We set the @('headerp') flag to @('nil') when reading the next lexeme.
     This is only called on lexemes
     that do not immediately follow a @('#include');
     lexemes immediately following a @('#include') are handled elsewhere."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) ppstate)
       ((erp lexeme span ppstate) (read-lexeme nil ppstate))
       ((unless lexeme)
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a lexeme"
                    :found "end of file"))
       ((when (plexeme-case lexeme :newline)) (retok ppstate)))
    (skip-to-end-of-line ppstate))
  :no-function nil
  :measure (ppstate->size ppstate)

  ///

  (defret ppstate->size-of-skip-to-end-of-line-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-skip-to-end-of-line-cond
    (implies (not erp)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pproc-groups-skipped
  :short "Preprocess skipped groups."
  :long
  (xdoc::topstring
   (xdoc::p
    "In an @('if-section') [C17:6.10.1],
     at most one optional group (i.e. zero or more group parts)
     becomes, after preprocessing, part of the code.
     The other optional groups are skipped,
     but we still need to go through them to find where they end,
     without being confused by possible nested @('if-section')s
     [C17:6.10.1/6].")
   (xdoc::p
    "The functions in this clique are similar in structure to
     (some of) the ones in the @(tsee pproc-files/groups/etc) clique,
     but they discard all the lexemes,
     they do not perform macro replacement,
     and they do not execute the directives.
     See the documentation of @(tsee pproc-files/groups/etc)."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-*-group-part-skipped ((ppstate ppstatep))
    :returns (mv erp
                 (groupend groupendp)
                 (new-ppstate ppstatep))
    :parents (preprocessor pproc-groups-skipped)
    :short "Preprocess zero or more group parts to be skipped."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is similar to @(tsee pproc-*-group-part) in structure:
       see that function's documentation."))
    (b* ((ppstate (ppstate-fix ppstate))
         ((reterr) (irr-groupend) ppstate)
         (psize (ppstate->size ppstate))
         ((erp groupend? ppstate) (pproc-?-group-part-skipped ppstate))
         ((when groupend?) (retok groupend? ppstate))
         ((unless (mbt (<= (ppstate->size ppstate) (1- psize))))
          (reterr :impossible)))
      (pproc-*-group-part-skipped ppstate))
    :measure (two-nats-measure (ppstate->size ppstate)
                               1)) ; > pproc-?-group-part-skipped

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-?-group-part-skipped ((ppstate ppstatep))
    :returns (mv erp
                 (groupend? groupend-optionp)
                 (new-ppstate ppstatep))
    :parents (preprocessor pproc-groups-skipped)
    :short "Preprocess a group part to be skipped, if present."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is similar to @(tsee pproc-?-group-part) in structure:
       see that function's documentation.")
     (xdoc::p
      "We treat @('#if'), @('#ifdef'), and @('#ifndef') identically,
       since we are not actually executing the directives.
       After going through the first line,
       we call a separate function in the clique to handle the rest.
       Note that these are nested inside the outer conditional
       part of whose code we are preprocessing/skipping;
       we need to follow the structure of the nested conditionals
       to see where they end, without confusing their ending
       with the ending of the outer conditional.")
     (xdoc::p
      "Just after a @('#include'),
       we read the next token or new line trying to recognize header names;
       after that, we skip the rest of the line,
       regardless of whether we found a header name or anything else.
       We also accept @('#include') followed by no tokens,
       since this is skipped code anyhow.")
     (xdoc::p
      "We treat
       @('#define'), @('#undef'), @('#line'), @('#error') and @('#pragma')
       identically, by skipping through the next end of line.
       We also treat @('#warning') in the same way
       if the C standard version is C23 [C23:6.10.1]
       or if GCC or Clang extensions are enabled."))
    (b* ((ppstate (ppstate-fix ppstate))
         ((reterr) nil ppstate)
         ((erp nontoknls toknl span ppstate) (read-token/newline ppstate)))
      (cond
       ((not toknl) ; EOF
        (if nontoknls
            (reterr-msg :where (position-to-msg (span->start span))
                        :expected "new line"
                        :found (plexeme-to-msg toknl))
          (retok (groupend-eof) ppstate)))
       ((plexeme-hashp toknl) ; #
        (b* (((erp & toknl2 span2 ppstate) (read-token/newline ppstate)))
          (cond
           ((not toknl2) ; # EOF
            (reterr-msg :where (position-to-msg (span->start span2))
                        :expected "a token or new line"
                        :found (plexeme-to-msg toknl2)))
           ((plexeme-case toknl2 :newline) ; # EOF -- null directive
            (retok nil ppstate))
           ((plexeme-case toknl2 :ident) ; # ident
            (b* ((directive (ident->unwrap (plexeme-ident->ident toknl2))))
              (cond
               ((equal directive "elif") ; # elif
                (retok (groupend-elif) ppstate))
               ((equal directive "else") ; # else
                (retok (groupend-else) ppstate))
               ((equal directive "endif") ; # endif
                (retok (groupend-endif) ppstate))
               ((or (equal directive "if") ; # if
                    (equal directive "ifdef") ; # ifdef
                    (equal directive "ifndef")) ; # ifndef
                (b* (((erp ppstate) ; # if/ifdef/ifndef ... EOL
                      (skip-to-end-of-line ppstate))
                     (psize (ppstate->size ppstate))
                     ((erp ppstate)
                      (pproc-if/ifdef/ifndef-rest-skipped ppstate))
                     ((unless (mbt (<= (ppstate->size ppstate) (1- psize))))
                      (reterr :impossible)))
                  (retok nil ppstate)))
               ((equal directive "include") ; # include
                (b* (((erp & toknl3 span3 ppstate)
                      (read-token/newline-after-include ppstate))
                     ((unless toknl3) ; # include EOF
                      (reterr-msg :where (position-to-msg (span->start span3))
                                  :expected "a token or new line"
                                  :found (plexeme-to-msg toknl3)))
                     ((when (plexeme-case toknl3 :newline)) ; # include EOL
                      (retok nil ppstate))
                     ((erp ppstate) ; # include ... EOL
                      (skip-to-end-of-line ppstate)))
                  (retok nil ppstate)))
               ((or (equal directive "define") ; # define
                    (equal directive "undef") ; # undef
                    (equal directive "line") ; # line
                    (equal directive "error") ; # error
                    (and (equal directive "warning") ; # warning
                         (b* ((ienv (ppstate->ienv ppstate)))
                           (or (= (ienv->std ienv) 23)
                               (ienv->gcc/clang ienv))))
                    (equal directive "pragma")) ; # pragma
                (b* (((erp ppstate) ; # ... EOL
                      (skip-to-end-of-line ppstate)))
                  (retok nil ppstate)))
               (t ; # other -- non-directive
                (b* (((erp ppstate) ; # ... EOL
                      (skip-to-end-of-line ppstate)))
                  (retok nil ppstate))))))
           (t ; # non-ident -- non-directive
            (b* (((erp ppstate) ; # ... EOL
                  (skip-to-end-of-line ppstate)))
              (retok nil ppstate))))))
       (t ; non-# -- text line
        (if (plexeme-case toknl :newline) ; EOL
            (retok nil ppstate)
          (b* (((erp ppstate) ; ... EOL
                (skip-to-end-of-line ppstate)))
            (retok nil ppstate))))))
    :no-function nil
    :measure (two-nats-measure (ppstate->size ppstate)
                               0)) ; < pproc-*-group-part-skipped

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-if/ifdef/ifndef-rest-skipped ((ppstate ppstatep))
    :returns (mv erp (new-ppstate ppstatep))
    :parents (preprocessor pproc-groups-skipped)
    :short "Preprocess the rest of
            a @('#if'), @('#ifdef'), or @('#ifndef') section to be skipped."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is similar to @(tsee pproc-if/ifdef/ifndef-rest) in structure;
       see that function's documentation."))
    (b* ((ppstate (ppstate-fix ppstate))
         ((reterr) ppstate)
         (psize (ppstate->size ppstate))
         ((erp groupend ppstate) (pproc-*-group-part-skipped ppstate))
         ((when (groupend-case groupend :eof))
          (reterr-msg :where (position-to-msg (ppstate->position ppstate))
                      :expected "a #elif or ~
                                 a #else or ~
                                 a #endif"
                      :found "end of file"))
         ((unless (mbt (<= (ppstate->size ppstate) (1- psize))))
          (reterr :impossible))
         ((erp ppstate) ; #elif/else/endif ... EOL
          (skip-to-end-of-line ppstate))
         ((when (groupend-case groupend :else))
          (b* (((erp groupend ppstate) (pproc-*-group-part-skipped ppstate))
               ((unless (groupend-case groupend :endif))
                (reterr-msg :where (position-to-msg (ppstate->position ppstate))
                            :expected "a #endif"
                            :found (case (groupend-kind groupend)
                                     (:eof "end of file")
                                     (:elif "a #elif")
                                     (:else "a #else")))))
            (skip-to-end-of-line ppstate)))
         ((when (groupend-case groupend :endif))
          (retok ppstate)))
      ;; (groupend-case groupend :elif)
      (pproc-if/ifdef/ifndef-rest-skipped ppstate))
    :no-function nil
    :measure (two-nats-measure (ppstate->size ppstate)
                               2)) ; > pproc-*-group-part-skipped

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual ppstate->size-of-pproc-groups-skipped-uncond
    (defret ppstate->size-of-pproc-*-group-part-skipped-uncond
      (<= (ppstate->size new-ppstate)
          (ppstate->size ppstate))
      :fn pproc-*-group-part-skipped
      :rule-classes :linear)
    (defret ppstate->size-of-pproc-?-group-part-skipped-uncond
      (<= (ppstate->size new-ppstate)
          (ppstate->size ppstate))
      :fn pproc-?-group-part-skipped
      :rule-classes :linear)
    (defret ppstate->size-of-pproc-if/ifdef/ifndef-rest-skipped-uncond
      (<= (ppstate->size new-ppstate)
          (ppstate->size ppstate))
      :fn pproc-if/ifdef/ifndef-rest-skipped
      :rule-classes :linear))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual ppstate->size-of-pproc-groups-skipped-cond
    (defret ppstate->size-of-pproc-*-group-part-skipped-cond
      (implies (and (not erp)
                    (not (groupend-case groupend :eof)))
               (<= (ppstate->size new-ppstate)
                   (1- (ppstate->size ppstate))))
      :fn pproc-*-group-part-skipped
      :rule-classes :linear)
    (defret ppstate->size-of-pproc-?-group-part-skipped-cond
      (implies (and (not erp)
                    (or (not groupend?)
                        (not (groupend-case groupend? :eof))))
               (<= (ppstate->size new-ppstate)
                   (1- (ppstate->size ppstate))))
      :fn pproc-?-group-part-skipped
      :rule-classes :linear)
    (defret ppstate->size-of-pproc-if/ifdef/ifndef-rest-skipped-cond
      (implies (not erp)
               (<= (ppstate->size new-ppstate)
                   (1- (ppstate->size ppstate))))
      :fn pproc-if/ifdef/ifndef-rest-skipped
      :rule-classes :linear))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards pproc-*-group-part-skipped))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define s-char-list-to-q-char-list ((schars s-char-listp))
  :returns (mv erp (qchars q-char-listp))
  :short "Convert a list of @(tsee s-char)s to a list of @(tsee q-char)s."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when attempting to convert a string literal
     to a double-quote header name, in @(tsee indirect-header-name).
     We ensure that there are no escapes.
     For now there are no restrictions on the ASTs,
     so every @(tsee s-char) code can be used as a @(tsee q-char) code."))
  (b* (((reterr) nil)
       ((when (endp schars)) (retok nil))
       (schar (car schars))
       ((when (s-char-case schar :escape))
        (reterr (msg "Cannot have escape ~x0 in header name."
                     (s-char-escape->escape schar))))
       (qchar (q-char (s-char-char->code schar)))
       ((erp qchars) (s-char-list-to-q-char-list (cdr schars))))
    (retok (cons qchar qchars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define s-char-list-to-h-char-list ((schars s-char-listp))
  :returns (mv erp (hchars h-char-listp))
  :short "Convert a list of @(tsee s-char)s to a list of @(tsee h-char)s."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when attempting to convert a stringization
     to an angle-bracket header name, in @(tsee indirect-header-name).
     We ensure that there are no escapes.
     For now there are no restrictions on the ASTs,
     so every @(tsee s-char) code can be used as a @(tsee h-char) code."))
  (b* (((reterr) nil)
       ((when (endp schars)) (retok nil))
       (schar (car schars))
       ((when (s-char-case schar :escape))
        (reterr (msg "Cannot have escape ~x0 in header name."
                     (s-char-escape->escape schar))))
       (hchar (h-char (s-char-char->code schar)))
       ((erp hchars) (s-char-list-to-h-char-list (cdr schars))))
    (retok (cons hchar hchars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-closing-angle-bracket ((lexemes plexeme-listp))
  :returns (mv erp
               (lexemes-before plexeme-listp)
               (lexemes-after plexeme-listp))
  :short "Find the first closing angle bracket in a list of lexemes,
          returning the lexemes before and after it."
  :long
  (xdoc::topstring
   (xdoc::p
    "An error is returned if the bracket is not found."))
  (b* (((reterr) nil nil)
       ((when (endp lexemes))
        (reterr (msg "No closing angle bracket found.")))
       (lexeme (car lexemes))
       ((when (plexeme-punctuatorp lexeme ">"))
        (retok nil (plexeme-list-fix (cdr lexemes))))
       ((erp lexemes-before lexemes-after)
        (find-closing-angle-bracket (cdr lexemes))))
    (retok (cons (plexeme-fix lexeme) lexemes-before)
           lexemes-after)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define indirect-header-name ((lexemes plexeme-listp))
  :returns (mv erp
               (header header-namep)
               (wsc-after plexeme-listp)
               (newline plexemep))
  :short "Obtain a header name from a list of lexemes, if possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for ``indirect'' file inclusions,
     i.e. ones where the @('#include') directive
     has the form in [C17:6.10.2/4],
     i.e. not as explicit as [C17:6.10.2/2] and [C17:6.10.2/3],
     but they should be reducible to one of those two forms.
     The lexemes passed as input to this function
     are obtained by performing macro replacement just after the @('#include').
     This function attempts to extract the header name,
     and also returns any white space and comments after it,
     and separately the final new line.
     There cannot be any white space and comments before the header name,
     because the macro replacement that results in
     the lexemes passed as input to this function
     is performed starting with a token,
     after it has been recognized not to be a header name.")
   (xdoc::p
    "[C17:6.10.2/4] says that the details of how the resulting lexemes
     are combined into a header name are implementation-defined.
     Our approach is the following.")
   (xdoc::p
    "If the lexemes start with a string literal,
     we attempt to build a double-quote header name;
     note that this is the only option,
     as an angle-bracket header name would have to start with @('<').
     We ensure that the string literal has no prefix,
     and that its characters can be converted.
     We also ensure that no other token follows.
     We build and return a double-quote header name.")
   (xdoc::p
    "If instead the lexemes start with an open angle bracket @('<'),
     we try to find the closing one @('>'), returning an error if not found.
     We stringize all the lexemes before the @('>'),
     obtaining a list of @(tsee s-char)s,
     which we convert to @(tsee q-char)s
     via @(tsee s-char-list-to-q-char-list).
     We form an angle-bracket header, which we return.
     We also ensure that there are no other tokens after the @('>').")
   (xdoc::p
    "In all other cases, we return an error.
     We will extend our approach, if needed."))
  (b* (((reterr) (irr-header-name) nil (irr-plexeme))
       ((when (endp lexemes))
        (raise "Internal error: no lexemes.")
        (reterr t))
       (lexeme (car lexemes))
       ((when (plexeme-case lexeme :string))
        (b* (((stringlit stringlit) (plexeme-string->literal lexeme))
             ((when stringlit.prefix?)
              (reterr (msg "Cannot convert string with prefix ~x0 ~
                            to a header name."
                           stringlit)))
             ((erp qchars) (s-char-list-to-q-char-list stringlit.schars))
             (header (header-name-quotes qchars))
             (lexemes-rest (cdr lexemes))
             ((unless (plexeme-list-not-tokenp lexemes-rest))
              (reterr (msg "Extra tokens in ~x0 after header name."
                           lexemes-rest)))
             ((unless (consp lexemes-rest))
              (raise "Internal error: ~
                      indirect #include line does not end with new line.")
              (reterr t))
             (lexemes-rest (plexeme-list-fix lexemes-rest))
             (wsc-after (butlast lexemes-rest 1))
             (newline (car (last lexemes-rest)))
             ((unless (plexeme-case newline :newline))
              (raise "Internal error: ~
                      indirect #include line does not end with new line.")
              (reterr t)))
          (retok header wsc-after newline)))
       ((when (plexeme-punctuatorp lexeme "<"))
        (b* (((erp lexemes-before lexemes-after)
              (find-closing-angle-bracket (cdr lexemes)))
             (schars (stringize-lexeme-list lexemes-before))
             ((erp hchars) (s-char-list-to-h-char-list schars))
             (header (header-name-angles hchars))
             ((unless (plexeme-list-not-tokenp lexemes-after))
              (reterr (msg "Extra tokens in ~x0 after header name."
                           lexemes-after)))
             ((unless (consp lexemes-after))
              (raise "Internal error: ~
                      indirect #include line does not end with new line.")
              (reterr t))
             (lexemes-after (plexeme-list-fix lexemes-after))
             (wsc-after (butlast lexemes-after 1))
             (newline (car (last lexemes-after)))
             ((unless (plexeme-case newline :newline))
              (raise "Internal error: ~
                      indirect #include line does not end with new line.")
              (reterr t)))
          (retok header wsc-after newline))))
    (reterr (msg "Cannot convert ~x0 to a header name."
                 (plexeme-list-fix lexemes))))
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable true-listp-when-plexeme-listp)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-to-end-of-line ((ppstate ppstatep))
  :returns (mv erp
               (lexemes plexeme-listp)
               (new-ppstate ppstatep))
  :short "Read lexemes up to (including) the next new line."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return the lexemes, in the order they appear."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil ppstate)
       ((erp lexeme span ppstate) (read-lexeme nil ppstate))
       ((when (not lexeme)) ; EOF
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a lexeme"
                    :found "end of file"))
       ((when (plexeme-case lexeme :newline)) ; EOL
        (retok (list lexeme) ppstate))
       ((erp lexemes ppstate) (read-to-end-of-line ppstate)))
    (retok (cons lexeme lexemes) ppstate))
  :no-function nil
  :measure (ppstate->size ppstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pproc-error ((ppstate ppstatep))
  :returns (mv erp (new-ppstate ppstatep))
  :short "Preprocess a @('#error') directive."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called just after the @('error') identifier has been parsed.")
   (xdoc::p
    "We read the rest of the directive.
     If errors and warnings must be ignored, we do nothing.
     Otherwise, we return an error message that contains the rest of the line,
     in printed form (using the preprocessor printer).
     This could be refined in the future.")
   (xdoc::p
    "Although neither [C17:6.10.5] nor [C23:6.10.7]
     explicitly say that preprocessing must stop,
     [CPPM:5] does, and that seems indeed the intention."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) ppstate)
       ((erp lexemes ppstate) (read-to-end-of-line ppstate))
       (ppstate (hg-trans-non-ifndef/elif/else/define ppstate))
       ((when (ppoptions->no-errors/warnings (ppstate->options ppstate)))
        (retok ppstate))
       (bytes (plexemes-to-bytes lexemes))
       (string (acl2::nats=>string bytes)))
    (reterr (msg "#error: ~s0" string)))
  :guard-hints
  (("Goal" :in-theory (enable acl2::unsigned-byte-listp-rewrite-byte-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pproc-warning ((ppstate ppstatep))
  :returns (mv erp (new-ppstate ppstatep))
  :short "Preprocess a @('#warning') directive."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called just after the @('warning') identifier has been parsed.")
   (xdoc::p
    "This is allowed only if the C version is C23,
     or the GCC or Clang extensions are enabled;
     otherwise we return an error.")
   (xdoc::p
    "We read the rest of the directive.
     If errors and warnings must be ignored, we do nothing.
     Otherwise, we use the printer to turn the lexemes in the rest of the line
     into an ACL2 string, which we print as comment output.
     Unlike @(tsee pproc-error), we do not return an error,
     so preprocessing can continue.
     The choice of printing the warning as comment output
     could be revisited in the future;
     perhaps some new options to the preprocessor
     could indicate different ways to handle the warning messages.")
   (xdoc::p
    "Although [C23:6.10.7] does not explicitly say that
     preprocessing must continue,
     [CPPM:5] does, and that seems indeed the intention."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) ppstate)
       (ienv (ppstate->ienv ppstate))
       ((unless (or (= (ienv->std ienv) 23)
                    (ienv->gcc/clang ienv)))
        (reterr (msg "#warning directive disallowed in ~
                      C17 without GCC or Clang extensions.")))
       ((erp lexemes ppstate) (read-to-end-of-line ppstate))
       (ppstate (hg-trans-non-ifndef/elif/else/define ppstate))
       ((when (ppoptions->no-errors/warnings (ppstate->options ppstate)))
        (retok ppstate))
       (bytes (plexemes-to-bytes lexemes))
       (string (acl2::nats=>string bytes))
       (- (cw "#warning: ~s0" string)))
    (retok ppstate))
  :guard-hints
  (("Goal" :in-theory (enable acl2::unsigned-byte-listp-rewrite-byte-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-rev-lexemes ((ppstate ppstatep))
  :returns (rev-lexemes plexeme-listp)
  :short "Extract all the reverse output lexemes from the preprocessor state."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee add-rev-lexeme),
     the output lexemes are organized in four lists in @(tsee ppstate).
     After finishing the preprocessing of a file,
     we call this function to obtain the final list of lexemes.
     The header guard state must be a final one (it should be an invariant).
     Based on that, we combine the lexemes,
     either interposing the directives or not.")
   (xdoc::p
    "When interposing the directives,
     currently we only have information about the macro name.
     We plan to improve this by keeping track of more details,
     such as the exact new lines (for now we just use LF)."))
  (b* ((hg (ppstate->hg ppstate)))
    (hg-state-case
     hg
     :eof
     (b* ((rev-lexemes nil)
          (rev-lexemes (append (ppstate->rev-lexemes1 ppstate) rev-lexemes))
          (rev-lexemes (cons (plexeme-punctuator "#") rev-lexemes))
          (rev-lexemes (cons (plexeme-ident (ident "ifndef")) rev-lexemes))
          (rev-lexemes (cons (plexeme-spaces 1) rev-lexemes))
          (rev-lexemes (cons (plexeme-ident hg.name) rev-lexemes))
          (rev-lexemes (cons (plexeme-newline (newline-lf)) rev-lexemes))
          (rev-lexemes (append (ppstate->rev-lexemes2 ppstate) rev-lexemes))
          (rev-lexemes (cons (plexeme-punctuator "#") rev-lexemes))
          (rev-lexemes (cons (plexeme-ident (ident "define")) rev-lexemes))
          (rev-lexemes (cons (plexeme-spaces 1) rev-lexemes))
          (rev-lexemes (cons (plexeme-ident hg.name) rev-lexemes))
          (rev-lexemes (cons (plexeme-spaces 1) rev-lexemes))
          (rev-lexemes (cons (plexeme-ident hg.name) rev-lexemes))
          (rev-lexemes (cons (plexeme-newline (newline-lf)) rev-lexemes))
          (rev-lexemes (append (ppstate->rev-lexemes3 ppstate) rev-lexemes))
          (rev-lexemes (cons (plexeme-punctuator "#") rev-lexemes))
          (rev-lexemes (cons (plexeme-ident (ident "endif")) rev-lexemes))
          (rev-lexemes (cons (plexeme-newline (newline-lf)) rev-lexemes))
          (rev-lexemes (append (ppstate->rev-lexemes4 ppstate) rev-lexemes)))
       rev-lexemes)
     :not
     (b* ((rev-lexemes nil)
          (rev-lexemes (append (ppstate->rev-lexemes1 ppstate) rev-lexemes))
          (rev-lexemes (append (ppstate->rev-lexemes2 ppstate) rev-lexemes))
          (rev-lexemes (append (ppstate->rev-lexemes3 ppstate) rev-lexemes))
          (rev-lexemes (append (ppstate->rev-lexemes4 ppstate) rev-lexemes)))
       rev-lexemes)
     :otherwise
     (raise "Internal error: non-final header guard state ~x0." hg)))
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable true-listp-when-plexeme-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rebuild-include-directive ((nontoknls-before-hash plexeme-listp)
                                   (nontoknls-after-hash plexeme-listp)
                                   (nontoknls-before-header plexeme-listp)
                                   (header header-namep)
                                   (nontoknls-after-header plexeme-listp)
                                   (newline-at-end plexemep))
  :returns (lexemes plexeme-listp)
  :short "Rebuild a @('#include') directive from its components."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return the directive as a list of lexemes."))
  (append (plexeme-list-fix nontoknls-before-hash)
          (list (plexeme-punctuator "#"))
          (plexeme-list-fix nontoknls-after-hash)
          (list (plexeme-ident (ident "include")))
          (plexeme-list-fix nontoknls-before-header)
          (list (plexeme-header header))
          (plexeme-list-fix nontoknls-after-header)
          (list (plexeme-fix newline-at-end))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expanded-include-comment-lines ((header header-namep)
                                        (newline-at-end plexemep))
  :returns (mv (opening-line plexeme-listp)
               (closing-line plexeme-listp))
  :short "Opening and closing comment lines for expanded @('#include')s."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when tracing the expansion of @('#include') directives.
     The expanded material is surrounded by
     an opening comment line and a closing comment line."))
  (b* ((header-codes (header-name-case
                      header
                      :angles (append (list (char-code #\<))
                                      (h-char-list->code-list header.chars)
                                      (list (char-code #\>)))
                      :quotes (append (list (char-code #\"))
                                      (q-char-list->code-list header.chars)
                                      (list (char-code #\")))))
       (include-codes (append (acl2::string=>nats " #include ") header-codes))
       (opening-codes (append include-codes (acl2::string=>nats " >>>>>>>>>>")))
       (closing-codes (append (acl2::string=>nats " <<<<<<<<<<") include-codes))
       (opening-line (list (plexeme-line-comment opening-codes)
                           (plexeme-fix newline-at-end)))
       (closing-line (list (plexeme-line-comment closing-codes)
                           (plexeme-fix newline-at-end))))
    (mv opening-line closing-line)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expand-include-in-place ((header header-namep)
                                 (newline-at-end plexemep)
                                 (rev-included-file-lexemes plexeme-listp)
                                 (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Expand an included file in place."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when, while preprocessing an including file,
     we find a @('#include') of a file (the included file)
     that must be expanded in place.
     At the core, this just adds the lexemes of the included file
     to the list of lexemes of the including file.
     If the option to trace @('#include') expansions is set,
     we surround the inserted lexemes with two line comments,
     indicating and delimiting the contents of the included file.")
   (xdoc::p
    "With reference to @(tsee pproc-header-name), which calls this function,
     we ignore all the white space and comments in the @('#include') directive,
     except for the final new line, which we pass to this function,
     so we can use it to end the delimiting line comments that we generate.")
   (xdoc::p
    "A @('#include') directive takes one or more lines.
     Conceptually it is just one line,
     but it could contain block comments that take multiple lines;
     it is a single line when those block comments are regarded as single spaces
     [C17:5.1.1.2/3].
     In any case, it takes a whole number of lines.
     We replace those lines with the lexemes we generate in this function,
     which also take a whole number of lines."))
  (if (ppoptions->trace-expansion (ppstate->options ppstate))
      (b* (((mv opening-line closing-line)
            (expanded-include-comment-lines header newline-at-end))
           (ppstate (add-rev-lexemes opening-line ppstate))
           (ppstate (add-rev-rev-lexemes rev-included-file-lexemes ppstate))
           (ppstate (add-rev-lexemes closing-line ppstate)))
        ppstate)
    (add-rev-rev-lexemes rev-included-file-lexemes ppstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines compare-pparts/conds
  :short "Functions to compare
          preprocessor group parts, and related entities,
          for equivalence with respect to macro tables."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee compare-pfiles) for motivation and overview."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define compare-pparts ((part1 ppartp)
                          (part2 ppartp)
                          (macros macro-tablep)
                          (ienv ienvp))
    :returns (yes/no booleanp)
    :parents (preprocessor compare-pparts/conds)
    :short "Compare two preprocessor group parts
            for equivalence with respect to a macro table."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two group parts must be of the same kind.
       If they are of the @(':line') kind, they must be identical.
       If they are of the @(':cond') kind,
       they must have the same opening
       @('#if') of @('#ifdef') or @('#ifndef') directive,
       and then we use a seaparate function to compare the rest.
       The separate function uses the same flags @('condp') and @('donep')
       used by some of the @('pproc-...') functions
       to select the branch of a conditional section.
       The initial @('condp') is determined from
       the initial @('#if') of @('#ifdef') or @('#ifndef') directive;
       in the case of the @('#if'),
       the evaluation of the expression should not return an error,
       because when we get here the expression has been already evaluated,
       in the @('pproc-...') functions."))
    (ppart-case
     part1
     :line (ppart-equiv part1 part2)
     :cond
     (ppart-case
      part2
      :line nil
      :cond
      (and (equal part1.if part2.if)
           (b* ((condp
                 (pif-case
                  part1.if
                  :if (b* (((mv erp pval)
                            (peval-expr part1.if.expr macros ienv))
                           ((when erp)
                            (raise "Internal error: ~
                                    evaluation of ~x0 errors."
                                   part1.if.expr)))
                        (not (= (pvalue->integer pval) 0)))
                  :ifdef (and (macro-lookup part1.if.name macros) t)
                  :ifndef (not (macro-lookup part1.if.name macros)))))
             (compare-if/ifdef/ifndef-rest condp
                                           nil ; done
                                           part1.parts
                                           part2.parts
                                           part1.elifs
                                           part2.elifs
                                           part1.else
                                           part2.else
                                           macros
                                           ienv)))))
    :no-function nil
    :measure (ppart-count part1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define compare-ppart-lists ((parts1 ppart-listp)
                               (parts2 ppart-listp)
                               (macros macro-tablep)
                               (ienv ienvp))
    :returns (yes/no booleanp)
    :parents (preprocessor compare-pparts/conds)
    :short "Compare two lists of preprocessor group parts
            for equivalence with respect to a macro table."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two lists must have the same length
       and their corresponding elements must compare equal."))
    (if (endp parts1)
        (endp parts2)
      (and (consp parts2)
           (compare-pparts (car parts1) (car parts2) macros ienv)
           (compare-ppart-lists (cdr parts1) (cdr parts2) macros ienv)))
    :measure (ppart-list-count parts1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define compare-if/ifdef/ifndef-rest ((condp booleanp)
                                        (donep booleanp)
                                        (prev-cond-body1 ppart-listp)
                                        (prev-cond-body2 ppart-listp)
                                        (elifs1 pelif-listp)
                                        (elifs2 pelif-listp)
                                        (else?1 pelse-optionp)
                                        (else?2 pelse-optionp)
                                        (macros macro-tablep)
                                        (ienv ienvp))
    :returns (yes/no booleanp)
    :parents (preprocessor compare-pparts/conds)
    :short "Compare the rest of two preprocessor conditional sections
            for equivalence with respect to a macro table."
    :long
    (xdoc::topstring
     (xdoc::p
      "First, we need to compare the group parts of the previous condition,
       passed here as the @('prev-cond-body1') and @('prev-cond-body2') inputs.
       Their comparison succeeds if they compare equal,
       or if they are not selected.
       Whether they are selected or not is determined
       from the @('condp') and @('donep') boolean flags.")
     (xdoc::p
      "If that comparison succeeds,
       we must look at the `elif' and `else' groups.
       If the first list of `elif' groups is exhausted,
       the second list must be exhausted as well,
       and we compare the `else' groups.
       The two `else' groups must be either both present or both absent.
       If present, they must be equal, unless they are not selected;
       they are not selected only if a previous branch was selected.")
     (xdoc::p
      "If the first list of `elif' groups is not exhausted,
       the second one must not be exhausted either.
       The starting `elif' groups of both lists must have the same expression,
       and then we recursively call this function with the two bodies;
       we update the @('condp') and @('donep') flags as needed.
       Expression evaluation cannot fail,
       for the same reasons noted in @(tsee compare-pparts).
       If @('donep') is already @('t'),
       there is no need to update @('condp')."))
    (b* ((selectedp (and condp (not donep))))
      (and (or (not selectedp)
               (compare-ppart-lists prev-cond-body1
                                    prev-cond-body2
                                    macros
                                    ienv))
           (if (endp elifs1)
               (and (endp elifs2)
                    (if else?1
                        (and else?2
                             (b* ((selectedp (not donep)))
                               (or (not selectedp)
                                   (compare-ppart-lists (pelse->parts else?1)
                                                        (pelse->parts else?2)
                                                        macros
                                                        ienv))))
                      (not else?2)))
             (and (not (endp elifs2))
                  (b* (((pelif elif1) (car elifs1))
                       ((pelif elif2) (car elifs2)))
                    (and (equal elif1.expr elif2.expr)
                         (if donep
                             (compare-if/ifdef/ifndef-rest condp
                                                           donep
                                                           elif1.parts
                                                           elif2.parts
                                                           (cdr elifs1)
                                                           (cdr elifs2)
                                                           else?1
                                                           else?2
                                                           macros
                                                           ienv)
                           (b* (((mv erp pval)
                                 (peval-expr elif1.expr macros ienv))
                                ((when erp)
                                 (raise "Internal error: ~
                                         evaluation of ~x0 errors."
                                        elif1.expr))
                                (condp (not (= (pvalue->integer pval) 0))))
                             (compare-if/ifdef/ifndef-rest condp
                                                           donep
                                                           elif1.parts
                                                           elif2.parts
                                                           (cdr elifs1)
                                                           (cdr elifs2)
                                                           else?1
                                                           else?2
                                                           macros
                                                           ienv)))))))))
    :no-function nil
    :measure (+ (ppart-list-count prev-cond-body1)
                (pelif-list-count elifs1)
                (pelse-option-count else?1)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable fix
                                     ppart-count
                                     pelse-option-count
                                     pelse-option-some->val)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual compare-pparts/conds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compare-pfiles ((pfile1 pfilep)
                        (pfile2 pfilep)
                        (macros macro-tablep)
                        (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Compare two preprocessor files for equivalence
          with respect to a macro table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This checks whether the two preprocessor files are equal,
     modulo the elimination of conditional bodies
     that are not selected according to the macro table.
     Consider two conditional (i.e. `if') sections,
     which have one or more conditions:
     one is the @('#if') or @('#ifdef') or @('#ifndef'),
     then zero or more @('#elif')s,
     then an optional final @('#else').
     Under each such condition, there is a body,
     i.e. the group parts that are selected when the condition is selected.
     Here `selected' does not just mean `true', because order matters:
     the selected condition is the first true conditions;
     subsequent conditions, whether true or false, are not selected.
     In the @('pproc-...') functions for conditionals,
     this selection is realized via the @('condp') and @('donep') flags.")
   (xdoc::p
    "Now consider two such conditional sections,
     with the same shape, i.e. the same conditions,
     but possibly some differences in the bodies of the conditions.
     If the only differences in these bodies are in non-selected conditions,
     then the two conditional sections are considered equivalent.")
   (xdoc::p
    "The motivation for this kind of comparison
     is to support more "
    (xdoc::seetopic "preservable-inclusions"
                    "preservation of @('#include')s")
    ". Currently files with header guards of a common but specific form
     are treated specially,
     but that is just a special case of the comparison
     realized by this function.
     We plan to replace that specific header guard handling
     with the use of this comparison between preprocessor files."))
  (compare-ppart-lists (pfile->parts pfile1)
                       (pfile->parts pfile2)
                       macros
                       ienv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pproc-files/groups/etc
  :short "Preprocess files, groups, and some related entities."
  :long
  (xdoc::topstring
   (xdoc::p
    "The top-level function of the clique is @(tsee pproc-file),
     which is called by @(tsee pproc-files) outside the clique.
     But it is also called when encountering files to be included,
     which is why it is mutually recursive with the other functions.")
   (xdoc::p
    "The functions in the clique have certain common inputs and outputs:")
   (xdoc::ul
    (xdoc::li
     "All the functions take
      the path @('file') of the file being preprocessed,
      along with the base directory @('base-dir')
      and the inclusion directories @('include-dirs').
      The base and inclusion directories
      come from @(tsee pproc-files) and never change.
      The @('file') path comes from the list @('files') in @(tsee pproc-files),
      as well as from the resolution of @('#include') directives.")
    (xdoc::li
     "All the functions take and return
      the alist @('preprocessed'), which contain (the results of)
      the files preprocessed so far.
      This starts empty and eventually (if there are no errors)
      contains all the preprocessed files,
      namely the files listed in the list @('files')
      passed to @(tsee pproc-files),
      as well as zero or more referenced in preserved @('#include')s.")
    (xdoc::li
     "All the functions take
      the list @('preprocessing') of the files being preprocessed.
      This is used to detect circularities.")
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
                 "[CPPM:12.2]")
    ". So we could perhaps use a lexicographic measure consisting of
     the number of recursive files remaining
     followed by the size of the preprocessing state.
     We plan to flesh out the termination proof at some point.")
   (xdoc::p
    "These functions handle the state machine described in @(tsee hg-state),
     via the @('hg-trans-...') functions defined on the preprocessor state.")
   (xdoc::p
    "Some of the functions also take as input
     indicating the level of nesting of conditionals.
     It is 0 at the top level,
     and it is incremented by 1 when entering an @('if-section')."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-file ((bytes byte-listp)
                      (file stringp)
                      (base-dir stringp)
                      (include-dirs string-listp)
                      (options ppoptionsp)
                      (preprocessed string-pfile-alistp)
                      (preprocessing string-listp)
                      (macros macro-tablep)
                      (ienv ienvp)
                      state
                      (limit natp))
    :returns (mv erp
                 (pfile pfilep)
                 (file-macros ident-macro-info-option-alistp)
                 (new-preprocessed string-pfile-alistp)
                 state)
    :parents (preprocessor pproc-files/groups/etc)
    :short "Preprocess a file."
    :long
    (xdoc::topstring
     (xdoc::p
      "The bytes contained in the file are passed to this function.
       The file itself is read by the callers,
       namely @(tsee pproc-files) and @(tsee pproc-header-name).")
     (xdoc::p
      "If @('file') is found in the list of the files under preprocessing,
       we stop with an error, because there is a circularity.
       Otherwise, before preprocessing the file,
       we add it to the list of files under preprocessing.")
     (xdoc::p
      "The macro table passed as input to this function
       is empty when this function is called by @(tsee pproc-files).
       Otherwise, it is the table for
       the file that contains the @('#include') directive
       that results in this call of @(tsee pproc-file),
       called by @(tsee pproc-header-name), called by @(tsee pproc-include).")
     (xdoc::p
      "We create a local preprocessing state stobj from
       the bytes of the file,
       the macro table,
       and the implementation environment.
       The preprocessing of this file may involve
       the recursive preprocessing of more files,
       and the consequent extension of the @('preprocessed') alist.
       We ensure that the optional group read by @(tsee pproc-*-group-part)
       ends with the end of the file,
       because we are at the top level,
       not inside a conditional directive.
       If there are no errors, we return
       the lexemes of the file (in reverse order),
       the macros contributed by the file,
       and the header guard symbol (if the file has the header guard form).")
     (xdoc::p
      "If full expansion is required,
       we set the header guard state to @(':not'),
       because for full expansion we do not need
       to recognize the header guard form."))
    (b* (((reterr) (irr-pfile) nil nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         (file (str-fix file))
         (preprocessing (string-list-fix preprocessing))
         ((when (member-equal file preprocessing))
          (reterr (msg "Circular file dependencies involving ~&0."
                       preprocessing)))
         (preprocessing (cons file preprocessing))
         ((erp pfile
               groupend
               file-macros
               preprocessed
               state)
          (with-local-stobj
            ppstate
            (mv-let (erp
                     pfile
                     groupend
                     file-macro-table
                     ppstate
                     preprocessed
                     state)
                (b* ((ppstate (init-ppstate bytes
                                            macros
                                            options
                                            ienv
                                            ppstate))
                     (ppstate (if (ppoptions->full-expansion options)
                                  (update-ppstate->hg (hg-state-not) ppstate)
                                ppstate))
                     ((mv erp
                          pparts
                          groupend
                          ppstate
                          preprocessed
                          state)
                      (pproc-*-group-part file
                                          base-dir
                                          include-dirs
                                          preprocessed
                                          preprocessing
                                          0 ; cond-level
                                          ppstate
                                          state
                                          (1- limit))))
                  (mv erp
                      (make-pfile :parts pparts)
                      groupend
                      (ppstate->macros ppstate)
                      ppstate
                      preprocessed
                      state))
              (mv erp
                  pfile
                  groupend
                  (macro-table->dynamic file-macro-table)
                  preprocessed
                  state))))
         ((unless (groupend-case groupend :eof))
          (reterr (msg "Found directive ~s0 ~
                        without a preceding #if, #ifdef, or #ifndef."
                       (groupend-case
                        groupend
                        :eof (impossible)
                        :elif "#elif"
                        :else "#else"
                        :endif "#endif")))))
      (retok pfile
             file-macros
             preprocessed
             state))
    :no-function nil
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-*-group-part ((file stringp)
                              (base-dir stringp)
                              (include-dirs string-listp)
                              (preprocessed string-pfile-alistp)
                              (preprocessing string-listp)
                              (cond-level natp)
                              (ppstate ppstatep)
                              state
                              (limit natp))
    :returns (mv erp
                 (pparts ppart-listp)
                 (groupend groupendp)
                 (new-ppstate ppstatep)
                 (new-preprocessed string-pfile-alistp)
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
         ((reterr) nil (irr-groupend) ppstate nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         ((erp pparts groupend? ppstate preprocessed state)
          (pproc-?-group-part file
                              base-dir
                              include-dirs
                              preprocessed
                              preprocessing
                              cond-level
                              ppstate
                              state
                              (1- limit)))
         ((when groupend?)
          (retok pparts groupend? ppstate preprocessed state))
         ((erp more-pparts groupend ppstate preprocessed state)
          (pproc-*-group-part file
                              base-dir
                              include-dirs
                              preprocessed
                              preprocessing
                              cond-level
                              ppstate
                              state
                              (1- limit))))
      (retok (append pparts more-pparts) groupend ppstate preprocessed state))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-?-group-part ((file stringp)
                              (base-dir stringp)
                              (include-dirs string-listp)
                              (preprocessed string-pfile-alistp)
                              (preprocessing string-listp)
                              (cond-level natp)
                              (ppstate ppstatep)
                              state
                              (limit natp))
    :returns (mv erp
                 (pparts ppart-listp)
                 (groupend? groupend-optionp)
                 (new-ppstate ppstatep)
                 (new-preprocessed string-pfile-alistp)
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
       Otherwise, we return the end-of-file group ending,
       and we update the header guard according to end of file.")
     (xdoc::p
      "If we find a hash, we have a directive.
       We read the next token or new line.
       If we find none, it is an error,
       beacuse the file cannot end without a new line [C17:5.2.1.2/2].
       If we find a new line, we have a null directive [C17:6.10.7]:
       we eliminate the line, since it does nothing.
       If we find an identifier, we dispatch based on the identifier:
       for @('#elif'), @('#else'), and @('#endif'),
       we return the corresponding group ending;
       for other directives, we call separate functions.
       If the identifier is not a directive name,
       or if we do not find an identifier,
       we have a non-directive
       (which is a directive, despite the name,
       see footnote 175 in [C17:6.10.3/11]):
       we return an error for now, which is consistent with [C17:6.10/9].
       We allow the @('#warning') directive
       if the C standard is C23 [C23:6.10.1]
       or the GCC or Clang extensions are enabled;
       this is handled in a separate function.
       For @('#elif'), @('#else'), and @('#endif'),
       we do not udpate the header guard state,
       because, in a valid file, we would not encounter them
       as part of preprocessing the top-level list of group parts,
       but only in the course of
       recursive preprocessing of lists of group parts;
       for other directives, any updates to the guard header state
       are performed in separate functions.")
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
          (b* ((ppstate (hg-trans-eof ppstate)))
            (retok nil ; no group parts
                   (groupend-eof)
                   ppstate
                   (string-pfile-alist-fix preprocessed)
                   state))))
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
            (retok nil ; no group parts
                   nil ; no group ending
                   ppstate
                   (string-pfile-alist-fix preprocessed)
                   state))
           ((plexeme-case toknl2 :ident) ; # ident
            (b* ((directive (ident->unwrap (plexeme-ident->ident toknl2))))
              (cond
               ((equal directive "elif") ; # elif
                (retok nil ; no group parts
                       (groupend-elif)
                       ppstate
                       (string-pfile-alist-fix preprocessed)
                       state))
               ((equal directive "else") ; # else
                (retok nil ; no group parts
                       (groupend-else)
                       ppstate
                       (string-pfile-alist-fix preprocessed)
                       state))
               ((equal directive "endif") ; # endif
                (retok nil ; no group parts
                       (groupend-endif)
                       ppstate
                       (string-pfile-alist-fix preprocessed)
                       state))
               ((equal directive "if") ; # if
                (b* (((erp pparts ppstate preprocessed state)
                      (pproc-if file
                                base-dir
                                include-dirs
                                preprocessed
                                preprocessing
                                (1+ (lnfix cond-level))
                                ppstate
                                state
                                (1- limit))))
                  (retok pparts
                         nil ; no group ending
                         ppstate
                         preprocessed
                         state)))
               ((equal directive "ifdef") ; # ifdef
                (b* (((erp pparts ppstate preprocessed state)
                      (pproc-ifdef/ifndef t
                                          file
                                          base-dir
                                          include-dirs
                                          preprocessed
                                          preprocessing
                                          (1+ (lnfix cond-level))
                                          ppstate
                                          state
                                          (1- limit))))
                  (retok pparts
                         nil ; no group ending
                         ppstate
                         preprocessed
                         state)))
               ((equal directive "ifndef") ; # ifndef
                (b* (((erp pparts ppstate preprocessed state)
                      (pproc-ifdef/ifndef nil
                                          file
                                          base-dir
                                          include-dirs
                                          preprocessed
                                          preprocessing
                                          (1+ (lnfix cond-level))
                                          ppstate
                                          state
                                          (1- limit))))
                  (retok pparts
                         nil ; no group ending
                         ppstate
                         preprocessed
                         state)))
               ((equal directive "include") ; # include
                (b* (((erp pparts ppstate preprocessed state)
                      (pproc-include nontoknls-before-hash
                                     nontoknls-after-hash
                                     file
                                     base-dir
                                     include-dirs
                                     preprocessed
                                     preprocessing
                                     ppstate
                                     state
                                     (1- limit))))
                  (retok pparts
                         nil ; no group ending
                         ppstate
                         preprocessed
                         state)))
               ((equal directive "define") ; # define
                (b* (((erp pparts ppstate) (pproc-define ppstate)))
                  (retok pparts
                         nil ; no group ending
                         ppstate
                         (string-pfile-alist-fix preprocessed)
                         state)))
               ((equal directive "undef") ; # undef
                (b* (((erp pparts ppstate) (pproc-undef ppstate)))
                  (retok pparts
                         nil ; no group ending
                         ppstate
                         (string-pfile-alist-fix preprocessed)
                         state)))
               ((equal directive "line") ; # line
                (reterr (msg "#line directive not yet supported."))) ; TODO
               ((equal directive "error") ; # error
                (b* (((erp ppstate) (pproc-error ppstate)))
                  (retok nil ; no group parts
                         nil ; no group ending
                         ppstate
                         (string-pfile-alist-fix preprocessed)
                         state)))
               ((equal directive "warning") ; # warning
                (b* (((erp ppstate) (pproc-warning ppstate)))
                  (retok nil ; no group parts
                         nil ; no group ending
                         ppstate
                         (string-pfile-alist-fix preprocessed)
                         state)))
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
           (t ; # non-ident -- non-directive
            (reterr-msg :where (span->start span2)
                        :expected "an identifier"
                        :found (plexeme-to-msg toknl2))))))
       (t ; non-# -- text line
        (b* ((ppstate (add-rev-lexemes nontoknls ppstate))
             (ppstate (unread-lexeme toknl span ppstate))
             (preprocessed (string-pfile-alist-fix preprocessed))
             ((erp rev-lexmarks ppstate)
              (pproc-lexemes (macrep-mode-line)
                             nil ; rev-lexmarks
                             0 ; paren-level
                             nil ; no-expandp
                             nil ; disabled
                             nil ; directivep
                             ppstate
                             limit)) ; unrelated to limit for this clique
             ((unless (lexmark-list-case-lexeme-p rev-lexmarks))
              (raise "Internal error: ~x0 contains markers.")
              (reterr t))
             (rev-lexemes-to-add (lexmark-list-to-lexeme-list rev-lexmarks))
             (ppstate (if (plexeme-list-not-tokenp rev-lexemes-to-add)
                          ppstate
                        (hg-trans-non-ifndef/elif/else/define ppstate)))
             (ppstate (add-rev-rev-lexemes rev-lexemes-to-add ppstate))
             (lexemes (append nontoknls (rev rev-lexemes-to-add)))
             (lexemes (if (ppoptions->keep-comments
                           (ppstate->options ppstate))
                          lexemes
                        (plexemes-without-comments lexemes))))
          (retok (list (ppart-line lexemes))
                 nil ; no group ending
                 ppstate
                 preprocessed
                 state)))))
    :no-function nil
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-include ((nontoknls-before-hash plexeme-listp)
                         (nontoknls-after-hash plexeme-listp)
                         (file stringp)
                         (base-dir stringp)
                         (include-dirs string-listp)
                         (preprocessed string-pfile-alistp)
                         (preprocessing string-listp)
                         (ppstate ppstatep)
                         state
                         (limit natp))
    :returns (mv erp
                 (pparts ppart-listp)
                 (new-ppstate ppstatep)
                 (new-preprocessed string-pfile-alistp)
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
       in the line (see grammar).
       Then we call a separate function to handle the header name.")
     (xdoc::p
      "If we find some other token, we put it back,
       and we perform macro replacement on the rest of the line.
       The resulting lexmarks are all lexemes,
       but since we do not have that fact statically available,
       we double-check that and throw a hard error if the check fails.
       We try to turn those lexemes into a header name,
       and then we use a separate function to preprocess it.")
     (xdoc::p
      "Since the only ways in which this function does not return an error
       is by first calling @(tsee pproc-header-name),
       we do not perform header guard transitions here,
       but we do in @(tsee pproc-header-name)."))
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
             ((erp pparts ppstate preprocessed state)
              (pproc-header-name nontoknls-before-hash
                                 nontoknls-after-hash
                                 nontoknls-before-header
                                 (plexeme-header->name toknl)
                                 nontoknls-after-header
                                 toknl2 ; new line
                                 file
                                 base-dir
                                 include-dirs
                                 preprocessed
                                 preprocessing
                                 ppstate
                                 state
                                 (1- limit))))
          (retok pparts
                 ppstate
                 (string-pfile-alist-fix preprocessed)
                 state)))
       (t ; # include not-headername
        (b* ((ppstate (unread-lexeme toknl span ppstate))
             ((erp rev-lexmarks ppstate)
              (pproc-lexemes (macrep-mode-line)
                             nil ; rev-lexmarks
                             0 ; paren-level
                             nil ; no-expandp
                             nil ; disabled
                             t ; directivep
                             ppstate
                             limit)) ; unrelated to limit for this clique
             (lexmarks (rev rev-lexmarks))
             ((unless (lexmark-list-case-lexeme-p lexmarks))
              (raise "Internal error: ~x0 contains markers." lexmarks)
              (reterr t))
             (header-name-lexemes (lexmark-list-to-lexeme-list lexmarks))
             ((erp header nontoknls-after-header newline)
              (indirect-header-name header-name-lexemes))
             ((erp pparts ppstate preprocessed state)
              (pproc-header-name nontoknls-before-hash
                                 nontoknls-after-hash
                                 nontoknls-before-header
                                 header
                                 nontoknls-after-header
                                 newline
                                 file
                                 base-dir
                                 include-dirs
                                 preprocessed
                                 preprocessing
                                 ppstate
                                 state
                                 (1- limit))))
          (retok pparts ppstate preprocessed state)))))
    :no-function nil
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-header-name ((nontoknls-before-hash plexeme-listp)
                             (nontoknls-after-hash plexeme-listp)
                             (nontoknls-before-header plexeme-listp)
                             (header header-namep)
                             (nontoknls-after-header plexeme-listp)
                             (newline-at-end plexemep)
                             (file stringp)
                             (base-dir stringp)
                             (include-dirs string-listp)
                             (preprocessed string-pfile-alistp)
                             (preprocessing string-listp)
                             (ppstate ppstatep)
                             state
                             (limit natp))
    :returns (mv erp
                 (pparts ppart-listp)
                 (new-ppstate ppstatep)
                 (new-preprocessed string-pfile-alistp)
                 state)
    :parents (preprocessor pproc-files/groups/etc)
    :short "Preprocess a @('#include') directive."
    :long
    (xdoc::topstring
     (xdoc::p
      "We resolve the header name to a file.")
     (xdoc::p
      "We preprocess the file, in the context of the including file.")
     (xdoc::p
      "To see whether we can avoid expanding the @('#include'),
       we re-preprocess the included file in a fresh context,
       unless we have already done that,
       in which case we use the previous results,
       which are part of the @('preprocessed') alist;
       after re-processing the file afresh,
       we add it to the @('preprocessed') alist.")
     (xdoc::p
      "There are two cases in which we can preserve the @('#include').
       The normal case is when we obtain identical results
       when we preprocess the included file in context vs. stand-alone.
       The special case is when the file has a header guard structure,
       and the header guard is defined in the context of the including file:
       see @(see preservable-inclusions).")
     (xdoc::p
      "However, if the options indicate full expansion,
       we do not re-preprocess the file,
       and we always expand it in place."))
    (b* ((ppstate (ppstate-fix ppstate))
         ((reterr) nil ppstate nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         (ppstate (hg-trans-non-ifndef/elif/else/define ppstate))
         ((erp resolved-file bytes state)
          (resolve-included-file file header base-dir include-dirs state))
         (ienv (ppstate->ienv ppstate))
         (options (ppstate->options ppstate))
         ((erp pfile
               file-macros
               preprocessed
               state)
          (pproc-file bytes
                      resolved-file
                      base-dir
                      include-dirs
                      options
                      preprocessed
                      preprocessing
                      (ppstate->macros ppstate)
                      ienv
                      state
                      (1- limit)))
         ((when (ppoptions->full-expansion options))
          (b* ((ppstate (update-ppstate->macros
                         (macro-extend file-macros (ppstate->macros ppstate))
                         ppstate))
               (ppstate (expand-include-in-place header
                                                 newline-at-end
                                                 nil ; file-rev-lexemes
                                                 ppstate))
               (pparts
                (if (ppoptions->trace-expansion (ppstate->options ppstate))
                    (b* (((mv opening-line closing-line)
                          (expanded-include-comment-lines header
                                                          newline-at-end)))
                      (append (list (ppart-line opening-line))
                              (pfile->parts pfile)
                              (list (ppart-line closing-line))))
                  (pfile->parts pfile))))
            (retok pparts ppstate preprocessed state)))
         ((erp standalone-pfile
               preprocessed
               state)
          (b* (((reterr) (irr-pfile) nil state)
               (name+pfile (assoc-equal resolved-file preprocessed)))
            (if name+pfile
                (retok (cdr name+pfile) preprocessed state)
              (b* (((erp pfile
                         & ; file-macros
                         preprocessed
                         state)
                    (pproc-file bytes
                                resolved-file
                                base-dir
                                include-dirs
                                (change-ppoptions options
                                                  :no-errors/warnings t)
                                preprocessed
                                preprocessing
                                (macro-init (ienv->version ienv))
                                ienv
                                state
                                (1- limit)))
                   (preprocessed (acons resolved-file pfile preprocessed)))
                (retok pfile
                       preprocessed
                       state)))))
         (preserve-include-p
          (compare-pfiles pfile
                          standalone-pfile
                          (ppstate->macros ppstate)
                          (ppstate->ienv ppstate)))
         (ppstate (update-ppstate->macros
                   (macro-extend file-macros (ppstate->macros ppstate))
                   ppstate))
         (ppstate (if preserve-include-p
                      (add-rev-lexemes
                       (rebuild-include-directive nontoknls-before-hash
                                                  nontoknls-after-hash
                                                  nontoknls-before-header
                                                  header
                                                  nontoknls-after-header
                                                  newline-at-end)
                       ppstate)
                    (expand-include-in-place header
                                             newline-at-end
                                             nil ; file-rev-lexemes
                                             ppstate)))
         (pparts (if preserve-include-p
                     (list
                      (ppart-line
                       (rebuild-include-directive nontoknls-before-hash
                                                  nontoknls-after-hash
                                                  nontoknls-before-header
                                                  header
                                                  nontoknls-after-header
                                                  newline-at-end)))
                   (if (ppoptions->trace-expansion (ppstate->options ppstate))
                       (b* (((mv opening-line closing-line)
                             (expanded-include-comment-lines header
                                                             newline-at-end)))
                         (append (list (ppart-line opening-line))
                                 (pfile->parts pfile)
                                 (list (ppart-line closing-line))))
                     (pfile->parts pfile)))))
      (retok pparts ppstate preprocessed state))
    :no-function nil
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-if ((file stringp)
                    (base-dir stringp)
                    (include-dirs string-listp)
                    (preprocessed string-pfile-alistp)
                    (preprocessing string-listp)
                    (cond-level natp)
                    (ppstate ppstatep)
                    state
                    (limit natp))
    :returns (mv erp
                 (pparts ppart-listp)
                 (new-ppstate ppstatep)
                 (new-preprocessed string-pfile-alistp)
                 state)
    :parents (preprocessor pproc-files/groups/etc)
    :short "Preprocess a @('#if') section."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is for an @('if-section') (see ABNF grammar)
       that starts with @('#if').")
     (xdoc::p
      "This function is called after consuming
       the @('if') identifier of the @('#if').
       Thus, it remains to consume and evaluate the constant expression,
       which we do via @(tsee pproc-const-expr).
       The result of the evaluation, a boolean,
       is passed to @(tsee pproc-if/ifdef/ifndef-rest),
       which preprocesses the rest of the @('if-section').")
     (xdoc::p
      "We perform a header guard transition
       just before preprocessing the rest of the section,
       just after preprocessing the condition."))
    (b* ((ppstate (ppstate-fix ppstate))
         ((reterr) nil ppstate nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         ((erp pexpr condp ppstate) (pproc-const-expr ppstate))
         (ppstate (hg-trans-non-ifndef/elif/else/define ppstate))
         ((erp pparts
               pelifs
               pelse?
               ppstate
               preprocessed
               state)
          (pproc-if/ifdef/ifndef-rest condp
                                      nil ; donep
                                      file
                                      base-dir
                                      include-dirs
                                      preprocessed
                                      preprocessing
                                      cond-level
                                      ppstate
                                      state
                                      (1- limit)))
         (pcond (make-ppart-cond
                 :if (pif-if pexpr)
                 :parts pparts
                 :elifs pelifs
                 :else pelse?))
         (pparts (if (ppoptions->full-expansion (ppstate->options ppstate))
                     (concatenate-cond-bodies pparts pelifs pelse?)
                   (list pcond))))
      (retok pparts ppstate preprocessed state))
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-ifdef/ifndef ((ifdefp booleanp)
                              (file stringp)
                              (base-dir stringp)
                              (include-dirs string-listp)
                              (preprocessed string-pfile-alistp)
                              (preprocessing string-listp)
                              (cond-level natp)
                              (ppstate ppstatep)
                              state
                              (limit natp))
    :returns (mv erp
                 (pparts ppart-listp)
                 (new-ppstate ppstatep)
                 (new-preprocessed string-pfile-alistp)
                 state)
    :parents (preprocessor pproc-files/groups/etc)
    :short "Preprocess a @('#ifdef') or @('#ifndef') section."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is an @('if-section') (see ABNF grammar)
       that starts with @('#ifdef') or @('#ifndef').
       The @('ifdefp') flag passed to this function
       distinguishes @('#ifdef') (if @('t'))
       from @('#ifndef') (if @('nil')).")
     (xdoc::p
      "This function is called after consuming
       the @('ifdef') or @('ifndef') identifier
       of the @('#ifdef') or @('#ifndef').")
     (xdoc::p
      "Thus, it remains to consume the identifier that follows,
       which must form the whole of the rest of the line.
       We look up the identifier in the macro table:
       if it is defined or not defined
       (i.e. we find information for it in the table),
       then the condition evaluates to true or false;
       otherwise, the condition evaluates to false or true.
       We pass the result of the condition
       to @(tsee pproc-if/ifdef/ifndef-rest),
       which preprocesses the rest of the @('if-section')."))
    (b* ((ppstate (ppstate-fix ppstate))
         ((reterr) nil ppstate nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         ((erp & ident? span ppstate) (read-token/newline ppstate))
         ((unless (and ident? ; #ifdef/#ifndef ident
                       (plexeme-case ident? :ident)))
          (reterr-msg :where (position-to-msg (span->start span))
                      :expected "an identifier"
                      :found (plexeme-to-msg ident?)))
         (ident (plexeme-ident->ident ident?))
         ((erp & newline? span ppstate) (read-token/newline ppstate))
         ((unless (and newline? ; #ifdef/#ifndef ident EOL
                       (plexeme-case newline? :newline)))
          (reterr-msg :where (position-to-msg (span->start span))
                      :expected "a new line"
                      :found (plexeme-to-msg ident?)))
         (info? (macro-lookup ident (ppstate->macros ppstate)))
         (condp (if ifdefp
                    (and info? t)
                  (not info?)))
         (ppstate (if ifdefp
                      (hg-trans-non-ifndef/elif/else/define ppstate)
                    (hg-trans-ifndef ident ppstate)))
         ((erp pparts
               pelifs
               pelse?
               ppstate
               preprocessed
               state)
          (pproc-if/ifdef/ifndef-rest condp
                                      nil ; donep
                                      file
                                      base-dir
                                      include-dirs
                                      preprocessed
                                      preprocessing
                                      cond-level
                                      ppstate
                                      state
                                      (1- limit)))
         (pcond (make-ppart-cond
                 :if (if ifdefp
                         (pif-ifdef ident)
                       (pif-ifndef ident))
                 :parts pparts
                 :elifs pelifs
                 :else pelse?))
         (pparts (if (ppoptions->full-expansion (ppstate->options ppstate))
                     (concatenate-cond-bodies pparts pelifs pelse?)
                   (list pcond))))
      (retok pparts ppstate preprocessed state))
    :no-function nil
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-if/ifdef/ifndef-rest ((condp booleanp)
                                      (donep booleanp)
                                      (file stringp)
                                      (base-dir stringp)
                                      (include-dirs string-listp)
                                      (preprocessed string-pfile-alistp)
                                      (preprocessing string-listp)
                                      (cond-level natp)
                                      (ppstate ppstatep)
                                      state
                                      (limit natp))
    :returns (mv erp
                 (pparts ppart-listp)
                 (pelifs pelif-listp)
                 (pelse? pelse-optionp)
                 (new-ppstate ppstatep)
                 (new-preprocessed string-pfile-alistp)
                 state)
    :parents (preprocessor pproc-files/groups/etc)
    :short "Preprocess the rest of
            a @('#if'), @('#ifdef'), or @('#ifndef') section."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after preprocessing
       the first line of an @('if-section'), as defined by the grammar,
       i.e. after preprocessing the directive line with
       the @('#if'), @('#ifdef'), or @('#ifndef').
       That directive is preprocessed by
       @(tsee pproc-if) or @(tsee pproc-ifdef/ifndef),
       which evaluate the condition to a boolean,
       which is passed to this function as the @('condp') input,
       i.e. the value of the latest condition.
       This function also takes an input @('donep') which says whether
       we are done preprocessing the part of the @('if-section')
       corresponding to a true condition;
       this is initially @('nil'),
       but it may become @('t') in recursive calls of this function.")
     (xdoc::p
      "The recursive structure of this function
       matches the recursive structure of
       the @('elif-group')s in the @('if-section').")
     (xdoc::p
      "We preprocess zero or more group parts,
       via @(tsee pproc-*-group-part) or @(tsee pproc-*-group-part-skipped)
       based on whether this is the code to include or not:
       if the condition is true,
       and we have not already included the code,
       then we use @(tsee pproc-*-group-part);
       otherwise we use @(tsee pproc-*-group-part-skipped).
       Note that multiple conditions in an @('if-section') may be true,
       but only the first one counts:
       this is why we need the @('donep') flag,
       which becomes @('t') after the first true condition.")
     (xdoc::p
      "After preprocessing the optional group (with either function),
       we look at how the group ended.
       If it ended with end of file, it is an error.
       If it ended with @('#elif'),
       we preprocess the constant expression that follows,
       and then we recursively call this function,
       with the possibly updated @('donep').
       If it ended with @('#else'),
       we ensure that it is immediately followed by a new line
       (except for possibly some comments and white space),
       we preprocess another optional group,
       and then we ensure that we find a @('#endif') after that;
       for the optional group after the @('#else'),
       we use the skipping function unless
       @('donep') is still false.
       Finally, if the group instead with @('#endif'),
       we ensure there is just a new line after that."))
    (b* ((ppstate (ppstate-fix ppstate))
         ((reterr) nil nil nil ppstate nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         ((erp first-pparts groupend ppstate preprocessed state)
          (b* (((reterr) nil (irr-groupend) ppstate nil state))
            (if (and condp
                     (not donep))
                (pproc-*-group-part file
                                    base-dir
                                    include-dirs
                                    preprocessed
                                    preprocessing
                                    cond-level
                                    ppstate
                                    state
                                    (1- limit))
              (b* (((erp groupend ppstate)
                    (pproc-*-group-part-skipped ppstate)))
                (retok nil ; no group parts
                       groupend
                       ppstate
                       (string-pfile-alist-fix preprocessed)
                       state)))))
         (donep (and condp (not donep))))
      (groupend-case
       groupend
       :eof (reterr-msg :where (position-to-msg (ppstate->position ppstate))
                        :expected "a #elif or a #else or a #endif"
                        :found "end of file")
       :elif (b* (((erp pexpr condp ppstate) ; #elif constexpr EOL
                   (pproc-const-expr ppstate))
                  (ppstate (hg-trans-elif/else cond-level ppstate))
                  ((erp pparts
                        pelifs
                        pelse?
                        ppstate
                        preprocessed
                        state)
                   (pproc-if/ifdef/ifndef-rest condp
                                               donep
                                               file
                                               base-dir
                                               include-dirs
                                               preprocessed
                                               preprocessing
                                               cond-level
                                               ppstate
                                               state
                                               (1- limit))))
               (retok first-pparts
                      (cons (make-pelif :expr pexpr
                                        :parts pparts)
                            pelifs)
                      pelse?
                      ppstate
                      preprocessed
                      state))
       :else (b* (((erp & toknl span ppstate) (read-token/newline ppstate))
                  ((unless (and toknl ; #else EOL
                                (plexeme-case toknl :newline)))
                   (reterr-msg :where (position-to-msg (span->start span))
                               :expected "a new line"
                               :found (plexeme-to-msg toknl)))
                  (ppstate (hg-trans-elif/else cond-level ppstate))
                  ((erp pparts groupend ppstate preprocessed state)
                   (b* (((reterr) nil (irr-groupend) ppstate nil state))
                     (if (not donep)
                         (pproc-*-group-part file
                                             base-dir
                                             include-dirs
                                             preprocessed
                                             preprocessing
                                             cond-level
                                             ppstate
                                             state
                                             (1- limit))
                       (b* (((erp groupend ppstate)
                             (pproc-*-group-part-skipped ppstate)))
                         (retok nil groupend ppstate preprocessed state)))))
                  ((unless (groupend-case groupend :endif)) ; #endif
                   (reterr-msg :where (position-to-msg
                                       (ppstate->position ppstate))
                               :expected "a #endif"
                               :found (case (groupend-kind groupend)
                                        (:eof "end of file")
                                        (:elif "a #elif")
                                        (:else "a #else"))))
                  ((erp & toknl span ppstate) (read-token/newline ppstate))
                  ((unless (and toknl ; #endif EOL
                                (plexeme-case toknl :newline)))
                   (reterr-msg :where (position-to-msg (span->start span))
                               :expected "a new line"
                               :found (plexeme-to-msg toknl))))
               (retok first-pparts
                      nil ; pelifs
                      (pelse pparts)
                      ppstate
                      preprocessed
                      state))
       :endif (b* (((erp & toknl span ppstate) (read-token/newline ppstate))
                   ((unless (and toknl ; #endif EOL
                                 (plexeme-case toknl :newline)))
                    (reterr-msg :where (position-to-msg (span->start span))
                                :expected "a new line"
                                :found (plexeme-to-msg toknl)))
                   (ppstate (hg-trans-endif cond-level ppstate)))
                (retok first-pparts
                       nil ; pelifs
                       nil ; pelse?
                       ppstate
                       preprocessed
                       state))))
    :no-function nil
    :measure (nfix limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :prepwork ((local
              (in-theory
               (enable
                acons
                pfilep-of-cdr-of-assoc-equal-when-string-pfile-alistp))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  :guard-hints
  (("Goal" :in-theory (enable alistp-when-string-pfile-alistp-rewrite
                              true-listp-when-plexeme-listp
                              true-listp-when-ppart-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pproc-files ((files string-listp)
                     (base-dir stringp)
                     (include-dirs string-listp)
                     (options ppoptionsp)
                     (ienv ienvp)
                     state
                     (recursion-limit natp))
  :returns (mv erp (preprocessed string-pfile-alistp) state)
  :short "Preprocess zero or more files."
  :long
  (xdoc::topstring
   (xdoc::p
    "The files are identified by the @('files') strings,
     which must be paths relative to the @('base-dir') string path:
     this is the same interface as @(tsee input-files).
     The list @('include-dirs') specifies the directories to search
     for @('#include') directives with angle brackets.
     The input to this function come directly from @(tsee preprocess),
     except for the recursion limit
     (discussed in @(tsee pproc-files/groups/etc)),
     which is set there.")
   (xdoc::p
    "The elements of @('files') are preprocessed in order.
     Each file is read from the file system,
     preprocessed via @(tsee pproc-file),
     and added to the @('preprocessed') alist.
     It is possible for a file in @('files')
     to @('#include') another file in @('files'),
     which, as explained in @(see preservable-inclusions),
     causes the second file to be re-processed afresh
     to see whether the @('#include') can be preserved.
     If this happens before the loop below considers the second file,
     the file will be already in the @('preprocessed') alist,
     so it does not need to be added.
     Note that the resulting @(tsee pfile) cannot differ,
     because all the files in @('files'), in the loop below,
     are preprocessed afresh, i.e. with only the predefined macros.")
   (xdoc::p
    "We keep track of the files under preprocessing in a list (initially empty),
     to detect and avoid circularities.")
   (xdoc::p
    "The result of this function is an alist of @(tsee pfile)s,
     whose keys are generally a superset of the input file names,
     as already explained in @(see preprocessor)."))
  (pproc-files-loop files
                    base-dir
                    include-dirs
                    options
                    nil ; preprocessed
                    nil ; preprocessing
                    ienv
                    state
                    recursion-limit)
  :hooks nil

  :prepwork
  ((define pproc-files-loop ((files string-listp)
                             (base-dir stringp)
                             (include-dirs string-listp)
                             (options ppoptionsp)
                             (preprocessed string-pfile-alistp)
                             (preprocessing string-listp)
                             (ienv ienvp)
                             state
                             (recursion-limit natp))
     :returns (mv erp (new-preprocessed string-pfile-alistp) state)
     :parents nil
     (b* (((reterr) nil state)
          ((when (endp files))
           (retok (string-pfile-alist-fix preprocessed) state))
          (file (str-fix (car files)))
          (path-to-read (str::cat base-dir "/" file))
          ((mv erp bytes state)
           (acl2::read-file-into-byte-list path-to-read state))
          ((when erp)
           (reterr (msg "Cannot read file ~x0." path-to-read)))
          ((erp pfile
                & ; file-macros
                preprocessed
                state)
           (pproc-file bytes
                       (car files)
                       base-dir
                       include-dirs
                       options
                       preprocessed
                       preprocessing
                       (macro-init (ienv->version ienv))
                       ienv
                       state
                       recursion-limit))
          (preprocessed (string-pfile-alist-fix preprocessed))
          (preprocessed (if (assoc-equal file preprocessed)
                            preprocessed
                          (acons file pfile preprocessed))))
       (pproc-files-loop (cdr files)
                         base-dir
                         include-dirs
                         options
                         preprocessed
                         preprocessing
                         ienv
                         state
                         recursion-limit))
     :no-function nil
     :guard-hints
     (("Goal" :in-theory (enable alistp-when-string-pfile-alistp-rewrite)))
     :prepwork ((local (in-theory (enable acons))))
     :hooks nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define preprocess ((files string-listp)
                    (base-dir stringp)
                    (include-dirs string-listp)
                    (options ppoptionsp)
                    (ienv ienvp)
                    state)
  :returns (mv erp (fileset filesetp) state)
  :short "Preprocess files into a file set."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level function of the preprocessor.
     It is called by @(tsee input-files)
     when the option for the internal preprocessor is selected;
     the inputs to this function come directly from @(tsee input-files),
     which lets the user specify them.")
   (xdoc::p
    "We call @(tsee pproc-files) with a recursion limit of 1,000,000,000,
     which should be normally sufficient.
     We convert the resulting alist into a file set."))
  (b* (((reterr) (irr-fileset) state)
       ((erp preprocessed state) (pproc-files files
                                              base-dir
                                              include-dirs
                                              options
                                              ienv
                                              state
                                              1000000000)))
    (retok (fileset
            (string-pfile-alist-to-filepath-filedata-map preprocessed))
           state))
  :hooks nil)
