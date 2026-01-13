; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "preprocessor-states")
(include-book "preprocessor-messages")
(include-book "preprocessor-reader")
(include-book "preprocessor-lexer")
(include-book "preprocessor-printer")
(include-book "files")

(include-book "kestrel/file-io-light/read-file-into-byte-list" :dir :system)
(include-book "std/strings/strpos" :dir :system)
(include-book "std/strings/strrpos" :dir :system)

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration :hooks nil)

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
  :order-subtopics (preprocessor-states
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

(define read-lexeme ((headerp booleanp) (ppstate ppstatep))
  :returns (mv erp
               (lexeme? plexeme-optionp)
               (span spanp)
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex a lexeme during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level function of the lexer.
     If there are pending lexmarks,
     we return the first one if it is a lexeme
     (and throw an error if it is a marker, for now).
     If there are no pending lexmarks,
     we call @(tsee plex-lexeme) to read a lexeme from the input."))
  (b* (((reterr) nil (irr-span) ppstate)
       (lexmarks (ppstate->lexmarks ppstate))
       (size (ppstate->size ppstate))
       ((when (consp lexmarks))
        (b* ((lexmark (car lexmarks))
             ((unless (lexmark-case lexmark :lexeme))
              (raise "Internal error: unexpected marker ~x0." lexmark)
              (reterr t))
             (lexeme+span (lexmark-lexeme->lexspan lexmark))
             ((unless (> size 0))
              (raise "Internal error: size is 0 but there are pending lexemes.")
              (reterr t))
             (ppstate (update-ppstate->size (1- size) ppstate))
             (ppstate (update-ppstate->lexmarks (cdr lexmarks) ppstate)))
          (retok (plexeme+span->lexeme lexeme+span)
                 (plexeme+span->span lexeme+span)
                 ppstate)))
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

(define pread-token ((headerp booleanp) (ppstate ppstatep))
  :returns (mv erp
               (nontokens plexeme-listp)
               (token? plexeme-optionp)
               (token-span spanp)
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Read a token during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "We lex zero or more non-tokens, until we find a token.
     We return the list of non-tokens, and the token with its span.
     If we reach the end of file, we return @('nil') as the token,
     and a span consisting of just the current position.")
   (xdoc::p
    "The @('headerp') flag has the same meaning as in @(tsee plex-lexeme):
     see that function's documentation."))
  (b* (((reterr) nil nil (irr-span) ppstate)
       ((erp lexeme span ppstate) (read-lexeme headerp ppstate))
       ((when (not lexeme)) (retok nil nil span ppstate))
       ((when (plexeme-tokenp lexeme)) (retok nil lexeme span ppstate))
       ((erp nontokens token token-span ppstate) (pread-token headerp ppstate)))
    (retok (cons lexeme nontokens) token token-span ppstate))
  :measure (ppstate->size ppstate)

  ///

  (defret plexeme-list-not-tokenp-of-pread-token
    (plexeme-list-not-tokenp nontokens)
    :hints (("Goal" :induct t)))

  (defret plexeme-tokenp-of-pread-token
    (implies token?
             (plexeme-tokenp token?))
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-pread-token-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-pread-token-cond
    (implies (and (not erp)
                  token?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pread-token/newline ((headerp booleanp) (ppstate ppstatep))
  :returns (mv erp
               (nontoknls plexeme-listp)
               (toknl? plexeme-optionp)
               (toknl-span spanp)
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Read a token or new line during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "New lines are significant in most situations during preprocessing,
     i.e. they are not just white space to skip over.
     In such situations,
     we need to skip over non-new-line white space and comments,
     but stop when we encounter either a new line or a token.
     As explained in @(tsee plexeme-token/newline-p),
     line comments count as new lines,
     because conceptually each comment is replaced by a single space character
     before preprocessing [C17:5.1.1.2/1],
     and the new line that ends a line comment
     is not part of the comment [C17:6.4.9/2]:
     thus, a line comment must be treated like a space followed by new line."))
  (b* (((reterr) nil nil (irr-span) ppstate)
       ((erp lexeme span ppstate) (read-lexeme headerp ppstate))
       ((when (not lexeme)) (retok nil nil span ppstate))
       ((when (plexeme-token/newline-p lexeme)) (retok nil lexeme span ppstate))
       ((erp nontoknls toknl toknl-span ppstate)
        (pread-token/newline headerp ppstate)))
    (retok (cons lexeme nontoknls)
           toknl
           toknl-span
           ppstate))
  :measure (ppstate->size ppstate)

  ///

  (defret plexeme-list-not-token/newline-p-of-pread-token/newline
    (plexeme-list-not-token/newline-p nontoknls)
    :hints (("Goal" :induct t)))

  (defret plexeme-token/newline-p-of-pread-token/newline
    (implies token?
             (plexeme-token/newline-p toknl?))
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-pread-token/newline-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-pread-token/newline-cond
    (implies (and (not erp)
                  toknl?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define punread-lexeme ((lexeme plexemep) (span spanp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep :hyp (ppstatep ppstate))
  :short "Unread a lexeme."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add the lexeme to the list of pending lexmarks.
     See @(tsee ppstate)."))
  (b* ((lexmarks (ppstate->lexmarks ppstate))
       (size (ppstate->size ppstate))
       (lexmark (lexmark-lexeme (make-plexeme+span :lexeme lexeme :span span)))
       (ppstate (update-ppstate->lexmarks (cons lexmark lexmarks) ppstate))
       (ppstate (update-ppstate->size (1+ size) ppstate)))
    ppstate)
  :no-function nil

  ///

  (defret ppstate->size-of-punread-lexeme
    (equal (ppstate->size new-ppstate)
           (1+ (ppstate->size ppstate)))))

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
       (eql (char path 0) #\/)))

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
  :guard-hints (("Goal" :in-theory (enable length string-append)))
  :no-function nil)

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
    :enable assoc-equal))

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
       ((cons string scfile) (car alist))
       (bytes (plexemes-to-bytes (scfile->lexemes scfile)))
       (filepath (filepath string))
       (filedata (filedata bytes))
       (map (string-scfile-alist-to-filepath-filedata-map (cdr alist))))
    (omap::update filepath filedata map))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pproc
  :short "Preprocess files."
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
    :parents (preprocessor pproc)
    :short "Preprocess a file."
    :long
    (xdoc::topstring
     (xdoc::p
      "The bytes contained in the file are passed to this function.
       The file itself is read by the callers,
       namely @(tsee pproc-files) and @(tsee pproc-include-directive).")
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
       that results in this call of @(tsee pproc-file).")
     (xdoc::p
      "If the file is in the @('preprocessed') alist,
       we avoid re-preprocessing it:
       we leave @('preprocessed') unchanged,
       and we return the @(tsee scfile) from the alist.")
     (xdoc::p
      "Otherwise, we create a local preprocessing state stobj from
       the bytes of the file,
       a file recursion limit of 200 (consistent with GCC),
       the macro table
       (which @(tsee init-ppstate) extends with a new empty scope for the file),
       and the implementation environment.
       The preprocessing of this file may involve
       the recursive preprocessing of more files,
       and the consequent extension of the @('preprocessed') alist.
       If the file is not self-contained,
       @(tsee pproc-*-group-part) will return @(':not-self-contained')
       (see @(tsee pproc)),
       which this function also returns;
       the caller handles that.
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
         ((when (member-equal file preprocessing))
          (reterr (msg "Circular file dependencies involving ~&0."
                       preprocessing)))
         (preprocessing (cons file preprocessing))
         (preprocessed (string-scfile-alist-fix preprocessed))
         (name+scfile (assoc-equal file preprocessed))
         ((when name+scfile) (retok (cdr name+scfile) preprocessed state))
         ((erp lexemes macros preprocessed state)
          (with-local-stobj
            ppstate
            (mv-let (erp rev-lexemes macros ppstate preprocessed state)
                (b* ((ppstate
                      (init-ppstate bytes
                                    200
                                    (macro-table-fix macros)
                                    ienv
                                    ppstate))
                     ((mv erp rev-lexemes ppstate preprocessed state)
                      (pproc-*-group-part file
                                          base-dir
                                          include-dirs
                                          preprocessed
                                          preprocessing
                                          nil
                                          ppstate
                                          state
                                          (1- limit))))
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
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-scfile-alistp)
                 state)
    :parents (preprocessor pproc)
    :short "Preprocess zero or more group parts."
    :long
    (xdoc::topstring
     (xdoc::p
      "According to the grammar,
       a preprocessing file consists of zero or more group parts.
       Each group part ends with a new line,
       and non-empty files must end with a new line [C17:5.1.1.2/1, phase 4].
       Thus, we can detect whether there is a group part or not
       by checking for end of file
       (this may need to be relaxed at some point,
       since GCC is more lenient on this front)."))
    (b* (((reterr) nil ppstate nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         ((when (= (ppstate->size ppstate) 0)) ; EOF
          (retok (plexeme-list-fix rev-lexemes)
                 ppstate
                 (string-scfile-alist-fix preprocessed)
                 state))
         ((erp rev-lexemes ppstate preprocessed state) ; group-part
          (pproc-group-part file
                            base-dir
                            include-dirs
                            preprocessed
                            preprocessing
                            rev-lexemes
                            ppstate
                            state
                            (1- limit))))
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

  (define pproc-group-part ((file stringp)
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
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-scfile-alistp)
                 state)
    :parents (preprocessor pproc)
    :short "Preprocess a group part."
    :long
    (xdoc::topstring
     (xdoc::p
      "We read the next token or new line,
       skipping over white space and comments.
       If we find no token or new line, it is an error,
       because it means that the file has some white space or comments
       without a terminating new line;
       this function is called (by @(tsee pproc-*-group-part))
       only if we are not at the end of file.")
     (xdoc::p
      "If we find a hash, we have a directive,
       which we handle in a separate function,
       to which we pass the white space and comments before the hash.")
     (xdoc::p
      "If we do not find a hash, we have a text line.
       We add any preceding white space and comments to the growing lexemes,
       and we call a separate function to handle the rest of the line,
       after putting the non-hash lexeme back."))
    (b* (((reterr) nil ppstate nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         ((erp nontoknls toknl span ppstate) (pread-token/newline nil ppstate)))
      (cond
       ((not toknl) ; EOF
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a token or new line"
                    :found (plexeme-to-msg toknl)))
       ((plexeme-hashp toknl) ; #
        (pproc-directive nontoknls
                         file
                         base-dir
                         include-dirs
                         preprocessed
                         preprocessing
                         rev-lexemes
                         ppstate
                         state
                         (1- limit)))
       (t ; non-#
        (b* ((rev-lexemes (revappend nontoknls (plexeme-list-fix rev-lexemes)))
             (ppstate (punread-lexeme toknl span ppstate)))
          (pproc-line-rest file
                           base-dir
                           include-dirs
                           preprocessed
                           preprocessing
                           rev-lexemes
                           ppstate
                           state
                           (1- limit))))))
    :measure (nfix limit)
    :no-function nil)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-directive ((nontoknls-before-hash plexeme-listp)
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
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-scfile-alistp)
                 state)
    :parents (preprocessor pproc)
    :short "Preprocess a directive."
    :long
    (xdoc::topstring
     (xdoc::p
      "With reference to the grammar,
       a directive is a group part that starts with @('#');
       this function is called just after the @('#') has been encountered,
       possibly preceded by comments and white space,
       which are passed as the @('nontoknls-before-hash') parameter.
       A directive may be an @('if') group (which may span multiple lines),
       a control line (which spans one line),
       or a non-directive (which spans one line);
       the latter, despite the name, is considered a directive
       (see footnote 175 in [C17:6.10.3/11]).")
     (xdoc::p
      "We read the next token or new line, and dispatch accordingly.
       Although [C17:6.10/5] only allows spaces and horizontal tabs
       as white space within preprocessing directives,
       [C17:5.1.1.2/1] in phase 3 (which precedes preprocessing, i.e. phase 4)
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
       Thus, the use of @(tsee pread-token/newline) is justified here.")
     (xdoc::p
      "If we find no token or new line, it is an error.")
     (xdoc::p
      "If we find a new line, we have the null directive [C17:6.10.7].
       We leave the line as is,
       but we wrap the @('#') into a (small) block comment.")
     (xdoc::p
      "If we find an identifier,
       we check to see if it is the name of a known directive,
       and we handle the directive accordingly if that is the case.
       If it is not a directive name, or if it is not even an identifier,
       we have a non-directive [C17:6.10/9],
       which renders the behavior undefined;
       we stop with an error in this case.
       (We may extend this in the future,
       e.g. to accommodate non-standard directives.)"))
    (b* (((reterr) nil ppstate nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         ((erp nontoknls-after-hash toknl span ppstate)
          (pread-token/newline nil ppstate)))
      (cond
       ((not toknl) ; # EOF
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a token or new line"
                    :found (plexeme-to-msg toknl)))
       ((or (plexeme-case toknl :newline) ; # EOL
            (plexeme-case toknl :line-comment)) ; # // ... EOL
        ;; null directive
        (b* ((nontoknls-before-hash (plexeme-list-fix nontoknls-before-hash))
             (rev-lexemes (plexeme-list-fix rev-lexemes))
             (rev-lexemes (revappend nontoknls-before-hash rev-lexemes))
             (rev-lexemes (cons (plexeme-block-comment (list (char-code #\#)))
                                rev-lexemes))
             (rev-lexemes (revappend nontoknls-after-hash rev-lexemes))
             (rev-lexemes (cons toknl ; toknl is new line or line comment
                                rev-lexemes)))
          (retok rev-lexemes
                 ppstate
                 (string-scfile-alist-fix preprocessed)
                 state)))
       ((plexeme-case toknl :ident) ; # ident
        (b* ((dirname (ident->unwrap (plexeme-ident->ident toknl))))
          (cond
           ((equal dirname "if") ; # if
            (reterr (msg "#if directive not yet supported."))) ; TODO
           ((equal dirname "ifdef") ; # ifdef
            (reterr (msg "#ifdef directive not yet supported."))) ; TODO
           ((equal dirname "ifndef") ; # ifndef
            (reterr (msg "#ifndef directive not yet supported."))) ; TODO
           ((equal dirname "include") ; # include
            (pproc-include-directive nontoknls-before-hash
                                     nontoknls-after-hash
                                     file
                                     base-dir
                                     include-dirs
                                     preprocessed
                                     preprocessing
                                     rev-lexemes
                                     ppstate
                                     state
                                     (1- limit)))
           ((equal dirname "define") ; # define
            (reterr (msg "#define directive not yet supported."))) ; TODO
           ((equal dirname "undef") ; # undef
            (reterr (msg "#undef directive not yet supported."))) ; TODO
           ((equal dirname "line") ; # line
            (reterr (msg "#line directive not yet supported."))) ; TODO
           ((equal dirname "error") ; # error
            (reterr (msg "#error directive not yet supported."))) ; TODO
           ((equal dirname "pragma") ; # pragma
            (reterr (msg "#pragma directive not yet supported."))) ; TODO
           (t ;  # non-directive
            (reterr-msg :where (span->start span)
                        :expected "a directive name among ~
                                   'if', ~
                                   'ifdef', ~
                                   'ifndef', ~
                                   'include', ~
                                   'define', ~
                                   'undef', ~
                                   'line', ~
                                   'error', and ~
                                   'pragma'"
                        :found (plexeme-to-msg toknl))))))
       (t ; # non-directive
        (reterr-msg :where (span->start span)
                    :expected "a directive name among ~
                               'if', ~
                               'ifdef', ~
                               'ifndef', ~
                               'include', ~
                               'define', ~
                               'undef', ~
                               'line', ~
                               'error', and ~
                               'pragma'"
                    :found (plexeme-to-msg toknl)))))
    :measure (nfix limit)
    :no-function nil)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-include-directive ((nontoknls-before-hash plexeme-listp)
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
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-scfile-alistp)
                 state)
    :parents (preprocessor pproc)
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
       (see documentation of @(tsee unread-char-to-bytes)),
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
    (b* (((reterr) nil ppstate nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         ((erp nontoknls-before-header toknl span ppstate)
          (pread-token/newline t ppstate)))
      (cond
       ((not toknl) ; # include EOF
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a token"
                    :found (plexeme-to-msg toknl)))
       ((or (plexeme-case toknl :newline) ; # include EOL
            (plexeme-case toknl :line-comment)) ; # include // ... EOL
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a token"
                    :found (plexeme-to-msg toknl)))
       ((plexeme-case toknl :header) ; # include headername
        (b* (((erp nontoknls-after-header toknl2 span2 ppstate)
              (pread-token/newline nil ppstate))
             ((unless (and toknl2
                           (or (plexeme-case toknl2 :newline)
                               ;; # include EOL
                               (plexeme-case toknl2 :line-comment)
                               ;; # include // ... EOL
                               )))
              (reterr-msg :where (position-to-msg (span->start span2))
                          :expected "a new line or line comment"
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
              (b* ((ppstate (unread-char-to-bytes ppstate))
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
             (rev-lexemes (cons toknl2 ; toknl2 is new line or line comment
                                rev-lexemes)))
          (retok rev-lexemes ppstate preprocessed state)))
       (t ; # include token
        (reterr (msg "Non-direct #include not yet supported."))))) ; TODO
    :measure (nfix limit)
    :no-function nil)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-line-rest ((file stringp)
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
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-scfile-alistp)
                 state)
    :parents (preprocessor pproc)
    :short "Preprocess the rest of a line."
    :long
    (xdoc::topstring
     (xdoc::p
      "We read the next token or new line,
       adding any preceding white space and comments to the growing list.")
     (xdoc::p
      "If we find no token or new line, it is an error,
       because there must be a full line.")
     (xdoc::p
      "If we find a new line (or line comment),
       we add it to the growing list,
       and we return, because we have finished preprocessing the line.")
     (xdoc::p
      "If we find an identifier, we look it up in the macro table.
       If we find it in a scope that is not the innermost,
       it means that the file is not self-contained,
       and so we abort the preprocessing by returning @(':not-self-contained'),
       as explained in @(tsee pproc).
       If the macro is predefined or found in the innermost scope,
       it should be expanded in place, which we plan to do soon.
       If no macro is found,
       it must be an identifier that passes through preprocessing:
       it is added to the growing list,
       we read the next token,
       and we recursively call this function.")
     (xdoc::p
      "All the other kinds of tokens also pass through preprocessing,
       in the same way as an identifier that is not a macro name."))
    (b* (((reterr) nil ppstate nil state)
         ((when (zp limit)) (reterr (msg "Exhausted recursion limit.")))
         ((erp nontoknls toknl span ppstate) (pread-token/newline nil ppstate))
         (rev-lexemes (revappend nontoknls (plexeme-list-fix rev-lexemes))))
      (cond
       ((not toknl) ; EOF
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a token or new line"
                    :found (plexeme-to-msg toknl)))
       ((or (plexeme-case toknl :newline) ; # EOL
            (plexeme-case toknl :line-comment)) ; # // ... EOL
        (retok (cons toknl rev-lexemes)
               ppstate
               (string-scfile-alist-fix preprocessed)
               state))
       ((plexeme-case toknl :ident) ; ident
        (b* (((mv info? innermostp predefinedp)
              (macro-lookup (plexeme-ident->ident toknl)
                            (ppstate->macros ppstate)))
             ((when (not info?)) ; regular identifier
              (b* ((rev-lexemes (cons toknl rev-lexemes)))
                (pproc-line-rest file
                                 base-dir
                                 include-dirs
                                 preprocessed
                                 preprocessing
                                 rev-lexemes
                                 ppstate
                                 state
                                 (1- limit))))
             ((when (and (not innermostp)
                         (not predefinedp)))
              (reterr :not-self-contained)))
          (reterr (msg "Macro expansion not yet supported."))))
       (t ; non-ident-token
        (b* ((rev-lexemes (cons toknl rev-lexemes)))
          (pproc-line-rest file
                           base-dir
                           include-dirs
                           preprocessed
                           preprocessing
                           rev-lexemes
                           ppstate
                           state
                           (1- limit))))))
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
    "The recursion limit is discussed in @(tsee pproc).
     It seems best to let the user set this limit (outside this function),
     with perhaps a reasonably large default."))
  (b* (((reterr) (irr-fileset) state)
       ((erp preprocessed state)
        (pproc-files-loop files base-dir include-dirs
                          nil nil ienv state recursion-limit)))
    (retok
     (fileset (string-scfile-alist-to-filepath-filedata-map preprocessed))
     state))

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
     :no-function nil)))
