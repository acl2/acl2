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
(include-book "implementation-environments")

(include-book "kestrel/file-io-light/read-file-into-byte-list" :dir :system)

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
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
     in certain common cases.
     That is, it does not replace such directives
     with the (preprocessed) contents of the referenced files,
     but it otherwise performs the rest of the preprocessing.
     This is only done under certain (common) conditions;
     in general, the C preprocessor operates at a low lexical level,
     making it difficult to preserve code structure in general
     (in those cases, our preprocessor expands the included files in place).")
   (xdoc::p
    "Our preprocessor maps a list of file paths
     to a file set (see @(see files)):
     it preprocesses all the files with the given file paths,
     as well as all the files directly and indirectly included.
     The resulting file set contains entries
     for all the files with the given file paths,
     as well as for zero or more @(see self-contained) files.")
   (xdoc::p
    "Our preprocessor reads characters,
     lexes them into lexemes,
     and parses the lexemes while executing the preprocessing directives.
     The resulting sequence of lexemes is then turned into characters
     that are written (printed) to files.
     The resulting file set is amenable to our parser
     (more precisely, it will be, once we have extended our parser
     to accept @('#include') directives in certain places).
     Our preprocessor preserves white space and comments when possible,
     but some layout (i.e. white space) changes are inherent to preprocessing,
     some comments may be impossible to preserve
     (e.g. if they occur within macro parameters),
     and some comments may no longer apply to preprocessed code
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
     because those details do not matter.")
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
    "However, the situation above is often not the case.
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
     to the file set returned as result of preprocessing a list of files,
     specified by name (see @(see preprocessor)).
     This is why, in addition to one element for each specified file,
     our preprocessor also returns zero or more additional elements
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
     is still work in progress.
     It will be described more precisely as we advance the implementation.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
       ((erp lexeme span ppstate) (plex-lexeme headerp ppstate))
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
       ((erp lexeme span ppstate) (plex-lexeme headerp ppstate))
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

(define punread-token ((ppstate ppstatep))
  :returns (new-ppstate ppstatep :hyp (ppstatep ppstate))
  :short "Unread a token."
  :long
  (xdoc::topstring
   (xdoc::p
    "We move the token from the sequence of read lexemes
     to the sequence of unread lexemes.
     See @(tsee ppstate).")
   (xdoc::p
    "It is an internal error if @('lexemes-read') is 0.
     It means that the calling code is wrong.
     In this case, after raising the hard error,
     logically we still increment @('lexemes-read')
     so that the theorem about @(tsee ppstate->size) holds unconditionally."))
  (b* ((ppstate.lexemes-read (ppstate->lexemes-read ppstate))
       (ppstate.lexemes-unread (ppstate->lexemes-unread ppstate))
       (ppstate.size (ppstate->size ppstate))
       ((unless (> ppstate.lexemes-read 0))
        (raise "Internal error: no token to unread.")
        (b* ((ppstate (update-ppstate->lexemes-unread
                       (1+ ppstate.lexemes-unread) ppstate))
             (ppstate (update-ppstate->size (1+ ppstate.size) ppstate)))
          ppstate))
       (ppstate (update-ppstate->lexemes-unread
                 (1+ ppstate.lexemes-unread) ppstate))
       (ppstate (update-ppstate->lexemes-read
                 (1- ppstate.lexemes-read) ppstate))
       (ppstate (update-ppstate->size (1+ ppstate.size) ppstate)))
    ppstate)
  :no-function nil

  ///

  (defret ppstate->size-of-punread-token
    (equal (ppstate->size new-ppstate)
           (1+ (ppstate->size ppstate)))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-input-file-to-preprocess ((path stringp) (file stringp) state)
  :returns (mv erp (bytes byte-listp) state)
  :short "Read a file to preprocess, explicitly specified as user input."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for the files
     whose paths are explicitly passed to @(tsee pproc-files).
     We concatenate the path prefix (passed to @(tsee pproc-files))
     to the file path suffix,
     with a slash in between (this is for Unix-like systems).
     We read the bytes from the file system, and return them."))
  (b* (((reterr) nil state)
       (path-to-read (str::cat path "/" file))
       ((mv erp bytes state)
        (acl2::read-file-into-byte-list path-to-read state))
       ((when erp)
        (reterr (msg "Reading ~x0 failed." path-to-read))))
    (retok bytes state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-included-file-to-preprocess ((path stringp)
                                          (file stringp)
                                          (hname header-namep)
                                          state)
  :returns (mv erp (bytes byte-listp) state)
  :short "Read a file to preprocess,
          referenced via a header name in an @('#include') directive."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('path') and @('file') parameters of this function are
     the ones for the including file,
     i.e. the one that contains the @('#include') directive,
     since they may participate in the resolution of
     the header name to a file in the file system.
     If @('path') is the empty string, @('file') is an absolute path;
     this is the case for library files.
     Otherwise, @('file') is a path relative to @('path'),
     with the latter absolute or relative
     (if relative, it is so with respect to the "
    (xdoc::seetopic "cbd" "connected book directory")
    ".")
   (xdoc::p
    "[C17:6.10.2] gives leeway in how header names
     are resolved to files in the file system.
     Roughly and informally speaking, one could perhaps say that
     header names with angle brackets resolve to ``library files'',
     while header names with double quotes resolve to ``application files'';
     the latter would often be files within the same file system subtree
     where the including file resides.
     GCC uses the strategy described in "
    (xdoc::ahref "https://gcc.gnu.org/onlinedocs/cpp/Search-Path.html"
                 "[CPPM:2.3]")
    ".")
   (xdoc::p
    "We start with a very simple strategy in our preprocessor
     For header names in double quotes,
     we form a full path from @('path') and the header name.
     When the header name is just a file name without directories,
     and when @('file') is also just a file name without directories,
     this strategy correspond to the idea of finding the included file
     relative to the directory where the including file is, as in [CPPM:2.3].
     This is very preliminary, and we will refine it.
     We will also add suitable support for header names with angle brackets,
     possibly via a user-supplied list of paths containing ``library files''."))
  (declare (ignore file))
  (b* (((reterr) nil state)
       ((erp path-to-read)
        (b* (((reterr) ""))
          (header-name-case
           hname
           :angles (reterr :todo)
           :quotes (b* (((erp name) (q-char-list-to-string hname.chars)))
                     (retok (str::cat path "/" name))))))
       ((mv erp bytes state)
        (acl2::read-file-into-byte-list path-to-read state))
       ((when erp)
        (reterr (msg "Reading ~x0 failed." path-to-read))))
    (retok bytes state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ppdfile
  :short "Fixtype of preprocessed files."
  :long
  (xdoc::topstring
   (xdoc::p
    "By `preprocessed file' here we mean the result of preprocessing a file.
     This result consists of
     the list of lexemes that forms the file after preprocessing
     (which can be printed to bytes into a file in the file system),
     the macros defined by the file (bundled into a single scope alist),
     and a flag indicating whether the file is @(see self-contained)."))
  ((lexemes plexeme-listp)
   (macros macro-scopep)
   (selfp booleanp))
  :pred ppdfilep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-ppdfile
  :short "An irrelevant preprocessed file."
  :type ppdfilep
  :body (ppdfile nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist string-ppdfile-alist
  :short "Fixtype of alists from strings to preprocessed files."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use these alists to keep track of which files
     have been already preprocessed and are @(see self-contained).
     That is, all the values of this alist have the @('selfp') flag @('t'),
     although we do not capture that invariant in this fixtype.")
   (xdoc::p
    "These alists always have unique keys,
     i.e. there are no shadowed pairs.
     This is not enforced in this fixtype.")
   (xdoc::p
    "When all the files have been preprocessed,
     this alist contains all the results from the preprocessing.
     The non-@(see self-contained) files are not part of this alist,
     because they have been expanded in place."))
  :key-type string
  :val-type ppdfile
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred string-ppdfile-alistp
  :prepwork ((set-induction-depth-limit 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-ppdfile-alist-to-filepath-filedata-map ((alist
                                                        string-ppdfile-alistp))
  :returns (map filepath-filedata-mapp)
  :short "Turn (1) an alist from string to preprocessed files
          into (2) a map from file paths to file data."
  :long
  (xdoc::topstring
   (xdoc::p
    "The strings are wrapped into file paths;
     as mentioned in @(tsee string-ppdfile-alist),
     the alist has unique keys, so the order of the alist is immaterial.
     The lists of lexemes are printed to bytes,
     obtaining the file datas.")
   (xdoc::p
    "This is called on the alist at the end of the preprocessing."))
  (b* (((when (endp alist)) nil)
       ((cons string ppdfile) (car alist))
       (bytes (plexemes-to-bytes (ppdfile->lexemes ppdfile)))
       (filepath (filepath string))
       (filedata (filedata bytes))
       (map (string-ppdfile-alist-to-filepath-filedata-map (cdr alist))))
    (omap::update filepath filedata map))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pproc
  :short "Preprocess files."
  :long
  (xdoc::topstring
   (xdoc::p
    "All these functions are mutually recursive because,
     as we preprocess a file,
     we may need to recursively preprocess files that it includes.")
   (xdoc::p
    "The top-level function of the clique is @(tsee pproc-file),
     which is called by @(tsee pproc-files) outside the clique.
     But it is also called when encoutering files to be included,
     which is why it is mutually recursive with the other functions.")
   (xdoc::p
    "All the functions take and return the ACL2 state,
     since they (indirectly) read files.")
   (xdoc::p
    "All the functions take as inputs
     the path prefix @('path') and the path rest @('file')
     of the file being preprocessed.
     These are needed to recursively find and read included files.")
   (xdoc::p
    "All the functions take and return the @('preprocessed') alist,
     which is extended not only with the file indicated in @(tsee pproc-file),
     but also possibly with other @(see self-contained) files
     included along the way.")
   (xdoc::p
    "All the functions also take the @('preprocessing') list,
     to detect and avoid circularities;
     see @(tsee pproc-file) and @(tsee pproc-files).")
   (xdoc::p
    "The top-level function @(tsee pproc-file) also takes as inputs
     the current macro table and an implementation environment,
     from which it constructs a local preprocessing state stobj @(tsee ppstate),
     which is passed to and returned from all the other functions.
     There is one such stobj for each file being preprocessed.")
   (xdoc::p
    "All the functions except the top-level @(tsee pproc-file)
     take and return the list of lexemes resulting from preprocessing,
     in reverse order for efficiency.
     They are reversed into the right order by @(tsee pproc-file).")
   (xdoc::p
    "In the absence of explicit checks, preprocessing may not terminate:
     @('file1.h') may include @('file2.h'), which may include @('file3.h'), etc.
     In practice, the file system is finite,
     but nontermination is the default, mathematically speaking.
     So we impose an artificial limit on the number of files being preprocessed,
     specifically on the depth of the recursion of @(tsee pproc-file).
     The GCC preprocessor imposes an @('#include') nesting limit of 200,
     according to "
    (xdoc::ahref "https://gcc.gnu.org/onlinedocs/cpp/Implementation-limits.html"
                 "Section 12.2 of the GNU C Preprocessor Manual")
    ". We pass the limit as an argument to these functions,
     so it can be set outside these functions;
     when this limit reaches 0, @(tsee pproc-file) returns an error."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-file ((path stringp)
                      (file stringp)
                      (preprocessed string-ppdfile-alistp)
                      (preprocessing string-listp)
                      (macros macro-tablep)
                      (ienv ienvp)
                      state
                      (file-recursion-limit natp))
    :guard (not (assoc-equal file preprocessed))
    :returns (mv erp
                 (ppdfile ppdfilep)
                 (new-preprocessed string-ppdfile-alistp)
                 state)
    :parents (preprocessor pproc)
    :short "Preprocess a file."
    :long
    (xdoc::topstring
     (xdoc::p
      "The file is specified by the @('file') string,
       which must be either a path relative to the @('path') string,
       or an absolute path with no relation to @('path').
       The latter is meant to happen with library files,
       but we have not implemented their handling yet.")
     (xdoc::p
      "As expressed by the guard,
       this function is called when the file is not in @('preprocessed'),
       because if that were the case, there is no need to re-preprocess it
       (see the callers of this function).")
     (xdoc::p
      "If @('file') is found in the list of the files under preprocessing,
       we stop with an error, because there is a circularity.
       Otherwise, before preprocessing the file,
       we add it to the list of files under preprocessing.")
     (xdoc::p
      "We read the file from the file system and we preprocess it,
       creating a local preprocessing state stobj for the file,
       with information from the implementation environment
       and with the current macro table
       (which @(tsee init-ppstate) extends with a new empty scope for the file.
       The preprocessing of this file may involve
       the recursive preprocessing of more files,
       and the consequent extension of the @('preprocessed') alist.
       The resulting @(tsee ppdfile) contains
       the lexemes obtained from the file
       and the macros contributed by the file,
       which are the macros in the innermost scope of the final table.
       The local preprocessing state stobj is discarded,
       after extracting the final macro table and self-contained flag.
       If the self-contained flag is @('t'),
       we extend the @('preprocessed') alist."))
    (b* (((reterr) (irr-ppdfile) nil state)
         ((when (zp file-recursion-limit))
          (reterr (msg "Exceeded the limit on file recursion.")))
         (file (str-fix file))
         (preprocessing (string-list-fix preprocessing))
         ((when (member-equal file preprocessing))
          (reterr (msg "Circular file dependencies involving ~&0."
                       preprocessing)))
         (preprocessing (cons file preprocessing))
         ((erp bytes state) (read-input-file-to-preprocess path file state))
         ((erp lexemes macros selfp preprocessed state)
          (with-local-stobj
            ppstate
            (mv-let (erp rev-lexemes macros selfp ppstate preprocessed state)
                (b* ((ppstate
                      (init-ppstate bytes
                                    (macro-table-fix macros)
                                    (ienv->version ienv)
                                    ppstate))
                     ((mv erp rev-lexemes ppstate preprocessed state)
                      (pproc-*-group-part path
                                          file
                                          preprocessed
                                          preprocessing
                                          nil
                                          ppstate
                                          state
                                          file-recursion-limit)))
                  (mv erp
                      rev-lexemes
                      (ppstate->macros ppstate)
                      (ppstate->selfp ppstate)
                      ppstate
                      preprocessed
                      state))
              (mv erp
                  (rev rev-lexemes)
                  (car (macro-table->scopes macros))
                  selfp
                  preprocessed
                  state))))
         (ppdfile (make-ppdfile :lexemes lexemes
                                :macros macros
                                :selfp selfp))
         (preprocessed (if selfp
                           (acons file ppdfile preprocessed)
                         preprocessed)))
      (retok ppdfile preprocessed state))
    :measure (nat-list-measure (list (nfix file-recursion-limit)
                                     1 ; > all other pproc-... functions
                                     0 ; irrelevant
                                     0))) ; irrelevant

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-*-group-part ((path stringp)
                              (file stringp)
                              (preprocessed string-ppdfile-alistp)
                              (preprocessing string-listp)
                              (rev-lexemes plexeme-listp)
                              (ppstate ppstatep)
                              state
                              (file-recursion-limit natp))
    :returns (mv erp
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-ppdfile-alistp)
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
         ((when (= (ppstate->size ppstate) 0)) ; EOF
          (retok (plexeme-list-fix rev-lexemes)
                 ppstate
                 (string-ppdfile-alist-fix preprocessed)
                 state))
         (psize (ppstate->size ppstate))
         ((erp rev-lexemes ppstate preprocessed state) ; group-part
          (pproc-group-part path
                            file
                            preprocessed
                            preprocessing
                            rev-lexemes
                            ppstate
                            state
                            file-recursion-limit))
         ((unless (mbt (<= (ppstate->size ppstate) (1- psize))))
          (reterr :impossible)))
      (pproc-*-group-part path
                          file
                          preprocessed
                          preprocessing
                          rev-lexemes
                          ppstate
                          state
                          file-recursion-limit))
    :measure (nat-list-measure (list (nfix file-recursion-limit)
                                     0 ; < pproc-file
                                     (ppstate->size ppstate)
                                     2))) ; > pproc-group-part

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-group-part ((path stringp)
                            (file stringp)
                            (preprocessed string-ppdfile-alistp)
                            (preprocessing string-listp)
                            (rev-lexemes plexeme-listp)
                            (ppstate ppstatep)
                            state
                            (file-recursion-limit natp))
    :returns (mv erp
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-ppdfile-alistp)
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
      "If we find a new line, it means that
       we have a text line (see grammar) without tokens.
       In this case we have finished the group part
       and we return all the lexemes.
       For example, this could contain comments, which we therefore preserve.")
     (xdoc::p
      "If we find a hash, we have a directive,
       which we handle in a separate function.
       We discard any white space and comments preceding the hash.")
     (xdoc::p
      "If we do not find a hash, we have a text line with tokens:
       we put back the token and we call a separate function.
       We pass any preceding white space and comments to that function."))
    (b* (((reterr) nil ppstate nil state)
         ((erp nontoknls toknl span ppstate) (pread-token/newline nil ppstate)))
      (cond
       ((not toknl) ; EOF
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a token or new line"
                    :found (plexeme-to-msg toknl)))
       ((or (plexeme-case toknl :newline) ; newline
            (plexeme-case toknl :line-comment)) ; // ...
        (retok (cons toknl (revappend nontoknls (plexeme-list-fix rev-lexemes)))
               ppstate
               (string-ppdfile-alist-fix preprocessed)
               state))
       ((plexeme-hashp toknl) ; #
        (pproc-directive path
                         file
                         preprocessed
                         preprocessing
                         rev-lexemes
                         ppstate
                         state
                         file-recursion-limit))
       (t ; non-#-token
        (b* ((ppstate (punread-token ppstate)))
          (pproc-text-line nontoknls
                           path
                           file
                           preprocessed
                           preprocessing
                           rev-lexemes
                           ppstate
                           state
                           file-recursion-limit)))))
    :measure (nat-list-measure (list (nfix file-recursion-limit)
                                     0 ; < pproc-file
                                     (ppstate->size ppstate)
                                     1)) ; > pproc-text-line
    :no-function nil)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-directive ((path stringp)
                           (file stringp)
                           (preprocessed string-ppdfile-alistp)
                           (preprocessing string-listp)
                           (rev-lexemes plexeme-listp)
                           (ppstate ppstatep)
                           state
                           (file-recursion-limit natp))
    :returns (mv erp
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-ppdfile-alistp)
                 state)
    :parents (preprocessor pproc)
    :short "Preprocess a directive."
    :long
    (xdoc::topstring
     (xdoc::p
      "With reference to the grammar,
       a directive is a group part that starts with @('#');
       this function is called just after the @('#') has been encountered.
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
       We simplify replace it with a blank line consisting of the new line,
       discarding any preceding comments or white space.")
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
         ((erp & toknl span ppstate) (pread-token/newline nil ppstate)))
      (cond
       ((not toknl) ; # EOF
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a token or new line"
                    :found (plexeme-to-msg toknl)))
       ((or (plexeme-case toknl :newline) ; # newline
            (plexeme-case toknl :line-comment)) ; # // ...
        ;; null directive
        (b* ((newline (if (plexeme-case toknl :newline)
                          toknl
                        (plexeme-newline
                         (plexeme-line-comment->newline toknl)))))
          (retok (cons newline (plexeme-list-fix rev-lexemes))
                 ppstate
                 (string-ppdfile-alist-fix preprocessed)
                 state)))
       ((plexeme-case toknl :ident) ; # ident
        (b* ((dirname (ident->unwrap (plexeme-ident->ident toknl))))
          (cond
           ((equal dirname "if") ; # if
            (reterr :todo))
           ((equal dirname "ifdef") ; # ifdef
            (reterr :todo))
           ((equal dirname "ifndef") ; # ifndef
            (reterr :todo))
           ((equal dirname "include") ; # include
            (pproc-include-directive path
                                     file
                                     preprocessed
                                     preprocessing
                                     rev-lexemes
                                     ppstate
                                     state
                                     file-recursion-limit))
           ((equal dirname "define") ; # define
            (reterr :todo))
           ((equal dirname "undef") ; # undef
            (reterr :todo))
           ((equal dirname "line") ; # line
            (reterr :todo))
           ((equal dirname "error") ; # error
            (reterr :todo))
           ((equal dirname "pragma") ; # pragma
            (reterr :todo))
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
    :measure (nat-list-measure (list (nfix file-recursion-limit)
                                     0 ; < pproc-file
                                     (ppstate->size ppstate)
                                     0))
    :no-function nil)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-include-directive ((path stringp)
                                   (file stringp)
                                   (preprocessed string-ppdfile-alistp)
                                   (preprocessing string-listp)
                                   (rev-lexemes plexeme-listp)
                                   (ppstate ppstatep)
                                   state
                                   (file-recursion-limit natp))
    :returns (mv erp
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-ppdfile-alistp)
                 state)
    :parents (preprocessor pproc)
    :short "Preprocess a @('#include') directive."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called just after the @('include') identifier has been parsed.")
     (xdoc::p
      "If we do not find a token or new line,
       it is an error, because there is no header name,
       and no macro that could result in a header name.")
     (xdoc::p
      "If we find a new line,
       it is an error, because there is no header name,
       and no macro that could result in a header name.")
     (xdoc::p
      "If we find a header name,
       we find the file referenced by it
       and we recursively preprocess it.
       Note that we pass @('t') as the @('headerp') flag,
       so that we can properly lex header names,
       which would otherwise be lexed as string literals
       or as the puctuator @('<') just for the opening angle bracket.
       Note that string literals and @('<') cannot be
       macro-expanded to a header name,
       so it is always correct to lex with the @('headerp') flag @('t').")
     (xdoc::p
      "If we find any other token,
       for now we return an error,
       but we should preprocess that token and any subsequent tokens,
       and see if they result in a header name."))
    (declare
     (ignore
      path file preprocessed preprocessing rev-lexemes file-recursion-limit))
    (b* (((reterr) nil ppstate nil state)
         ((erp & toknl span ppstate) (pread-token/newline t ppstate)))
      (cond
       ((not toknl) ; # include EOF
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a token"
                    :found (plexeme-to-msg toknl)))
       ((or (plexeme-case toknl :newline)
            (plexeme-case toknl :line-comment)) ; # include // ...
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a token"
                    :found (plexeme-to-msg toknl)))
       ((plexeme-case toknl :header) ; # include headername
        (reterr :todo))
       (t ; # include token
        (reterr (msg "Non-direct #include not yet supported.")))))
    :measure (nat-list-measure (list (nfix file-recursion-limit)
                                     0 ; < pproc-file
                                     (ppstate->size ppstate)
                                     0))
    :no-function nil)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-text-line ((nontoknls plexeme-listp)
                           (path stringp)
                           (file stringp)
                           (preprocessed string-ppdfile-alistp)
                           (preprocessing string-listp)
                           (rev-lexemes plexeme-listp)
                           (ppstate ppstatep)
                           state
                           (file-recursion-limit natp))
    :returns (mv erp
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-ppdfile-alistp)
                 state)
    :parents (preprocessor pproc)
    :short "Preprocess a (non-empty) text line."
    :long
    (xdoc::topstring
     (xdoc::p
      "That is, preprocess a line that does not start with a hash
       (possibly after some white space and comments).
       This is called after putting back the first token of the line,
       but without having put back any leading white space or comments,
       since those do not matter for the purpose of preprocessing the text line.
       Recall that empty text lines,
       i.e. with no tokens (but possibly with some white space and comments),
       are already handled in @(tsee pproc-group-part)."))
    (declare (ignore nontoknls preprocessed file-recursion-limit))
    (b* (((reterr) nil ppstate nil state))
      (reterr (list :todo path file preprocessing rev-lexemes)))
    :measure (nat-list-measure (list (nfix file-recursion-limit)
                                     0 ; < pproc-file
                                     (ppstate->size ppstate)
                                     0)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :prepwork ((set-bogus-mutual-recursion-ok t) ; TODO: remove eventually
             (local (in-theory (enable acons))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable len nfix fix)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual ppstate->size-of-pproc-uncond
    (defret ppstate->size-of-pproc-file-uncond
      t
      :fn pproc-file
      :rule-classes nil)
    (defret ppstate->size-of-pproc-*-group-part-uncond
      (<= (ppstate->size new-ppstate)
          (ppstate->size ppstate))
      :fn pproc-*-group-part
      :rule-classes :linear)
    (defret ppstate->size-of-pproc-group-part-uncond
      (<= (ppstate->size new-ppstate)
          (ppstate->size ppstate))
      :fn pproc-group-part
      :rule-classes :linear)
    (defret ppstate->size-of-pproc-directive-uncond
      (<= (ppstate->size new-ppstate)
          (ppstate->size ppstate))
      :fn pproc-directive
      :rule-classes :linear)
    (defret ppstate->size-of-pproc-include-directive-uncond
      (<= (ppstate->size new-ppstate)
          (ppstate->size ppstate))
      :fn pproc-include-directive
      :rule-classes :linear)
    (defret ppstate->size-of-pproc-text-line-uncond
      (<= (ppstate->size new-ppstate)
          (ppstate->size ppstate))
      :fn pproc-text-line
      :rule-classes :linear))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual ppstate->size-of-pproc-cond
    (defret ppstate->size-of-pproc-file-cond
      t
      :fn pproc-file
      :rule-classes nil)
    (defret ppstate->size-of-pproc-*-group-part-cond
      t
      :fn pproc-*-group-part
      :rule-classes nil)
    (defret ppstate->size-of-pproc-group-part-cond
      (implies (not erp)
               (<= (ppstate->size new-ppstate)
                   (1- (ppstate->size ppstate))))
      :fn pproc-group-part
      :rule-classes :linear)
    (defret ppstate->size-of-pproc-directive-cond
      (implies (not erp)
               (<= (ppstate->size new-ppstate)
                   (1- (ppstate->size ppstate))))
      :fn pproc-directive
      :rule-classes :linear)
    (defret ppstate->size-of-pproc-include-directive-cond
      (implies (not erp)
               (<= (ppstate->size new-ppstate)
                   (1- (ppstate->size ppstate))))
      :fn pproc-include-directive
      :rule-classes :linear)
    (defret ppstate->size-of-pproc-text-line-cond
      (implies (not erp)
               (<= (ppstate->size new-ppstate)
                   (1- (ppstate->size ppstate))))
      :fn pproc-text-line
      :rule-classes :linear))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards pproc-file
    :hints
    (("Goal" :in-theory (enable alistp-when-string-ppdfile-alistp-rewrite
                                true-listp-when-plexeme-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pproc-files ((path stringp)
                     (files string-listp)
                     (ienv ienvp)
                     state
                     (file-recursion-limit natp))
  :returns (mv erp (fileset filesetp) state)
  :short "Preprocess zero or more files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level function of the preprocessor.
     The files are identified by the @('files') strings,
     which must all be paths relative to the @('path') string:
     this is the same interface as @(tsee input-files).
     The elements of @('files') are preprocessed in order.
     Each file is read from the file system and preprocessed,
     unless it has been already preprocessed via
     a direct or indirect inclusion of some previous file.")
   (xdoc::p
    "We keep track of the files under preprocessing in a list (initially empty),
     to detect and avoid circularities.
     The result of this function is a file set,
     whose paths are generally a superset of the input ones:
     the files specified by @('files') may include, directly or indirectly,
     files whose paths are not in @('files'), e.g. files from the C library.
     The resulting file set is ``closed'' with respect to @('#include'):
     the @(see self-contained) ones are in the file set,
     and the non-@(see self-contained) ones have been expanded.")
   (xdoc::p
    "It is an internal (hard) error if
     any of the files specified directly is not @(see self-contained).")
   (xdoc::p
    "The file recursion limit is discussed in @(tsee pproc).
     It should be set to a sufficiently large value of course,
     but an excessively large value could be slow
     in diagnosing an actual circularity.
     It seems best to let the user set this limit (outside this function),
     with perhaps a reasonable default like GCC has."))
  (b* (((reterr) (irr-fileset) state)
       ((erp preprocessed state)
        (pproc-files-loop path files nil nil ienv state file-recursion-limit)))
    (retok
     (fileset (string-ppdfile-alist-to-filepath-filedata-map preprocessed))
     state))

  :prepwork
  ((define pproc-files-loop ((path stringp)
                             (files string-listp)
                             (preprocessed string-ppdfile-alistp)
                             (preprocessing string-listp)
                             (ienv ienvp)
                             state
                             (file-recursion-limit natp))
     :returns (mv erp (new-preprocessed string-ppdfile-alistp) state)
     :parents nil
     (b* (((reterr) nil state)
          ((when (endp files))
           (retok (string-ppdfile-alist-fix preprocessed) state))
          (file (str-fix (car files)))
          ((when (assoc-equal file (string-ppdfile-alist-fix preprocessed)))
           (pproc-files-loop path
                             (cdr files)
                             preprocessed
                             preprocessing
                             ienv
                             state
                             file-recursion-limit))
          ((erp ppdfile preprocessed state) (pproc-file path
                                                        (car files)
                                                        preprocessed
                                                        preprocessing
                                                        (macro-table-init)
                                                        ienv
                                                        state
                                                        file-recursion-limit))
          ((unless (ppdfile->selfp ppdfile))
           (raise "Internal error: non-self-contained top-level file ~x0."
                  (str-fix (car files)))
           (reterr t)))
       (pproc-files-loop path
                         (cdr files)
                         preprocessed
                         preprocessing
                         ienv
                         state
                         file-recursion-limit))
     :guard-hints
     (("Goal" :in-theory (enable alistp-when-string-ppdfile-alistp-rewrite)))
     :no-function nil)))
