; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
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
     preserves the information about the @('#include') directives in some cases.
     That is, it does not replace such directives
     with the (preprocessed) contents of the referenced files,
     but it otherwise performs the rest of the preprocessing.
     This is only done under certain conditions;
     in general, the C preprocessor operates at a low lexical level,
     making it difficult to preserve code structure in general.")
   (xdoc::p
    "Our preprocessor maps a list of file paths
     to a file set (see @(see files)):
     it preprocesses all the files with the given file paths,
     as well as all the files directly and indirectly included.
     The resulting file set contains entries for all such files,
     not only the ones with the given file paths.")
   (xdoc::p
    "Our preprocessor reads characters and lexes them into lexemes,
     while executing the preprocessing directives.
     The resulting sequence of lexemes is then turned into characters
     that are written into files.
     The resulting file set is amenable to our parser
     (more precisely, it will be, once we have extended our parser
     to accept @('#include') directives in certain places).
     Our preprocessor preserves white space, in order to preserve the layout
     (modulo the inherent layout changes caused by preprocessing).
     Our preprocessor also preserves comments,
     although some comments may no longer apply to preprocessed code
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
     and an span consisting of just the current position.")
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
    "As explained in @(tsee plexeme-token/newline-p),
     we also include line comments as new lines."))
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
     to the sequence of unread lexemes.")
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

  (defret ppstate->size-of-unread-token
    (equal (ppstate->size new-ppstate)
           (1+ (ppstate->size ppstate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-input-file-to-preproc ((path stringp) (file stringp) state)
  :returns (mv erp (bytes byte-listp) state)
  :short "Read a file to preprocess, explicitly specified as user input."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for the files
     whose paths are explicitly passed to @(tsee pproc-files).
     We concatenate the path prefix to the file path suffix,
     with a slash in between (this is for Unix-like systems).
     We read the bytes from the file system, and return them."))
  (b* (((reterr) nil state)
       (path-to-read (str::cat path "/" file))
       ((mv erp bytes state)
        (acl2::read-file-into-byte-list path-to-read state))
       ((when erp)
        (reterr (msg "Reading ~x0 failed." path-to-read))))
    (retok bytes state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist string-plexeme-list-alist
  :short "Fixtype of alists from strings to lists of preprocessing lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use these alists to keep track of which files
     have been already preprocessed,
     namely the ones whose paths are specified by the keys of the alist.
     The values associated to the keys are
     the lexemes resulting from the preprocessing.")
   (xdoc::p
    "These alists always have unique keys,
     i.e. there are no shadowed pairs.
     This is not enforced in this fixtype,
     but we could consider wrapping the alist
     into a @(tsee fty::defprod) with the invariant."))
  :key-type string
  :val-type plexeme-list
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t
  :pred string-plexeme-list-alistp
  :prepwork ((set-induction-depth-limit 1))

  ///

  (defruled len-of-string-plexeme-list-alist-fix-upper-bound-len
    (<= (len (string-plexeme-list-alist-fix x))
        (len x))
    :rule-classes :linear
    :induct t
    :enable (string-plexeme-list-alist-fix len)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-plexeme-list-alist-to-filepath-filedata-map
  ((alist string-plexeme-list-alistp))
  :returns (map filepath-filedata-mapp)
  :short "Turn (1) an alist from string to lists of preprocessing lexemes
          into (2) a map from file paths to file data."
  :long
  (xdoc::topstring
   (xdoc::p
    "The strings are wrapped into file paths;
     as mentioned in @(tsee string-plexeme-list-alist),
     the alist has unique keys, so the order of the alist is immaterial.
     The lists of lexemes are printed to bytes,
     obtaining the file datas."))
  (b* (((when (endp alist)) nil)
       ((cons string lexemes) (car alist))
       (bytes (plexemes-to-bytes lexemes))
       (filepath (filepath string))
       (filedata (filedata bytes))
       (map (string-plexeme-list-alist-to-filepath-filedata-map (cdr alist))))
    (omap::update filepath filedata map))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *pproc-files-max*
  :short "Maximum number of files being preprocessed."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the absence of explicit checks, preprocessing may not terminate:
     @('file1.h') may include @('file2.h'),
     which may include @('file3.h'),
     and so on.
     In practice, the file system is finite,
     but nontermination is the default, mathematically speaking.
     So we impose an artificial limit on the number of files being preprocessed,
     specifically on the length of the @(tsee string-plexeme-list-alistp) alists
     that are manipulated by our preprocessor.
     The GCC preprocessor imposes an @('#include') nesting limit of 200,
     according to "
    (xdoc::ahref "https://gcc.gnu.org/onlinedocs/cpp/Implementation-limits.html"
                 "Section 12.2 of the GNU C Preprocessor Manual")
    ". For simplicity, instead of keeping track of nesting,
     we impose a limit on the total number of files.
     We pick a very large limit that is unlikely to reach in practice
     (it may take too much time to reach,
     even if those many files could be found/generated)."))
  1000000000) ; 1 billion files

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
    "All the functions take and return state,
     since they (indirectly) read files.")
   (xdoc::p
    "All the functions take as inputs
     the path prefix @('path') and the path rest @('file')
     of the file being preprocessed.
     These are needed to recursively find and read included files.")
   (xdoc::p
    "All the functions take and return the @('preprocessed') alist,
     which is extended not only with the file indicated in @(tsee pproc-file),
     but also possibly with other files included along the way.
     See @(tsee pproc-file) and @(tsee pproc-files).")
   (xdoc::p
    "All the functions also take the @('preprocessing') list,
     to detect and avoid circularities;
     see @(tsee pproc-file) and @(tsee pproc-files).")
   (xdoc::p
    "The top-level function @(tsee pproc-file)
     takes an implementation environment,
     from which it constructs a local preprocessing state stobj @(tsee ppstate),
     which is passed to and returned from all the other functions.
     There is one such stobj for each file being preprocessed.")
   (xdoc::p
    "All the functions except the top-level @(tsee pproc-file)
     take and return the list of lexemes resulting from preprocessing,
     in reverse order for efficiency.
     They are reversed into the right order by @(tsee pproc-file)."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-file ((path stringp)
                      (file stringp)
                      (preprocessed string-plexeme-list-alistp)
                      (preprocessing string-listp)
                      (ienv ienvp)
                      state)
    :guard (<= (len preprocessed) *pproc-files-max*)
    :returns (mv erp
                 (new-preprocessed string-plexeme-list-alistp)
                 state)
    :parents (preprocessor pproc)
    :short "Preprocess a file."
    :long
    (xdoc::topstring
     (xdoc::p
      "The file is specified by the @('file') string,
       which must be either a path relative to the @('path') string,
       or an absolute path with no relation to @('path').")
     (xdoc::p
      "If @('file') is found in the list of the files under preprocessing,
       we stop with an error, because there is a circularity.
       If @('file') is found in the alist of already preprocessed files,
       the alist is returned unchanged.")
     (xdoc::p
      "Otherwise, we read the file from the file system and preprocess it,
       which may involve the recursive preprocessing of more files.
       Before preprocessing the file,
       we add it to the list of files under preprocessing.
       We create a local preprocessing state stobj for the file,
       with information from the implementation environment."))
    (b* (((reterr) nil state)
         ((unless (mbt (<= (len preprocessed) *pproc-files-max*)))
          (reterr :impossible))
         (file (str-fix file))
         (preprocessing (string-list-fix preprocessing))
         ((when (member-equal file preprocessing))
          (reterr (msg "Circular file dependencies involving ~&0."
                       preprocessing)))
         (file+lexemes
          (assoc-equal file (string-plexeme-list-alist-fix preprocessed)))
         ((when file+lexemes)
          (retok (string-plexeme-list-alist-fix preprocessed) state))
         ((erp bytes state) (read-input-file-to-preproc path file state))
         (preprocessing (cons file (string-list-fix preprocessing)))
         ((erp rev-lexemes preprocessed state)
          (with-local-stobj
            ppstate
            (mv-let (erp lexemes ppstate preprocessed state)
                (b* ((ppstate
                      (init-ppstate bytes (ienv->version ienv) ppstate)))
                  (pproc-*-group-part path
                                      file
                                      preprocessed
                                      preprocessing
                                      nil
                                      ppstate
                                      state))
              (mv erp lexemes preprocessed state))))
         (lexemes (rev rev-lexemes))
         ((when (= (len preprocessed) *pproc-files-max*))
          (reterr (msg "Exceeded ~x0 file limit." *pproc-files-max*)))
         (preprocessed (acons file lexemes preprocessed)))
      (retok preprocessed state))
    :measure (nat-list-measure (list (nfix (- *pproc-files-max*
                                              (len preprocessed)))
                                     1 ; > all other pproc-... functions
                                     0 ; irrelevant
                                     0))) ; irrelevant

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-*-group-part ((path stringp)
                              (file stringp)
                              (preprocessed string-plexeme-list-alistp)
                              (preprocessing string-listp)
                              (rev-lexemes plexeme-listp)
                              (ppstate ppstatep)
                              state)
    :guard (<= (len preprocessed) *pproc-files-max*)
    :returns (mv erp
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-plexeme-list-alistp)
                 state)
    :parents (preprocessor pproc)
    :short "Preprocess zero or more group parts."
    :long
    (xdoc::topstring
     (xdoc::p
      "According to the grammar,
       a preprocessing-file consists of zero or more group-parts.
       Each group part ends with a new line,
       and non-empty files must end with new line [C17:5.1.1.2/1, phase 4].
       Thus, we can detect whether there is a group part or not
       by checking for end of file
       (this may need to be relaxed at some point,
       since GCC is more lenient on this front)."))
    (b* (((reterr) nil ppstate nil state)
         ((unless (mbt (<= (len preprocessed) *pproc-files-max*)))
          (reterr :impossible))
         ((when (= (ppstate->size ppstate) 0)) ; EOF
          (retok (plexeme-list-fix rev-lexemes)
                 ppstate
                 (string-plexeme-list-alist-fix preprocessed)
                 state))
         (psize (ppstate->size ppstate))
         (plen (len preprocessed))
         ((erp rev-lexemes ppstate preprocessed state) ; group-part
          (pproc-group-part
           path file preprocessed preprocessing rev-lexemes ppstate state))
         ((unless (mbt (<= (ppstate->size ppstate) (1- psize))))
          (reterr :impossible))
         ((unless (mbt (>= (len preprocessed) plen)))
          (reterr :impossible)))
      (pproc-*-group-part ; group-part group-part
       path file preprocessed preprocessing rev-lexemes ppstate state))
    :measure (nat-list-measure (list (nfix (- *pproc-files-max*
                                              (len preprocessed)))
                                     0 ; < pproc-file
                                     (ppstate->size ppstate)
                                     2))) ; > pproc-group-part

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-group-part ((path stringp)
                            (file stringp)
                            (preprocessed string-plexeme-list-alistp)
                            (preprocessing string-listp)
                            (rev-lexemes plexeme-listp)
                            (ppstate ppstatep)
                            state)
    :guard (<= (len preprocessed) *pproc-files-max*)
    :returns (mv erp
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-plexeme-list-alistp)
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
         ((unless (mbt (<= (len preprocessed) *pproc-files-max*)))
          (reterr :impossible))
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
               (string-plexeme-list-alist-fix preprocessed)
               state))
       ((plexeme-hashp toknl) ; #
        (pproc-directive
         path file preprocessed preprocessing rev-lexemes ppstate state))
       (t ; non-#-token
        (b* ((ppstate (punread-token ppstate)))
          (pproc-text-line nontoknls path file preprocessed preprocessing
                           rev-lexemes ppstate state)))))
    :measure (nat-list-measure (list (nfix (- *pproc-files-max*
                                              (len preprocessed)))
                                     0 ; < pproc-file
                                     (ppstate->size ppstate)
                                     1)) ; > pproc-text-line
    :no-function nil)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-directive ((path stringp)
                           (file stringp)
                           (preprocessed string-plexeme-list-alistp)
                           (preprocessing string-listp)
                           (rev-lexemes plexeme-listp)
                           (ppstate ppstatep)
                           state)
    :guard (<= (len preprocessed) *pproc-files-max*)
    :returns (mv erp
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-plexeme-list-alistp)
                 state)
    :parents (preprocessor pproc)
    :short "Preprocess a directive."
    :long
    (xdoc::topstring
     (xdoc::p
      "With reference to the grammar,
       a directive is a group part that starts with @('#');
       this function is called just after the @('#') has been encountered.
       A directive may be an @('if') group (which spans multiple lines),
       a control line (which spans one line),
       or a non-directive (which spans one line);
       the latter, despite the name, is considered a directive
       (see footnote 175 in [C17:6.10.3/11].")
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
       without comments or white space before the new line.")
     (xdoc::p
      "If we find an identifier,
       we check to see if it is the name of a know directive,
       and we handle the directive accordingly if that is the case.
       If it is not a directive name, or if it is not even an identifier,
       we have a non-directive [C17:6.10/9],
       which renders the behavior undefined;
       we stop with an error in this case.
       (We may extend this in the future,
       e.g. to accommodate non-standard directives.)"))
    (b* (((reterr) nil ppstate nil state)
         ((unless (mbt (<= (len preprocessed) *pproc-files-max*)))
          (reterr :impossible))
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
                 (string-plexeme-list-alist-fix preprocessed)
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
            (pproc-include-directive
             path file preprocessed preprocessing rev-lexemes ppstate state))
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
    :measure (nat-list-measure (list (nfix (- *pproc-files-max*
                                              (len preprocessed)))
                                     0 ; < pproc-file
                                     (ppstate->size ppstate)
                                     0))
    :no-function nil)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-include-directive ((path stringp)
                                   (file stringp)
                                   (preprocessed string-plexeme-list-alistp)
                                   (preprocessing string-listp)
                                   (rev-lexemes plexeme-listp)
                                   (ppstate ppstatep)
                                   state)
    :guard (<= (len preprocessed) *pproc-files-max*)
    :returns (mv erp
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-plexeme-list-alistp)
                 state)
    :parents (preprocessor pproc)
    :short "Preprocess a @('#include') directive."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called just after the @('include') identifier has been parsed.")
     (xdoc::p
      "If we do not find a token or new line,
       it is an error, because there is no header name.")
     (xdoc::p
      "If we find a new line,
       it is an error, because there is no header name.")
     (xdoc::p
      "If we find a header name,
       we find the file referenced by it
       and we recursively preprocess it.
       Note that we pass @('t') as the @('headerp') flag.")
     (xdoc::p
      "If we find any other token,
       for now we return an error,
       but we should preprocess that token and any subsequent tokens,
       and see if they result in a header name."))
    (declare (ignore path file preprocessing rev-lexemes))
    (b* (((reterr) nil ppstate nil state)
         ((unless (mbt (<= (len preprocessed) *pproc-files-max*)))
          (reterr :impossible))
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
    :measure (nat-list-measure (list (nfix (- *pproc-files-max*
                                              (len preprocessed)))
                                     0 ; < pproc-file
                                     (ppstate->size ppstate)
                                     0))
    :no-function nil)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pproc-text-line ((nontoknls plexeme-listp)
                           (path stringp)
                           (file stringp)
                           (preprocessed string-plexeme-list-alistp)
                           (preprocessing string-listp)
                           (rev-lexemes plexeme-listp)
                           (ppstate ppstatep)
                           state)
    :guard (<= (len preprocessed) *pproc-files-max*)
    :returns (mv erp
                 (new-rev-lexemes plexeme-listp)
                 (new-ppstate ppstatep :hyp (ppstatep ppstate))
                 (new-preprocessed string-plexeme-list-alistp)
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
       are already handlede in @(tsee pproc-group-part)."))
    (declare (ignore nontoknls))
    (b* (((reterr) nil ppstate nil state)
         ((unless (mbt (<= (len preprocessed) *pproc-files-max*)))
          (reterr :impossible)))
      (reterr (list :todo path file preprocessing rev-lexemes)))
    :measure (nat-list-measure (list (nfix (- *pproc-files-max*
                                              (len preprocessed)))
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

  (defret-mutual len-of-new-preprocessed-of-pproc-upper-bound
    (defret len-of-new-preprocessed-of-pproc-file-upper-bound
      (<= (len new-preprocessed) *pproc-files-max*)
      :fn pproc-file
      :rule-classes :linear)
    (defret len-of-new-preprocessed-of-pproc-*-group-part-upper-bound
      (<= (len new-preprocessed) *pproc-files-max*)
      :fn pproc-*-group-part
      :rule-classes :linear)
    (defret len-of-new-preprocessed-of-pproc-group-part-upper-bound
      (<= (len new-preprocessed) *pproc-files-max*)
      :fn pproc-group-part
      :rule-classes :linear)
    (defret len-of-new-preprocessed-of-pproc-directive-upper-bound
      (<= (len new-preprocessed) *pproc-files-max*)
      :fn pproc-directive
      :rule-classes :linear)
    (defret len-of-new-preprocessed-of-pproc-include-directive-upper-bound
      (<= (len new-preprocessed) *pproc-files-max*)
      :fn pproc-include-directive
      :rule-classes :linear)
    (defret len-of-new-preprocessed-of-pproc-text-line-upper-bound
      (<= (len new-preprocessed) *pproc-files-max*)
      :fn pproc-text-line
      :rule-classes :linear)
    :hints
    (("Goal"
      :in-theory
      (enable len
              len-of-string-plexeme-list-alist-fix-upper-bound-len))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual len-of-new-preprocessed-of-pproc-lower-bound
    (defret len-of-new-preprocessed-of-pproc-file-lower-bound
      (implies (not erp)
               (>= (len new-preprocessed) (len preprocessed)))
      :hyp (string-plexeme-list-alistp preprocessed)
      :fn pproc-file
      :rule-classes :linear)
    (defret len-of-new-preprocessed-of-pproc-*-group-part-lower-bound
      (implies (not erp)
               (>= (len new-preprocessed) (len preprocessed)))
      :hyp (string-plexeme-list-alistp preprocessed)
      :fn pproc-*-group-part
      :rule-classes :linear
      :hints ('(:expand (pproc-*-group-part path
                                            file
                                            preprocessed
                                            preprocessing
                                            rev-lexemes
                                            ppstate
                                            state))))
    (defret len-of-new-preprocessed-of-pproc-group-part-lower-bound
      (implies (not erp)
               (>= (len new-preprocessed) (len preprocessed)))
      :hyp (string-plexeme-list-alistp preprocessed)
      :fn pproc-group-part
      :rule-classes :linear)
    (defret len-of-new-preprocessed-of-pproc-directive-lower-bound
      (implies (not erp)
               (>= (len new-preprocessed) (len preprocessed)))
      :hyp (string-plexeme-list-alistp preprocessed)
      :fn pproc-directive
      :rule-classes :linear)
    (defret len-of-new-preprocessed-of-pproc-include-directive-lower-bound
      (implies (not erp)
               (>= (len new-preprocessed) (len preprocessed)))
      :hyp (string-plexeme-list-alistp preprocessed)
      :fn pproc-include-directive
      :rule-classes :linear)
    (defret len-of-new-preprocessed-of-pproc-text-line-lower-bound
      (implies (not erp)
               (>= (len new-preprocessed) (len preprocessed)))
      :hyp (string-plexeme-list-alistp preprocessed)
      :fn pproc-text-line
      :rule-classes :linear)
    :hints (("Goal" :in-theory (enable len))))

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
    (("Goal" :in-theory (enable alistp-when-string-plexeme-list-alistp-rewrite
                                true-listp-when-plexeme-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pproc-files ((path stringp) (files string-listp) (ienv ienvp) state)
  :returns (mv erp (fileset filesetp) state)
  :short "Preprocess zero or more files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level function of the preprocessor.
     The files are identified by the @('files') strings,
     which must be all paths relative to the @('path') string
     (as in @(tsee input-files)).
     The elements of @('files') are preprocessed in order.
     Each file is read from the file system and preprocessed.
     We keep track of the files under preprocessing in a list (initially empty),
     to detect and avoid circularities.
     The result of this function is a file set,
     whose paths are generally a superset of the input ones:
     the files specified by @('files') may include, directly or indirectly,
     files whose paths are not in @('files'), e.g. files from the C library.
     The resulting file set is ``closed'' with respect to @('#include')."))
  (b* (((reterr) (irr-fileset) state)
       ((erp preprocessed state)
        (pproc-files-loop path files nil nil ienv state)))
    (retok
     (fileset (string-plexeme-list-alist-to-filepath-filedata-map preprocessed))
     state))

  :prepwork
  ((define pproc-files-loop ((path stringp)
                             (files string-listp)
                             (preprocessed string-plexeme-list-alistp)
                             (preprocessing string-listp)
                             (ienv ienvp)
                             state)
     :guard (<= (len preprocessed) *pproc-files-max*)
     :returns (mv erp (new-preprocessed string-plexeme-list-alistp) state)
     :parents nil
     (b* (((reterr) nil state)
          ((when (endp files))
           (retok (string-plexeme-list-alist-fix preprocessed) state))
          ((erp preprocessed state)
           (pproc-file path (car files) preprocessed preprocessing ienv state)))
       (pproc-files-loop
        path (cdr files) preprocessed preprocessing ienv state)))))
