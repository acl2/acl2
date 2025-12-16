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
     preserves the information about the @('#include') directives.
     That is, it does not replace such directives
     with the (preprocessed) contents of the referenced files,
     but it otherwise performs the rest of the preprocessing.")
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
               (nontokens-nonnewlines plexeme-listp)
               (token/newline? plexeme-optionp)
               (token/newline-span spanp)
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Read a token or newline during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee plexeme-token/newline-p),
     we also include line comments as newlines."))
  (b* (((reterr) nil nil (irr-span) ppstate)
       ((erp lexeme span ppstate) (plex-lexeme headerp ppstate))
       ((when (not lexeme)) (retok nil nil span ppstate))
       ((when (plexeme-token/newline-p lexeme)) (retok nil lexeme span ppstate))
       ((erp nontokens-nonnewlines token/newline token/newline-span ppstate)
        (pread-token/newline headerp ppstate)))
    (retok (cons lexeme nontokens-nonnewlines)
           token/newline
           token/newline-span
           ppstate))
  :measure (ppstate->size ppstate)

  ///

  (defret plexeme-list-not-token/newline-p-of-pread-token/newline
    (plexeme-list-not-token/newline-p nontokens-nonnewlines)
    :hints (("Goal" :induct t)))

  (defret plexeme-token/newline-p-of-pread-token/newline
    (implies token?
             (plexeme-token/newline-p token/newline?))
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-pread-token/newline-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-pread-token/newline-cond
    (implies (and (not erp)
                  token/newline?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

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
                                     1))) ; > pproc-group-part

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
      "We read the next token or newline, skipping over whitespace and comments.
       If we find no token or newline, it is an error,
       because it means that the file has some whitespace or comments
       without a terminating newline;
       this function is called (by @(tsee pproc-*-group-part))
       only if we are not at the end of file.")
     (xdoc::p
      "If we find a newline, it means that
       we have a text line (see grammar) without tokens.
       In this case we have finished the group part
       and we return all the lexemes.")
     (xdoc::p
      "If we find a hash, we have a directive;
       otherwise, we have a text line with tokens."))
    (b* (((reterr) nil ppstate nil state)
         ((unless (mbt (<= (len preprocessed) *pproc-files-max*)))
          (reterr :impossible))
         ((erp nontokens-nonnewlines token/newline span ppstate)
          (pread-token/newline nil ppstate)))
      (cond
       ((not token/newline) ; ... EOF
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a token or newline"
                    :found token/newline))
       ((plexeme-case token/newline :newline) ; ... newline
        (retok (cons token/newline
                     (revappend nontokens-nonnewlines
                                (plexeme-list-fix rev-lexemes)))
               ppstate
               (string-plexeme-list-alist-fix preprocessed)
               state))
       ((plexeme-hashp token/newline) ; ... #
        (reterr (list :todo path file preprocessing)))
       (t ; ... token
        (reterr (list :todo path file preprocessing)))))
    :measure (nat-list-measure (list (nfix (- *pproc-files-max*
                                              (len preprocessed)))
                                     0 ; < pproc-file
                                     (ppstate->size ppstate)
                                     0))
    :no-function nil)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :prepwork ((set-bogus-mutual-recursion-ok t) ; TODO: remove eventually
             (local (in-theory (enable acons))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable len nfix fix)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  :guard-hints
  (("Goal" :in-theory (enable alistp-when-string-plexeme-list-alistp-rewrite
                              true-listp-when-plexeme-listp)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual len-of-new-preprocessed-of-pproc-bound
    (defret len-of-new-preprocessed-of-pproc-file-bound
      (<= (len new-preprocessed) *pproc-files-max*)
      :fn pproc-file
      :rule-classes :linear)
    (defret len-of-new-preprocessed-of-pproc-*-group-part-bound
      (<= (len new-preprocessed) *pproc-files-max*)
      :fn pproc-*-group-part
      :rule-classes :linear
      :hints ('(:expand (pproc-*-group-part path
                                            file
                                            preprocessed
                                            preprocessing
                                            rev-lexemes
                                            ppstate
                                            state))))
    (defret len-of-new-preprocessed-of-pproc-group-part-bound
      (<= (len new-preprocessed) *pproc-files-max*)
      :fn pproc-group-part
      :rule-classes :linear)
    :hints
    (("Goal"
      :in-theory
      (enable pproc-file
              pproc-*-group-part
              pproc-group-part
              len
              len-of-string-plexeme-list-alist-fix-upper-bound-len)))))

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
