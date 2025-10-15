; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "parser-states")
(include-book "parser-messages")

(include-book "kestrel/fty/character-list" :dir :system)
(include-book "kestrel/fty/nat-option" :dir :system)
(include-book "std/strings/letter-uscore-chars" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (:e tau-system))))
(set-induction-depth-limit 0)

; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Library extensions.

(defruledl integerp-when-bytep
  (implies (bytep x)
           (integerp x)))

(defruledl rationalp-when-bytep
  (implies (bytep x)
           (rationalp x)))

(defruledl acl2-numberp-when-bytep
  (implies (bytep x)
           (acl2-numberp x)))

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
    "Our preprocessor maps a file set to a file set (see @(see files)).
     It reads characters and lexes them into lexemes,
     while executing the preprocessing directives.
     The resulting sequence of lexemes is then turned into characters
     that are written into files.
     The resulting file set is amenable to our parser
     (more precisely, it will be, once we have extended our parser
     to accept @('#include') directives in certain places,
     which we plan to do).
     Our preprocessor preserves white space, in order to preserve the layout
     (modulo the inherent layout changes caused by preprocessing).
     Our preprocessor also preserves comments,
     although some comments may no longer apply to preprocessed code
     (e.g. comments talking about macros).")
   (xdoc::p
    "Currently some of this preprocessor's code duplicates, at some level,
     some of the code in the @(see parser)
     (including the @(see lexer) and the @(see reader)).
     At some point we should integrate the preprocessor into the parser.")
   (xdoc::p
    "This preprocessor is very much work in progress."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum pnumber
  :short "Fixtype of preprocessing numbers [C17:6.4.8] [C17:A.1.9]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like an abstract syntax for preprocessing numbers,
     corresponding to the rule for @('pp-number') in the ABNF grammar.
     We need to capture their structure, in order to do preprocessing."))
  (:digit ((digit character
                  :reqfix (if (str::dec-digit-char-p digit)
                              digit
                            #\0)))
   :require (str::dec-digit-char-p digit))
  (:dot-digit ((digit character
                      :reqfix (if (str::dec-digit-char-p digit)
                                  digit
                                #\0)))
   :require (str::dec-digit-char-p digit))
  (:number-digit ((number pnumber)
                  (digit character
                         :reqfix (if (str::dec-digit-char-p digit)
                                     digit
                                   #\0)))
   :require (str::dec-digit-char-p digit))
  (:number-nondigit ((number pnumber)
                     (nondigit character
                               :reqfix (if (str::letter/uscore-char-p nondigit)
                                           nondigit
                                         #\_)))
   :require (str::letter/uscore-char-p nondigit))
  (:number-locase-e-sign ((number pnumber)
                          (sign sign)))
  (:number-upcase-e-sign ((number pnumber)
                          (sign sign)))
  (:number-locase-p-sign ((number pnumber)
                          (sign sign)))
  (:number-upcase-p-sign ((number pnumber)
                          (sign sign)))
  (:number-dot ((number pnumber)))
  :pred pnumberp
  :prepwork ((set-induction-depth-limit 1)
             (local (in-theory (enable fix (:e str::letter/uscore-char-p))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum newline
  :short "Fixtype of new lines."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to the rule @('new-line') in the ABNF grammar.
     Our preprocessor does not collapse them into a single new-line
     because it preserves white space, which includes new lines."))
  (:lf ())
  (:cr ())
  (:crlf ())
  :pred newlinep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum plexeme
  :short "Fixtype of preprocessing lexems."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of preprocessing tokens [C17:6.4] [C17:A.1.1],
     with the addition of comments and white space.")
   (xdoc::p
    "We reuse some of the fixtypes for ASTs here.")
   (xdoc::p
    "The @(':other') case corresponds to
     the last alternative in the ABNF grammar rule for @('preprocessing-token'),
     as well as the prose description of the rule in [C17].
     It consists of the code of the character.")
   (xdoc::p
    "For (block and line) comments, we include the content,
     consisting of the codes of the characters.
     For block comments, these are all the characters
     from just after the opening @('/*') to just before the closing @('*/').
     For line comments, these are all the characters
     from just after the opening @('//') to just before the closing new-line.")
   (xdoc::p
    "We keep the information about the three possible kinds of new-line,
     and of all other white space characters,
     according to the ABNF grammar rule for @('white-space').
     Since spaces (code 32) often occur in consecutive chunks,
     we represent them more efficiently as chunks, via positive counts."))
  (:header ((name header-name)))
  (:ident ((ident ident)))
  (:number ((number pnumber)))
  (:char ((const cconst)))
  (:string ((literal stringlit)))
  (:punctuator ((punctuator string)))
  (:other ((char nat)))
  (:block-comment ((content nat-list)))
  (:line-comment ((content nat-list)))
  (:newline ((chars newline)))
  (:spaces ((count pos)))
  (:horizontal-tab ())
  (:vertical-tab ())
  (:form-feed ())
  :pred plexemep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-plexeme
  :short "An irrelevant preprocessing lexeme."
  :type plexemep
  :body (plexeme-ident (ident :irrelevant)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod plexeme+span
  :short "Fixtype of pairs consisting of a lexeme and a span."
  ((lexeme plexeme)
   (span span))
  :pred plexeme+span-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist plexeme+span-list
  :short "Fixtype of lists of pairs consisting of a lexeme and a span."
  :elt-type plexeme+span
  :true-listp t
  :elementp-of-nil nil
  :pred plexeme+span-listp

  ///

  (defruled plexeme+span-listp-of-resize-list
    (implies (and (plexeme+span-listp lexemes)
                  (plexeme+span-p default))
             (plexeme+span-listp (resize-list lexemes length default)))
    :induct t
    :enable (resize-list))

  (defruled plexeme+span-listp-of-update-nth-strong
    (implies (plexeme+span-listp lexemes)
             (equal (plexeme+span-listp (update-nth i lexeme lexemes))
                    (and (plexeme+span-p lexeme)
                         (<= (nfix i) (len lexemes)))))
    :induct t
    :enable (update-nth nfix zp len)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ppstate
  :short "Fixtype of preprocessor states."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee parstate), but for the preprocessor.")
   (xdoc::p
    "Our preprocessing functions take and return preprocessor states.")
   (xdoc::p
    "The preprocessor state is a stobj, which we turn into a fixtype
     by adding a fixer along with readers and writers
     that fix their inputs and unconditionally return typed outputs.
     The use of a stobj is an optimization for speed:
     conceptually,
     the preprocessor state could be defined as a @(tsee fty::defprod).")
   (xdoc::p
    "The components of the preprocessor state
     are analogous to the ones of the parser state:
     see the documentation of @(tsee parstate) first.
     The only difference is that the processor state
     contains (preprocessing) lexemes instead of tokens,
     because our preprocessor preserves comments and white space."))

  ;; needed for DEFSTOBJ and reader/writer proofs:

  (local (in-theory (enable length)))

  ;; stobj definition:

  (make-event
   `(defstobj ppstate
      (bytes :type (satisfies byte-listp)
             :initially nil)
      (position :type (satisfies positionp)
                :initially ,(irr-position))
      (chars :type (array (satisfies char+position-p) (1))
             :initially ,(make-char+position :char 0
                                             :position (irr-position))
             :resizable t)
      (chars-read :type (integer 0 *)
                  :initially 0)
      (chars-unread :type (integer 0 *)
                    :initially 0)
      (lexemes :type (array (satisfies plexeme+span-p) (1))
               :initially ,(make-plexeme+span :lexeme (irr-plexeme)
                                              :span (irr-span))
               :resizable t)
      (lexemes-read :type (integer 0 *)
                    :initially 0)
      (lexemes-unread :type (integer 0 *)
                      :initially 0)
      (version :type (satisfies c::versionp)
               :initially ,(c::version-c23))
      (size :type (integer 0 *)
            :initially 0)
      :renaming (;; field recognizers:
                 (bytesp raw-ppstate->bytes-p)
                 (positionp raw-ppstate->position-p)
                 (charsp raw-ppstate->chars-p)
                 (chars-readp raw-ppstate->chars-read-p)
                 (chars-unreadp raw-ppstate->chars-unread-p)
                 (lexemesp raw-ppstate->lexemes-p)
                 (lexemes-readp raw-ppstate->lexemes-read-p)
                 (lexemes-unreadp raw-ppstate->lexemes-unread-p)
                 (versionp raw-ppstate->version-p)
                 (sizep raw-ppstate->size-p)
                 ;; field readers:
                 (bytes raw-ppstate->bytes)
                 (position raw-ppstate->position)
                 (chars-length raw-ppstate->chars-length)
                 (charsi raw-ppstate->char)
                 (chars-read raw-ppstate->chars-read)
                 (chars-unread raw-ppstate->chars-unread)
                 (lexemes-length raw-ppstate->lexemes-length)
                 (lexemesi raw-ppstate->lexeme)
                 (lexemes-read raw-ppstate->lexemes-read)
                 (lexemes-unread raw-ppstate->lexemes-unread)
                 (version raw-ppstate->version)
                 (size raw-ppstate->size)
                 ;; field writers:
                 (update-bytes raw-update-ppstate->bytes)
                 (update-position raw-update-ppstate->position)
                 (resize-chars raw-update-ppstate->chars-length)
                 (update-charsi raw-update-ppstate->char)
                 (update-chars-read raw-update-ppstate->chars-read)
                 (update-chars-unread raw-update-ppstate->chars-unread)
                 (resize-lexemes raw-update-ppstate->lexemes-length)
                 (update-lexemesi raw-update-ppstate->lexeme)
                 (update-lexemes-read raw-update-ppstate->lexemes-read)
                 (update-lexemes-unread raw-update-ppstate->lexemes-unread)
                 (update-version raw-update-ppstate->version)
                 (update-size raw-update-ppstate->size))))

  ;; fixer:

  (define ppstate-fix (ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (if (ppstatep ppstate)
                    ppstate
                  (create-ppstate))
         :exec ppstate)
    ///
    (defrule ppstate-fix-when-ppstatep
      (implies (ppstatep ppstate)
               (equal (ppstate-fix ppstate)
                      ppstate))))

  ;; fixtype:

  (fty::deffixtype ppstate
    :pred ppstatep
    :fix ppstate-fix
    :equiv ppstate-equiv
    :define t
    :executablep nil)

  ;; normalize recognizers:

  (defrule raw-ppstate->chars-p-becomes-char+position-listp
    (equal (raw-ppstate->chars-p x)
           (char+position-listp x))
    :induct t
    :enable (raw-ppstate->chars-p
             char+position-listp))

  (defrule raw-ppstate->lexemes-p-becomes-plexeme+span-listp
    (equal (raw-ppstate->lexemes-p x)
           (plexeme+span-listp x))
    :induct t
    :enable (raw-ppstate->lexemes-p
             plexeme+span-listp))

  ;; needed for reader/writer proofs:

  (local (in-theory (enable ppstate-fix)))

  ;; readers:

  (define ppstate->bytes (ppstate)
    :returns (bytes byte-listp)
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->bytes ppstate)
                  nil)
         :exec (raw-ppstate->bytes ppstate))
    :hooks (:fix)
    ///
    (more-returns
     (bytes true-listp :rule-classes :type-prescription)))

  (define ppstate->position (ppstate)
    :returns (position positionp)
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->position ppstate)
                  (irr-position))
         :exec (raw-ppstate->position ppstate)))

  (define ppstate->chars-length (ppstate)
    :returns (length natp)
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->chars-length ppstate)
                  1)
         :exec (raw-ppstate->chars-length ppstate))
    :hooks (:fix))

  (define ppstate->char ((i natp) ppstate)
    :guard (< i (ppstate->chars-length ppstate))
    :returns (char+pos char+position-p
                       :hints
                       (("Goal" :in-theory (enable ppstate->chars-length))))
    (mbe :logic (if (and (ppstatep ppstate)
                         (< (nfix i) (ppstate->chars-length ppstate)))
                    (raw-ppstate->char (nfix i) ppstate)
                  (make-char+position :char 0
                                      :position (irr-position)))
         :exec (raw-ppstate->char i ppstate))
    :guard-hints (("Goal" :in-theory (enable nfix ppstate->chars-length))))

  (define ppstate->chars-read (ppstate)
    :returns (chars-read natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->chars-read ppstate)
                  0)
         :exec (raw-ppstate->chars-read ppstate))
    :hooks (:fix))

  (define ppstate->chars-unread (ppstate)
    :returns (chars-unread natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->chars-unread ppstate)
                  0)
         :exec (raw-ppstate->chars-unread ppstate))
    :hooks (:fix))

  (define ppstate->lexemes-length (ppstate)
    :returns (length natp)
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->lexemes-length ppstate)
                  1)
         :exec (raw-ppstate->lexemes-length ppstate))
    :hooks (:fix))

  (define ppstate->lexeme ((i natp) ppstate)
    :guard (< i (ppstate->lexemes-length ppstate))
    :returns (lexeme+span plexeme+span-p
                          :hints
                          (("Goal" :in-theory (enable ppstate->lexemes-length))))
    (mbe :logic (if (and (ppstatep ppstate)
                         (< (nfix i) (ppstate->lexemes-length ppstate)))
                    (raw-ppstate->lexeme (nfix i) ppstate)
                  (make-plexeme+span :lexeme (irr-plexeme)
                                     :span (irr-position)))
         :exec (raw-ppstate->lexeme i ppstate))
    :guard-hints (("Goal" :in-theory (enable nfix ppstate->lexemes-length))))

  (define ppstate->lexemes-read (ppstate)
    :returns (lexemes-read natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->lexemes-read ppstate)
                  0)
         :exec (raw-ppstate->lexemes-read ppstate))
    :hooks (:fix))

  (define ppstate->lexemes-unread (ppstate)
    :returns (lexemes-unread natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->lexemes-unread ppstate)
                  0)
         :exec (raw-ppstate->lexemes-unread ppstate))
    :hooks (:fix))

  (define ppstate->version (ppstate)
    :returns (version c::versionp)
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->version ppstate)
                  (c::version-c23))
         :exec (raw-ppstate->version ppstate))
    :hooks (:fix))

  (define ppstate->size (ppstate)
    :returns (size natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->size ppstate)
                  0)
         :exec (raw-ppstate->size ppstate))
    :hooks (:fix))

  ;; writers:

  (define update-ppstate->bytes ((bytes byte-listp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->bytes (byte-list-fix bytes) ppstate))
    :hooks (:fix))

  (define update-ppstate->position ((position positionp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->position (position-fix position) ppstate))
    :hooks (:fix))

  (define update-ppstate->chars-length ((length natp) ppstate)
    :returns (ppstate ppstatep
                      :hints
                      (("Goal"
                        :in-theory
                        (enable nfix
                                ppstate-fix
                                length
                                char+position-listp-of-resize-list))))
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->chars-length (nfix length) ppstate))
    :hooks (:fix))

  (define update-ppstate->char ((i natp)
                                (char+pos char+position-p)
                                ppstate)
    :guard (< i (ppstate->chars-length ppstate))
    :returns (ppstate ppstatep
                      :hints
                      (("Goal"
                        :in-theory
                        (enable update-nth-array
                                ppstate->chars-length
                                char+position-listp-of-update-nth-strong))))
    (b* ((ppstate (ppstate-fix ppstate)))
      (mbe :logic (if (< (nfix i) (ppstate->chars-length ppstate))
                      (raw-update-ppstate->char (nfix i)
                                                (char+position-fix char+pos)
                                                ppstate)
                    ppstate)
           :exec (raw-update-ppstate->char i char+pos ppstate)))
    :guard-hints (("Goal" :in-theory (enable ppstate->chars-length nfix))))

  (define update-ppstate->chars-read ((chars-read natp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->chars-read (nfix chars-read) ppstate))
    :hooks (:fix))

  (define update-ppstate->chars-unread ((chars-unread natp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->chars-unread (nfix chars-unread) ppstate))
    :hooks (:fix))

  (define update-ppstate->lexemes-length ((length natp) ppstate)
    :returns (ppstate ppstatep
                      :hints
                      (("Goal"
                        :in-theory (enable nfix
                                           ppstate-fix
                                           length
                                           plexeme+span-listp-of-resize-list))))
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->lexemes-length (nfix length) ppstate))
    :hooks (:fix))

  (define update-ppstate->lexeme ((i natp)
                                  (lexeme+span plexeme+span-p)
                                  ppstate)
    :guard (< i (ppstate->lexemes-length ppstate))
    :returns (ppstate ppstatep
                      :hints
                      (("Goal"
                        :in-theory
                        (enable update-nth-array
                                ppstate->lexemes-length
                                plexeme+span-listp-of-update-nth-strong))))
    (b* ((ppstate (ppstate-fix ppstate)))
      (mbe :logic (if (< (nfix i) (ppstate->lexemes-length ppstate))
                      (raw-update-ppstate->lexeme (nfix i)
                                                  (plexeme+span-fix lexeme+span)
                                                  ppstate)
                    ppstate)
           :exec (raw-update-ppstate->lexeme i lexeme+span ppstate)))
    :guard-hints (("Goal" :in-theory (enable ppstate->lexemes-length nfix))))

  (define update-ppstate->lexemes-read ((lexemes-read natp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->lexemes-read (nfix lexemes-read) ppstate))
    :hooks (:fix))

  (define update-ppstate->lexemes-unread ((lexemes-unread natp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->lexemes-unread (nfix lexemes-unread) ppstate))
    :hooks (:fix))

  (define update-ppstate->version ((version c::versionp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->version (c::version-fix version) ppstate))
    :hooks (:fix))

  (define update-ppstate->size ((size natp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->size (lnfix size) ppstate))
    :hooks (:fix))

  ;; readers over writers:

  (defrule ppstate->chars-length-of-update-ppstate->bytes
    (equal (ppstate->chars-length (update-ppstate->bytes bytes ppstate))
           (ppstate->chars-length ppstate))
    :enable (ppstate->chars-length
             update-ppstate->bytes
             ppstatep
             ppstate-fix
             length))

  (defrule ppstate->size-of-update-ppstate->bytes
    (equal (ppstate->size (update-ppstate->bytes bytes ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->bytes
             ppstatep
             ppstate-fix
             length))

  (defrule ppstate->size-of-update-ppstate->position
    (equal (ppstate->size (update-ppstate->position position ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->position
             ppstatep
             ppstate-fix
             length))

  (defrule ppstate->size-of-update-ppstate->chars-read
    (equal (ppstate->size (update-ppstate->chars-read chars-read ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->chars-read
             ppstatep
             ppstate-fix
             length))

  (defrule ppstate->size-of-update-ppstate->chars-unread
    (equal (ppstate->size (update-ppstate->chars-unread chars-unread
                                                        ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->chars-unread
             ppstatep
             ppstate-fix
             length))

  (defrule ppstate->size-of-update-ppstate->lexeme
    (equal (ppstate->size (update-ppstate->lexeme i lexeme ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->lexeme
             ppstatep
             ppstate-fix
             length
             update-nth-array
             ppstate->lexemes-length
             plexeme+span-listp-of-update-nth-strong))

  (defrule ppstate->size-of-update-ppstate->lexemes-read
    (equal (ppstate->size (update-ppstate->lexemes-read lexemes-read ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->lexemes-read
             ppstatep
             ppstate-fix
             length))

  (defrule ppstate->size-of-update-ppstate->size
    (equal (ppstate->size (update-ppstate->size size ppstate))
           (lnfix size))
    :enable (ppstate->size
             update-ppstate->size
             ppstatep
             ppstate-fix
             length))

  ;; writers over readers:

  (defrule update-ppstate->chars-read-of-ppstate->chars-read
    (equal (update-ppstate->chars-read
            (ppstate->chars-read ppstate) ppstate)
           (ppstate-fix ppstate))
    :enable (update-ppstate->chars-read
             ppstate->chars-read
             ppstatep
             ppstate-fix
             nfix
             length
             acl2::update-nth-of-nth))

  (defrule update-ppstate->chars-read-of-ppstate->chars-unread
    (equal (update-ppstate->chars-unread
            (ppstate->chars-unread ppstate) ppstate)
           (ppstate-fix ppstate))
    :enable (update-ppstate->chars-unread
             ppstate->chars-unread
             ppstatep
             ppstate-fix
             nfix
             length
             acl2::update-nth-of-nth))

  ;; keep recognizer disabled:

  (in-theory (disable ppstatep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-ppstate ((data byte-listp) (version c::versionp) ppstate)
  :returns (ppstate ppstatep)
  :short "Initialize the preprocessor state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the state when we start preprocessing a file.
     Given (the data of) a file to preprocess,
     and a C version,
     the initial preprocessing state consists of
     the data to preprocess,
     no read characters or lexemes,
     no unread characters or lexemes,
     and the initial file position.
     We also resize the arrays of characters and lexemes
     to the number of data bytes,
     which is overkill but certainly sufficient
     (because we will never lex more characters or lexemes than bytes);
     if this turns out to be too large,
     we will pick a different size,
     but then we may need to resize the array as needed
     while preprocessing."))
  (b* ((ppstate (update-ppstate->bytes data ppstate))
       (ppstate (update-ppstate->position (position-init) ppstate))
       (ppstate (update-ppstate->chars-length (len data) ppstate))
       (ppstate (update-ppstate->chars-read 0 ppstate))
       (ppstate (update-ppstate->chars-unread 0 ppstate))
       (ppstate (update-ppstate->lexemes-length (len data) ppstate))
       (ppstate (update-ppstate->lexemes-read 0 ppstate))
       (ppstate (update-ppstate->lexemes-unread 0 ppstate))
       (ppstate (update-ppstate->version version ppstate))
       (ppstate (update-ppstate->size (len data) ppstate)))
    ppstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pchar-to-msg ((char nat-optionp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp
                                                   character-alistp))))
  :short "Represent an optional character as a message,
          in the preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is almost identical to @(tsee char-to-msg)
     (see its documentation first)
     with the difference that we consider LF and CR separately.
     This matches the fact that @(tsee pread-char), unlike @(tsee read-char),
     does not normalize the three possible kinds of new lines to LF."))
  (cond ((not char) "end of file")
        ((< char 32) (msg "the ~s0 character (ASCII code ~x1)"
                          (nth char *pchar-to-msg-ascii-control-char-names*)
                          char))
        ((= char 32) "the SP (space) character (ASCII code 32)")
        ((and (<= 33 char) (<= char 126))
         (msg "the ~s0 character (ASCII code ~x1)"
              (str::implode (list (code-char char))) char))
        ((= char 127) "the DEL (delete) character (ASCII code 127)")
        (t (msg "the non-ASCII Unicode character with code ~x0" char)))
  :guard-hints (("Goal" :in-theory (enable character-listp
                                           nat-optionp)))

  :prepwork
  ((defconst *pchar-to-msg-ascii-control-char-names*
     '("NUL"
       "SOH"
       "STX"
       "ETX"
       "EOT"
       "ENQ"
       "ACK"
       "BEL"
       "BS (backspace)"
       "HT (horizontal tab)"
       "LF (line feed)"
       "VT (vertical tab)"
       "FF (form feed)"
       "CR (carriage return)"
       "SO"
       "SI"
       "DLE"
       "DC1"
       "DC2"
       "DC3"
       "DC4"
       "NAK"
       "SYN"
       "ETB"
       "CAN"
       "EM"
       "SUB"
       "ESC"
       "FS"
       "GS"
       "RS"
       "US"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-ppstate-for-char ((char natp)
                                 (new-bytes byte-listp)
                                 (new-position positionp)
                                 (size-decrement posp)
                                 (ppstate ppstatep))
  :guard (and (< (ppstate->chars-read ppstate)
                 (ppstate->chars-length ppstate))
              (>= (ppstate->size ppstate) size-decrement))
  :returns (new-ppstate ppstatep :hyp (ppstatep ppstate))
  :short "Update the preprocessor state for a character."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when @(tsee pread-char)
     reads a character from the data bytes (not from the unread characters).
     The @('new-bytes') input consists of the remaining data bytes,
     i.e. after the one ore more bytes that form the character
     have already been removed (and decoded).
     The @('new-position') input consists of the next position,
     which is normally one column more than the current one,
     except when dealing with new-line characters."))
  (b* ((position (ppstate->position ppstate))
       (chars-read (ppstate->chars-read ppstate))
       (size (ppstate->size ppstate))
       (new-size (- size (pos-fix size-decrement)))
       (char+pos (make-char+position :char char :position position))
       (ppstate (update-ppstate->bytes new-bytes ppstate))
       (ppstate (update-ppstate->char chars-read char+pos ppstate))
       (ppstate (update-ppstate->chars-read (1+ chars-read) ppstate))
       (ppstate (update-ppstate->position new-position ppstate))
       (ppstate (update-ppstate->size new-size ppstate)))
    ppstate)
  :guard-hints (("Goal" :in-theory (enable natp)))

  ///

  (defret ppstate->size-of-update-ppstate-for-char
    (equal (ppstate->size new-ppstate)
           (- (ppstate->size ppstate)
              (pos-fix size-decrement)))
    :hyp (>= (ppstate->size ppstate)
             (pos-fix size-decrement))
    :hints (("Goal" :in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pread-char ((ppstate ppstatep))
  :returns (mv erp
               (char? nat-optionp
                      :hints (("Goal" :induct t :in-theory (enable natp))))
               (pos positionp)
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Read a character during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is almost identical to @(tsee read-char)
     (see its documentation first),
     but with some differences.")
   (xdoc::p
    "Here we perform phases 1 and 2 of [C17:5.1.1.2].")
   (xdoc::p
    "Here the implementation-defined mapping
     from physical source file multibyte characters to the source character set
     amounts to UTF-8 decoding.")
   (xdoc::p
    "Unlike @(tsee read-char),
     here we do not normalize the three kinds of new lines to LF,
     because we want to preserve line endings.
     However, we need to be careful about how we increment the current position.
     If we read a CR, we check whether it is followed by LF.
     If that is the case, the line ending is the combination of CR and LF,
     and thus we do not change the position upon reading the CR
     (as if the CR took no visual space);
     when this function is called again next,
     it will read the LF, which always changes the position to the next line.
     If instead the CR is not followed by LF,
     then the CR is the whole line ending,
     and we change the position to the next line.
     Reading an LF always changes the position to the next line,
     whether it is preceded by CR (see above) or not;
     in the latter case, the LF is the whole line ending.")
   (xdoc::p
    "If the next character is a question mark,
     we check the subsequent characters (if any)
     to see whether we have a trigraph sequence,
     which we turn into the single character it denotes [C17:5.2.1.1].")
   (xdoc::p
    "If the next character is a backslash,
     we check whether it is followed by new-line characters,
     namely CR (not followed by LF), LF, or CR LF.
     If that is the case,
     the backslash and the new-line character(s) are skipped,
     and we recursively try to read another character.
     We also ensure that the backslash-new-line being deleted
     is not at the end of the file [C17:5.1.1.2/2]."))
  (b* (((reterr) nil (irr-position) ppstate)
       (ppstate.bytes (ppstate->bytes ppstate))
       (ppstate.position (ppstate->position ppstate))
       (ppstate.chars-read (ppstate->chars-read ppstate))
       (ppstate.chars-unread (ppstate->chars-unread ppstate))
       (ppstate.size (ppstate->size ppstate))
       ((when (> ppstate.chars-unread 0))
        (b* (((unless (> ppstate.size 0))
              (raise "Internal error: ~
                      there are ~x0 unread characters ~
                      but the size of the preprocessing state is 0."
                     ppstate.chars-unread)
              (reterr t))
             ((unless (< ppstate.chars-read (ppstate->chars-length ppstate)))
              (raise "Internal error: index ~x0 out of bound ~x1."
                     ppstate.chars-read
                     (ppstate->chars-length ppstate))
              (reterr t))
             (char+pos (ppstate->char ppstate.chars-read ppstate))
             (ppstate (update-ppstate->chars-unread (1- ppstate.chars-unread)
                                                    ppstate))
             (ppstate (update-ppstate->chars-read (1+ ppstate.chars-read)
                                                  ppstate))
             (ppstate (update-ppstate->size (1- ppstate.size) ppstate)))
          (retok (char+position->char char+pos)
                 (char+position->position char+pos)
                 ppstate)))
       ((unless (consp ppstate.bytes))
        (if (> ppstate.size 0)
            (prog2$ (raise "Internal error: ~
                            there are no unread characters and no more bytes, ~
                            but the size of the preprocessing state is ~x0."
                           ppstate.size)
                    (reterr t))
          (retok nil ppstate.position ppstate)))
       ((unless (> ppstate.size 0))
        (raise "Internal error: ~
                there are more bytes but ~
                the size of the preprocessing state is 0.")
        (reterr t))
       (byte (car ppstate.bytes))
       (bytes (cdr ppstate.bytes))
       ((unless (< ppstate.chars-read (ppstate->chars-length ppstate)))
        (raise "Internal error: index ~x0 out of bound ~x1."
               ppstate.chars-read
               (ppstate->chars-length ppstate))
        (reterr t))
       ;; new lines:
       ((when (= byte 13)) ; CR
        (b* ((lf-follows-cr-p (and (consp bytes) (= (car bytes) 10)))
             (new-position (if lf-follows-cr-p
                               ppstate.position
                             (position-inc-line 1 ppstate.position)))
             (ppstate
              (update-ppstate-for-char 13 bytes new-position 1 ppstate)))
          (retok 13 ppstate.position ppstate)))
       ((when (= byte 10)) ; LF
        (b* ((new-position (position-inc-line 1 ppstate.position))
             (ppstate
              (update-ppstate-for-char 10 bytes new-position 1 ppstate)))
          (retok 10 ppstate.position ppstate)))
       ;; trigraph sequences (or just '?'):
       ((when (= byte (char-code #\?))) ; ?
        (b* (((mv char new-bytes num-chars/bytes)
              (if (and (consp bytes)
                       (= (car bytes) (char-code #\?)) ; ??
                       (consp (cdr bytes)))
                  (b* (((unless (>= ppstate.size 3))
                        (raise "Internal error: ~
                                there are three or more bytes ~
                                but the size of the preprocessing state is ~x0."
                               ppstate.size)
                        (mv 0 nil 1)))
                    (cond ((= (cadr bytes) (char-code #\=)) ; ??=
                           (mv (char-code #\#) (cddr bytes) 3))
                          ((= (cadr bytes) (char-code #\()) ; ??(
                           (mv (char-code #\[) (cddr bytes) 3))
                          ((= (cadr bytes) (char-code #\/)) ; ??/
                           (mv (char-code #\\) (cddr bytes) 3))
                          ((= (cadr bytes) (char-code #\))) ; ??)
                           (mv (char-code #\]) (cddr bytes) 3))
                          ((= (cadr bytes) (char-code #\')) ; ??'
                           (mv (char-code #\^) (cddr bytes) 3))
                          ((= (cadr bytes) (char-code #\<)) ; ??<
                           (mv (char-code #\{) (cddr bytes) 3))
                          ((= (cadr bytes) (char-code #\!)) ; ??!
                           (mv (char-code #\|) (cddr bytes) 3))
                          ((= (cadr bytes) (char-code #\>)) ; ??>
                           (mv (char-code #\}) (cddr bytes) 3))
                          ((= (cadr bytes) (char-code #\-)) ; ??-
                           (mv (char-code #\~) (cddr bytes) 3))
                          (t (mv byte bytes 1)))) ; just ?, not a tripgraph
                (mv byte bytes 1))) ; just ?, not a trigraph
             (new-position
              (position-inc-column num-chars/bytes ppstate.position))
             (ppstate
              (update-ppstate-for-char
               char new-bytes new-position num-chars/bytes ppstate)))
          (retok char ppstate.position ppstate)))
       ;; line splicing (or just '\'):
       ((when (= byte (char-code #\\))) ; \
        (b* (((when (endp bytes)) ; \ EOF
              (reterr (msg "File ends with backslash instead of new line.")))
             ((when (= (car bytes) 10)) ; \ LF
              (b* (((unless (>= ppstate.size 2))
                    (raise "Internal error: ~
                            there are two or more bytes ~
                            but the size of the preprocessing state is ~x0."
                           ppstate.size)
                    (reterr t))
                   (new-bytes (cdr bytes))
                   (new-position (position-inc-line 1 ppstate.position))
                   (new-size (- ppstate.size 2))
                   (ppstate (update-ppstate->bytes new-bytes ppstate))
                   (ppstate (update-ppstate->position new-position ppstate))
                   (ppstate (update-ppstate->size new-size ppstate))
                   ((unless (consp new-bytes))
                    (reterr (msg "File ends with backslash and new line."))))
                (pread-char ppstate)))
             ((when (= (car bytes) 13)) ; \ CR
              (if (and (consp (cdr bytes))
                       (= (cadr bytes) 10)) ; \ CR LF
                  (b* (((when (endp (cddr bytes))) ; \ CR LF EOF
                        (reterr (msg "File ends with backslash and new line ~
                                      instead of new line.")))
                       ((unless (>= ppstate.size 3))
                        (raise "Internal error: ~
                                there are three or more bytes ~
                                but the size of the preprocessing state is ~x0."
                               ppstate.size)
                        (reterr t))
                       (new-bytes (cddr bytes))
                       (new-position (position-inc-line 1 ppstate.position))
                       (new-size (- ppstate.size 3))
                       (ppstate (update-ppstate->bytes new-bytes ppstate))
                       (ppstate (update-ppstate->position new-position ppstate))
                       (ppstate (update-ppstate->size new-size ppstate))
                       ((unless (consp new-bytes))
                        (reterr
                         (msg "File ends with backslash and new line."))))
                    (pread-char ppstate))
                (b* (((when (endp (cdr bytes))) ; \ CR EOF
                      (reterr (msg "File ends with backslash and new line ~
                                    instead of new line.")))
                     ((unless (>= ppstate.size 2))
                      (raise "Internal error: ~
                              there are three or more bytes ~
                              but the size of the preprocessing state is ~x0."
                             ppstate.size)
                      (reterr t))
                     (new-bytes (cdr bytes))
                     (new-position (position-inc-line 1 ppstate.position))
                     (new-size (- ppstate.size 2))
                     (ppstate (update-ppstate->bytes new-bytes ppstate))
                     (ppstate (update-ppstate->position new-position ppstate))
                     (ppstate (update-ppstate->size new-size ppstate))
                     ((unless (consp new-bytes))
                      (reterr (msg "File ends with backslash and new line."))))
                  (pread-char ppstate))))
             ;; just \, no line splicing
             (new-position (position-inc-column 1 ppstate.position))
             (ppstate
              (update-ppstate-for-char byte bytes new-position 1 ppstate)))
          (retok byte ppstate.position ppstate)))
       ;; other ASCII:
       ((when (or (= byte 9) ; HT
                  (= byte 11) ; VT
                  (= byte 12) ; FF
                  (and (<= 32 byte) (<= byte 126))))
        (b* ((new-position (position-inc-column 1 ppstate.position))
             (ppstate
              (update-ppstate-for-char byte bytes new-position 1 ppstate)))
          (retok byte ppstate.position ppstate)))
       ;; 2-byte UTF-8:
       ((when (= (logand byte #b11100000) #b11000000)) ; 110xxxyy
        (b* (((unless (consp bytes))
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 110... ~
                                          (i.e. between 192 and 223) ~
                                          of a two-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
             ((unless (>= ppstate.size 2))
              (raise "Internal error: ~
                      there are two or more bytes ~
                      but the size of the preprocessing state is ~x0."
                     ppstate.size)
              (reterr t))
             (byte2 (car bytes))
             (bytes (cdr bytes))
             ((unless (= (logand byte2 #b11000000) #b10000000)) ; 10yyzzzz
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 110... ~
                                          (i.e. between 192 and 223) ~
                                          of a two-byte UTF-8 encoding"
                                         byte)
                          :found (msg "the byte ~x0" byte2)))
             (code (+ (ash (logand byte #b00011111) 6)
                      (logand byte2 #b00111111)))
             ((when (< code #x80))
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "a value between 80h and 7FFh ~
                                          UTF-8-encoded in the two bytes ~
                                          (~x0 ~x1)"
                                         byte byte2)
                          :found (msg "the value ~x0" code)))
             (new-position (position-inc-column 1 ppstate.position))
             (ppstate
              (update-ppstate-for-char code bytes new-position 2 ppstate)))
          (retok code ppstate.position ppstate)))
       ;; 3-byte UTF-8:
       ((when (= (logand byte #b11110000) #b11100000)) ; 1110xxxx
        (b* (((unless (consp bytes))
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 1110... ~
                                          (i.e. between 224 to 239) ~
                                          of a three-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
             ((unless (>= ppstate.size 2))
              (raise "Internal error: ~
                      there are two or more bytes ~
                      but the size of the preprocessing state is ~x0."
                     ppstate.size)
              (reterr t))
             (byte2 (car bytes))
             (bytes (cdr bytes))
             ((unless (= (logand byte2 #b11000000) #b10000000)) ; 10yyyyzz
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 1110... ~
                                          (i.e. between 224 and 239) ~
                                          of a three-byte UTF-8 encoding"
                                         byte)
                          :found (msg "the byte ~x0" byte2)))
             ((unless (consp bytes))
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 1110... ~
                                          (i.e. between 224 to 239) ~
                                          and the second byte ~x1 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          of a three-byte UTF-8 encoding"
                                         byte byte2)
                          :found "end of file"))
             ((unless (>= ppstate.size 3))
              (raise "Internal error: ~
                      there are three or more bytes ~
                      but the size of the preprocessing state is ~x0."
                     ppstate.size)
              (reterr t))
             (byte3 (car bytes))
             (bytes (cdr bytes))
             ((unless (= (logand byte3 #b11000000) #b10000000)) ; 10zzwwww
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 1110... ~
                                          (i.e. between 224 and 239) ~
                                          and the second byte ~x1 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          of a three-byte UTF-8 encoding"
                                         byte byte2)
                          :found (msg "the byte ~x0" byte3)))
             (code (+ (ash (logand byte #b00001111) 12)
                      (ash (logand byte2 #b00111111) 6)
                      (logand byte3 #b00111111)))
             ((when (< code #x800))
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "a value between 800h and FFFFh ~
                                          UTF-8-encoded in the three bytes ~
                                          (~x0 ~x1 ~x2)"
                                         byte byte2 byte3)
                          :found (msg "the value ~x0" code)))
             ((when (or (and (<= #x202a code)
                             (<= code #x202e))
                        (and (<= #x2066 code)
                             (<= code #x2069))))
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected "a Unicode character with code ~
                                     in the range 9-13 or 32-126 ~
                                     or 128-8233 or 8239-8293 or ~
                                     or 8298-55295 or 57344-1114111"
                          :found (char-to-msg code)))
             (new-position (position-inc-column 1 ppstate.position))
             (ppstate
              (update-ppstate-for-char code bytes new-position 3 ppstate)))
          (retok code ppstate.position ppstate)))
       ;; 4-byte UTF-8:
       ((when (= (logand #b11111000 byte) #b11110000)) ; 11110xyy
        (b* (((unless (consp bytes))
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 to 247) ~
                                          of a four-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
             ((unless (>= ppstate.size 2))
              (raise "Internal error: ~
                      there are two or more bytes ~
                      but the size of the preprocessing state is ~x0."
                     ppstate.size)
              (reterr t))
             (byte2 (car bytes))
             (bytes (cdr bytes))
             ((unless (= (logand byte2 #b11000000) #b10000000)) ; 10yyzzzz
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 and 247) ~
                                          of a four-byte UTF-8 encoding"
                                         byte)
                          :found (msg "the byte ~x0" byte2)))
             ((unless (consp bytes))
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 to 247) ~
                                          and the second byte ~x1 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          of a four-byte UTF-8 encoding"
                                         byte byte2)
                          :found "end of file"))
             ((unless (>= ppstate.size 3))
              (raise "Internal error: ~
                      there are three or more bytes ~
                      but the size of the preprocessing state is ~x0."
                     ppstate.size)
              (reterr t))
             (byte3 (car bytes))
             (bytes (cdr bytes))
             ((unless (= (logand byte3 #b11000000) #b10000000)) ; 10wwwwuu
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 and 247) ~
                                          and the second byte ~x1 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          of a four-byte UTF-8 encoding"
                                         byte byte2)
                          :found (msg "the byte ~x0" byte3)))
             ((unless (consp bytes))
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 to 247) ~
                                          and the second byte ~x1 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          and the third byte ~x2 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          of a four-byte UTF-8 encoding"
                                         byte byte2 byte3)
                          :found "end of file"))
             ((unless (>= ppstate.size 4))
              (raise "Internal error: ~
                      there are four or more bytes ~
                      but the size of the preprocessing state is ~x0."
                     ppstate.size)
              (reterr t))
             (byte4 (car bytes))
             (bytes (cdr bytes))
             ((unless (= (logand byte4 #b11000000) #b10000000)) ; 10uuvvvv
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 and 247) ~
                                          and the second byte ~x1 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          and the third byte ~x2 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          of a four-byte UTF-8 encoding"
                                         byte byte2 byte3)
                          :found (msg "the byte ~x0" byte4)))
             (code (+ (ash (logand byte #b00000111) 18)
                      (ash (logand byte2 #b00111111) 12)
                      (ash (logand byte3 #b00111111) 6)
                      (logand byte4 #b00111111)))
             ((when (or (< code #x10000)
                        (> code #x10ffff)))
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "a value between 10000h and 10FFFFh ~
                                          UTF-8-encoded in the four bytes ~
                                          (~x0 ~x1 ~x2 ~x3)"
                                         byte byte2 byte3 byte4)
                          :found (msg "the value ~x0" code)))
             (new-position (position-inc-column 1 ppstate.position))
             (ppstate
              (update-ppstate-for-char code bytes new-position 3 ppstate)))
          (retok code ppstate.position ppstate))))
    (reterr-msg :where (position-to-msg ppstate.position)
                :expected "a byte in the range 9-13 or 32-126 or 192-223"
                :found (msg "the byte ~x0" byte)))
  :measure (ppstate->size ppstate)
  :hints (("Goal" :in-theory (enable nfix)))
  :guard-hints (("Goal" :in-theory (enable len fix natp)))
  :prepwork ((local (in-theory (enable acl2-numberp-when-bytep
                                       rationalp-when-bytep
                                       integerp-when-bytep))))

  ///

  (defret ppstate->size-of-pread-char-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal"
             :induct t
             :in-theory (enable nfix))))

  (defret ppstate->size-of-pread-char-cond
    (implies (and (not erp)
                  char?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear
    :hints (("Goal"
             :induct t
             :in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define punread-char ((ppstate ppstatep))
  :returns (new-ppstate ppstatep :hyp (ppstatep ppstate))
  :short "Unread a character during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "We move the character from the sequence of read characters
     to the sequence of unread characters,
     by incrementing @('chars-unread') and decrementing @('chars-read').")
   (xdoc::p
    "It is an internal error if @('chars-read') is 0.
     It means that the calling code is wrong.
     In this case, after raising the hard error,
     logically we return a preprocessing state
     where we still increment @('chars-unread')
     so that the theorem about @(tsee ppstate->size) holds unconditionally."))
  (b* ((ppstate.chars-read (ppstate->chars-read ppstate))
       (ppstate.chars-unread (ppstate->chars-unread ppstate))
       (ppstate.size (ppstate->size ppstate))
       ((unless (> ppstate.chars-read 0))
        (raise "Internal error: no character to unread.")
        (b* ((ppstate (update-ppstate->chars-unread (1+ ppstate.chars-unread)
                                                      ppstate))
             (ppstate (update-ppstate->size (1+ ppstate.size) ppstate)))
          ppstate))
       (ppstate (update-ppstate->chars-read (1- ppstate.chars-read)
                                              ppstate))
       (ppstate (update-ppstate->chars-unread (1+ ppstate.chars-unread)
                                                ppstate))
       (ppstate (update-ppstate->size (1+ ppstate.size) ppstate)))
    ppstate)
  :guard-hints (("Goal" :in-theory (enable natp)))

  ///

  (defret ppstate->size-of-punread-char
    (equal (ppstate->size new-ppstate)
           (1+ (ppstate->size ppstate)))
    :hints (("Goal" :in-theory (enable len nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define punread-chars ((n natp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep :hyp (ppstatep ppstate))
  :short "Unread a specified number of characters during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "We move characters
     from the sequence of read characters
     to the sequence of unread characters
     by incrementing the number of unread characters by @('n')
     and decrementing the number of read characters by @('n').")
   (xdoc::p
    "It is an internal error if @('n') exceeds
     the number of character read so far.
     In this case, after raising the hard error,
     logically we return a preprocessing state
     where we still increment @('chars-unread')
     so that the theorem about @(tsee ppstate->size) holds unconditionally."))
  (b* ((n (nfix n))
       (chars-read (ppstate->chars-read ppstate))
       (chars-unread (ppstate->chars-unread ppstate))
       (size (ppstate->size ppstate))
       ((unless (<= n chars-read))
        (raise "Internal error: ~
                attempting to unread ~x0 characters ~
                from ~x1 read characters."
               n chars-read)
        (b* ((ppstate
              (update-ppstate->chars-unread (+ chars-unread n) ppstate))
             (ppstate
              (update-ppstate->size (+ size n) ppstate)))
          ppstate))
       (new-chars-read (- chars-read n))
       (new-chars-unread (+ chars-unread n))
       (new-size (+ size n))
       (ppstate (update-ppstate->chars-read new-chars-read ppstate))
       (ppstate (update-ppstate->chars-unread new-chars-unread ppstate))
       (ppstate (update-ppstate->size new-size ppstate)))
    ppstate)
  :guard-hints (("Goal" :in-theory (enable natp)))

  ///

  (defret ppstate->size-of-punread-chars
    (equal (ppstate->size new-ppstate)
           (+ (ppstate->size ppstate) (nfix n)))
    :hints (("Goal" :in-theory (enable nfix fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: continue
