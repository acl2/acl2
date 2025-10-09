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

(include-book "kestrel/fty/character-list" :dir :system)
(include-book "std/strings/letter-uscore-chars" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (:e tau-system))))
(set-induction-depth-limit 0)

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
      (gcc :type (satisfies booleanp)
           :initially nil)
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
                 (gccp raw-ppstate->gcc-p)
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
                 (gcc raw-ppstate->gcc)
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
                 (update-gcc raw-update-ppstate->gcc)
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

  (define ppstate->gcc (ppstate)
    :returns (gcc booleanp)
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->gcc ppstate)
                  nil)
         :exec (raw-ppstate->gcc ppstate))
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

  (define update-ppstate->gcc ((gcc booleanp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->gcc (bool-fix gcc) ppstate))
    :hooks (:fix))

  (define update-ppstate->size ((size natp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->size (lnfix size) ppstate))
    :hooks (:fix))

  ;; readers over writers:

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
