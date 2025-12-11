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

(include-book "std/strings/letter-uscore-chars" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))

(acl2::controlled-configuration)

; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor-states
  :parents (preprocessor)
  :short "States of the preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are somewhat analogous to the "
    (xdoc::seetopic "parser-states" "parser states")
    ", but for the preprocessor.")
   (xdoc::p
    "We include the file that defines parser states
     because we reuse some of the definitions here."))
  :order-subtopics t
  :default-parent t)

; cert_param: (non-acl2r)

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
                  :reqfix (if (dec-digit-char-p digit)
                              digit
                            #\0)))
   :require (dec-digit-char-p digit))
  (:dot-digit ((digit character
                      :reqfix (if (dec-digit-char-p digit)
                                  digit
                                #\0)))
   :require (dec-digit-char-p digit))
  (:number-digit ((number pnumber)
                  (digit character
                         :reqfix (if (dec-digit-char-p digit)
                                     digit
                                   #\0)))
   :require (dec-digit-char-p digit))
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

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-pnumber
  :short "An irrelevant preprocessing number."
  :type pnumberp
  :body (pnumber-digit #\0))

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

(fty::defoption plexeme-option
  plexeme
  :short "Fixtype of optional preprocessing lexemes."
  :pred plexeme-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist plexeme-list
  :short "Fixtype of lists of preprocessing lexemes."
  :elt-type plexeme
  :true-listp t
  :elementp-of-nil nil
  :pred plexeme-listp)

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

(define plexeme-tokenp ((lexeme plexemep))
  :returns (yes/no booleanp)
  :short "Check if a preprocessing lexeme is a token."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the grammar rule for <i>preprocessing-token</i>
     [C17:6.4] [C17:A.1.1]."))
  (and (member-eq (plexeme-kind lexeme)
                  '(:header
                    :ident
                    :number
                    :char
                    :string
                    :punctuator
                    :other))
       t)

  ///

  (defruled plexeme-tokenp-alt-def
    (equal (plexeme-tokenp lexeme)
           (not (member-eq (plexeme-kind lexeme)
                           '(:block-comment
                             :line-comment
                             :newline
                             :spaces
                             :horizontal-tab
                             :vertical-tab
                             :form-feed))))))

;;;;;;;;;;;;;;;;;;;;

(std::deflist plexeme-list-tokenp (x)
  :guard (plexeme-listp x)
  :short "Check if every preprocessing lexeme in a list is a token."
  (plexeme-tokenp x)
  :elementp-of-nil t
  ///
  (fty::deffixequiv plexeme-list-tokenp))

;;;;;;;;;;;;;;;;;;;;

(std::deflist plexeme-list-not-tokenp (x)
  :guard (plexeme-listp x)
  :short "Check if no preprocessing lexeme in a list is a token."
  (plexeme-tokenp x)
  :negatedp t
  :elementp-of-nil t
  ///
  (fty::deffixequiv plexeme-list-not-tokenp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plexeme-token/newline-p ((lexeme plexemep))
  :returns (yes/no booleanp)
  :short "Check if a preprocessing lexeme is a token or a newline."
  :long
  (xdoc::topstring
   (xdoc::p
    "During preprocessing, newline characters are significant:
     see grammar rules in [C17:6.10/1].
     Preprocessing is largely line-oriented.
     In our preprocessor, newline characters are captured as newline lexemes
     (see @(tsee plexeme)).")
   (xdoc::p
    "[C17:5.1.1.2/3] requires that comments, including line comments,
     are turned into single space characters;
     we do not actually do that, to preserve the comment information,
     but conceptually we need our preprocessor to behave as if we did.
     This means that, if we are looking for tokens or newline characters,
     we must also consider line comments,
     because they are always followed by a newline character."))
  (or (plexeme-tokenp lexeme)
      (plexeme-case lexeme :newline)
      (plexeme-case lexeme :line-comment)))

;;;;;;;;;;;;;;;;;;;;

(std::deflist plexeme-list-token/newline-p (x)
  :guard (plexeme-listp x)
  :short "Check if every preprocessing lexeme in a list is a token or newline."
  (plexeme-token/newline-p x)
  :elementp-of-nil t
  ///
  (fty::deffixequiv plexeme-list-token/newline-p))

;;;;;;;;;;;;;;;;;;;;

(std::deflist plexeme-list-not-token/newline-p (x)
  :guard (plexeme-listp x)
  :short "Check if no preprocessing lexeme in a list is a token or newline."
  (plexeme-token/newline-p x)
  :negatedp t
  :elementp-of-nil t
  ///
  (fty::deffixequiv plexeme-list-not-token/newline-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
                  (non-exec (create-ppstate)))
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
    ///
    (more-returns
     (bytes true-listp :rule-classes :type-prescription)))

  (define ppstate->position (ppstate)
    :returns (position positionp)
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->position ppstate)
                  (irr-position))
         :exec (raw-ppstate->position ppstate))
    :hooks nil)

  (define ppstate->chars-length (ppstate)
    :returns (length natp)
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->chars-length ppstate)
                  1)
         :exec (raw-ppstate->chars-length ppstate)))

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
    :guard-hints (("Goal" :in-theory (enable nfix ppstate->chars-length)))
    :hooks nil)

  (define ppstate->chars-read (ppstate)
    :returns (chars-read natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->chars-read ppstate)
                  0)
         :exec (raw-ppstate->chars-read ppstate)))

  (define ppstate->chars-unread (ppstate)
    :returns (chars-unread natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->chars-unread ppstate)
                  0)
         :exec (raw-ppstate->chars-unread ppstate)))

  (define ppstate->lexemes-length (ppstate)
    :returns (length natp)
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->lexemes-length ppstate)
                  1)
         :exec (raw-ppstate->lexemes-length ppstate)))

  (define ppstate->lexeme ((i natp) ppstate)
    :guard (< i (ppstate->lexemes-length ppstate))
    :returns (lexeme+span plexeme+span-p
                          :hints
                          (("Goal"
                            :in-theory (enable ppstate->lexemes-length))))
    (mbe :logic (if (and (ppstatep ppstate)
                         (< (nfix i) (ppstate->lexemes-length ppstate)))
                    (raw-ppstate->lexeme (nfix i) ppstate)
                  (make-plexeme+span :lexeme (irr-plexeme)
                                     :span (irr-position)))
         :exec (raw-ppstate->lexeme i ppstate))
    :guard-hints (("Goal" :in-theory (enable nfix ppstate->lexemes-length)))
    :hooks nil)

  (define ppstate->lexemes-read (ppstate)
    :returns (lexemes-read natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->lexemes-read ppstate)
                  0)
         :exec (raw-ppstate->lexemes-read ppstate)))

  (define ppstate->lexemes-unread (ppstate)
    :returns (lexemes-unread natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->lexemes-unread ppstate)
                  0)
         :exec (raw-ppstate->lexemes-unread ppstate)))

  (define ppstate->version (ppstate)
    :returns (version c::versionp)
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->version ppstate)
                  (c::version-c23))
         :exec (raw-ppstate->version ppstate)))

  (define ppstate->size (ppstate)
    :returns (size natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (ppstatep ppstate)
                    (raw-ppstate->size ppstate)
                  0)
         :exec (raw-ppstate->size ppstate)))

  ;; writers:

  (define update-ppstate->bytes ((bytes byte-listp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->bytes (byte-list-fix bytes) ppstate)))

  (define update-ppstate->position ((position positionp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->position (position-fix position) ppstate)))

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
      (raw-update-ppstate->chars-length (nfix length) ppstate)))

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
    :guard-hints (("Goal" :in-theory (enable ppstate->chars-length nfix)))
    :hooks nil)

  (define update-ppstate->chars-read ((chars-read natp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->chars-read (nfix chars-read) ppstate)))

  (define update-ppstate->chars-unread ((chars-unread natp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->chars-unread (nfix chars-unread) ppstate)))

  (define update-ppstate->lexemes-length ((length natp) ppstate)
    :returns (ppstate ppstatep
                      :hints
                      (("Goal"
                        :in-theory (enable nfix
                                           ppstate-fix
                                           length
                                           plexeme+span-listp-of-resize-list))))
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->lexemes-length (nfix length) ppstate)))

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
    :guard-hints (("Goal" :in-theory (enable ppstate->lexemes-length nfix)))
    :hooks nil)

  (define update-ppstate->lexemes-read ((lexemes-read natp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->lexemes-read (nfix lexemes-read) ppstate)))

  (define update-ppstate->lexemes-unread ((lexemes-unread natp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->lexemes-unread (nfix lexemes-unread) ppstate)))

  (define update-ppstate->version ((version c::versionp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->version (c::version-fix version) ppstate)))

  (define update-ppstate->size ((size natp) ppstate)
    :returns (ppstate ppstatep)
    (b* ((ppstate (ppstate-fix ppstate)))
      (raw-update-ppstate->size (lnfix size) ppstate)))

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

(define ppstate->gcc ((ppstate ppstatep))
  :returns (gcc booleanp)
  :short "Flag saying whether GCC extensions are supported or not."
  (c::version-gccp (ppstate->version ppstate)))

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
    ppstate))
