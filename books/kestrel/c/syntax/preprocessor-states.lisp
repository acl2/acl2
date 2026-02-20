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
(include-book "macro-tables")
(include-book "parser-states")
(include-book "implementation-environments")

(include-book "kestrel/fty/byte-list-list" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/no-duplicatesp" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))

(acl2::controlled-configuration)

; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl byte-list-listp-of-resize-list
  (implies (and (byte-list-listp bytess)
                (byte-listp default))
           (byte-list-listp (resize-list bytess length default)))
  :induct t
  :enable (byte-list-listp resize-list))

(defruledl byte-list-listp-of-update-nth-strong
  (implies (byte-list-listp bytess)
           (equal (byte-list-listp (update-nth i bytes bytess))
                  (byte-listp bytes)))
  :induct t
  :enable (byte-listp update-nth nfix zp len))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum lexmark
  :short "Fixtype of preprocessing lexemes and markers (`lexmarks')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Along with lexemes,
     it is convenient to handle certain markers.
     We use the term `lexmark' to denote a preprocessing lexeme or marker.")
   (xdoc::p
    "The lexemes are accompanied by spans.")
   (xdoc::p
    "The @(':start') and @(':end') summands are used to mark
     the start and end of an expansion of the macro,
     whose name is the @('macro') field of these two summands,
     in order to inhibit its (direct or indirect) recursive expansion
     [C17:6.10.3.4/2].")
   (xdoc::p
    "Only lexemes have spans associated with them.
     The markers are artifacts, not an actual part of the input files."))
  (:lexeme ((lexeme plexeme)
            (span span)))
  (:start ((macro ident)))
  (:end ((macro ident)))
  :pred lexmarkp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-lexmark
  :short "An irrelevant lexmark."
  :type lexmarkp
  :body (lexmark-lexeme (irr-plexeme) (irr-span)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption lexmark-option
  lexmark
  :short "Fixtype of optional lexmarks."
  :pred lexmark-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist lexmark-list
  :short "Fixtype of lists of lexmarks."
  :elt-type lexmark
  :true-listp t
  :elementp-of-nil nil
  :pred lexmark-listp

  ///

  (defruled true-listp-when-lexmark-listp
    (implies (lexmark-listp x)
             (true-listp x))
    :induct t
    :enable lexmark-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist lexmark-option-list
  :short "Fixtype of lists of optional lexmarks."
  :elt-type lexmark-option
  :true-listp t
  :elementp-of-nil t
  :pred lexmark-option-listp

  ///

  (defrule lexmark-option-listp-when-lexmark-listp
    (implies (lexmark-listp x)
             (lexmark-option-listp x))
    :induct t
    :enable lexmark-option-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-list-to-lexmark-list ((lexemes plexeme-listp))
  :returns (lexmarks lexmark-listp)
  :short "Turn a list of lexemes into a list of lexmarks."
  :long
  (xdoc::topstring
   (xdoc::p
    "We keep the ordering.
     We put irrelevant spans, which suggest that
     we should probably make the span optional in @(tsee lexmark)."))
  (cond ((endp lexemes) nil)
        (t (cons (make-lexmark-lexeme :lexeme (car lexemes) :span (irr-span))
                 (lexeme-list-to-lexmark-list (cdr lexemes))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist lexmark-list-case-lexeme-p (x)
  :guard (lexmark-listp x)
  :short "Check if all the lexmarks in a list are lexemes."
  (lexmark-case x :lexeme))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexmark-list-to-lexeme-list ((lexmarks lexmark-listp))
  :guard (lexmark-list-case-lexeme-p lexmarks)
  :returns (lexemes plexeme-listp)
  :short "Turn a list of lexmarks that are all lexemes
          into the list of lexemes."
  (cond ((endp lexmarks) nil)
        (t (cons (lexmark-lexeme->lexeme (car lexmarks))
                 (lexmark-list-to-lexeme-list (cdr lexmarks))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum hg-state
  :short "Fixtype of header guard states."
  :long
  (xdoc::topstring
   (xdoc::p
    "Header guards are a common technique to avoid
     including the same header (or file, in general) multiple times.
     The file, call it @('FILE'), has a form like")
   (xdoc::codeblock
    "#ifndef FILE_H"
    "#define FILE_H"
    "..."
    "#endif")
   (xdoc::p
    "When we preprocess a file, we check whether it has that form.
     To recognize that form, we use a sort of finite state machine
     that we make part of @(tsee ppstate).
     Here we define the states of the state machine:")
   (xdoc::ul
    (xdoc::li
     "The @(':initial') state is the one as we start preprocessing a file.
      We stay in this state so long as we do not find any token
      (i.e. just comments and white space).
      In this state, we are waiting for a @('#ifndef').")
    (xdoc::li
     "If we encounter a @('#ifndef') in the @(':initial') state,
      we transition to the @(':ifndef') state,
      where we keep track of the identifier following the @('#ifndef').
      Is we encounter anything else,
      we transition to the @(':not') state,
      meaning that the file does not have the header guard form.")
    (xdoc::li
     "If we encounter a @('#define') in the @(':ifndef') state,
      with the same identifier (@('FILE_H') in the example above),
      we transition to the @(':define') state.
      If we encounter anything else, we transition to @(':not').")
    (xdoc::li
     "We stay in the @(':define') state
      until we find the @('#endif') that matches the initial @('#ifndef'),
      at which point we move to the @(':endif') state,
      where we still keep track of the name.")
    (xdoc::li
     "If we find no other tokens (only comments and white space),
      and we reach the end of the file,
      we transition to the @(':eof') state.
      This is a final state, in which we have established that
      the file has the header guard form,
      and we know the name of the header guard.
      If instead there are more tokens,
      we transition to the other final state,
      namely the @(':not') state."))
   (xdoc::p
    "Here is a depiction of the states (except @(':not'))
     with respect to the content of the file:")
   (xdoc::codeblock
    "... (no tokens)     :initial"
    "#ifndef FILE_H      :ifndef(FILE_H)"
    "#define FILE_H      :define(FILE_H)"
    "...                 :define(FILE_H)"
    "#endif              :endif(FILE_H)"
    "... (no tokens)     :endif(FILE_H)"
    "EOF                 :eof(FILE_H)")
   (xdoc::p
    "In the future, we may add support for equivalent forms like")
   (xdoc::codeblock
    "#if !defined(FILE_H)"
    "#define FILE_H"
    "..."
    "#endif"))
  (:initial ())
  (:ifndef ((name ident)))
  (:define ((name ident)))
  (:endif ((name ident)))
  (:eof ((name ident)))
  (:not ())
  :pred hg-statep)

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
    "Most of the components of the preprocessor state
     are analogous to the ones of the parser state
     (see the documentation of @(tsee parstate) first),
     but there are differences:")
   (xdoc::ul
    (xdoc::li
     "Instead of just a C version as in the parser state,
      the preprocessor state has a full implementation environment.
      Probably parser states should have that too.")
    (xdoc::li
     "Instead of an array and two indices that represent
      a sequence of read and unread tokens,
      we have a single list of pending lexmarks.
      This is used like the sequence of unread tokens in the parser state,
      in the sense that the next lexeme is read from the list if non-empty,
      and otherwise it is lexed from the input characters.
      However, lexmarks are added to the pending list
      not only when unreading lexemes,
      which actually happens rarely in our preprocessor,
      but also when expanding macros.
      When a macro is expanded, the expansion is added to the pending list,
      so that preprocessing continues with the expansion,
      thus realizing rescanning and further replacement [C17:6.10.3.4].
      The @(':start') and @(':end') markers are added around that expansion,
      to delimit that the expansion comes from a certain macro,
      so that we can prevent recursive expansion,
      as explained in more detail elsewhere.")
    (xdoc::li
     "The preprocessor state also contains
      a macro table that consists of all the macros in scope.")
    (xdoc::li
     "The preprocessor state also contains a header guard state:
      see @(tsee hg-state).")
    (xdoc::li
     "The preprocessor state also contains a flag saying whether
      @('#error') and @('#warning') directives should be ignored,
      i.e. treated as no-ops.
      This flag is set when files are re-preprocessed
      in a fresh context as explained in @(see preservable-inclusions).")
    (xdoc::li
     "The preprocessor state also contains the preprocessor options.")))

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
      (lexmarks :type (satisfies lexmark-listp)
                :initially nil)
      (size :type (integer 0 *)
            :initially 0)
      (macros :type (satisfies macro-tablep)
              :initially ,(macro-table nil nil))
      (hg :type (satisfies hg-statep)
          :initially ,(hg-state-initial))
      (options :type (satisfies ppoptionsp)
               :initially ,(irr-ppoptions))
      (ienv :type (satisfies ienvp)
            :initially ,(irr-ienv))
      :renaming (;; field recognizers:
                 (bytesp raw-ppstate->bytes-p)
                 (positionp raw-ppstate->position-p)
                 (charsp raw-ppstate->chars-p)
                 (chars-readp raw-ppstate->chars-read-p)
                 (chars-unreadp raw-ppstate->chars-unread-p)
                 (lexmarksp raw-ppstate->lexmarks-p)
                 (sizep raw-ppstate->size-p)
                 (macrosp raw-ppstate->macros-p)
                 (hgp raw-ppstate->hg-p)
                 (optionsp raw-ppstate->options-p)
                 (ienvp raw-ppstate->ienvp)
                 ;; field readers:
                 (bytes raw-ppstate->bytes)
                 (position raw-ppstate->position)
                 (chars-length raw-ppstate->chars-length)
                 (charsi raw-ppstate->char)
                 (chars-read raw-ppstate->chars-read)
                 (chars-unread raw-ppstate->chars-unread)
                 (lexmarks raw-ppstate->lexmarks)
                 (size raw-ppstate->size)
                 (macros raw-ppstate->macros)
                 (hg raw-ppstate->hg)
                 (options raw-ppstate->options)
                 (ienv raw-ppstate->ienv)
                 ;; field writers:
                 (update-bytes raw-update-ppstate->bytes)
                 (update-position raw-update-ppstate->position)
                 (resize-chars raw-update-ppstate->chars-length)
                 (update-charsi raw-update-ppstate->char)
                 (update-chars-read raw-update-ppstate->chars-read)
                 (update-chars-unread raw-update-ppstate->chars-unread)
                 (update-lexmarks raw-update-ppstate->lexmarks)
                 (update-size raw-update-ppstate->size)
                 (update-macros raw-update-ppstate->macros)
                 (update-hg raw-update-ppstate->hg)
                 (update-options raw-update-ppstate->options)
                 (update-ienv raw-update-ppstate->ienv))))

  ;; fixer:

  (define ppstate-fix (ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (if (ppstatep ppstate)
                    ppstate
                  (non-exec (create-ppstate)))
         :exec ppstate)
    :inline t
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

  (defrule raw-ppstate->lexmarks-p-becomes-lexmark-listp
    (equal (raw-ppstate->lexmarks-p x)
           (lexmark-listp x))
    :induct t
    :enable (raw-ppstate->lexmarks-p
             lexmark-listp))

  ;; needed for subsequent proofs:

  (local (in-theory (enable ppstate-fix
                            nfix
                            update-nth-array
                            byte-list-listp-of-resize-list
                            char+position-listp-of-resize-list
                            byte-list-listp-of-update-nth-strong
                            char+position-listp-of-update-nth-strong)))

  ;; readers:

  (define ppstate->bytes (ppstate)
    :returns (bytes byte-listp)
    (mbe :logic (non-exec (raw-ppstate->bytes (ppstate-fix ppstate)))
         :exec (raw-ppstate->bytes ppstate))
    :inline t)

  (define ppstate->position (ppstate)
    :returns (position positionp)
    (mbe :logic (non-exec (raw-ppstate->position (ppstate-fix ppstate)))
         :exec (raw-ppstate->position ppstate))
    :inline t)

  (define ppstate->chars-length (ppstate)
    :returns (length natp)
    (mbe :logic (non-exec (raw-ppstate->chars-length (ppstate-fix ppstate)))
         :exec (raw-ppstate->chars-length ppstate))
    :inline t)

  (define ppstate->char ((i natp) ppstate)
    :guard (< i (ppstate->chars-length ppstate))
    :returns (char+pos char+position-p)
    (char+position-fix
     (mbe :logic (non-exec (raw-ppstate->char (nfix i) (ppstate-fix ppstate)))
          :exec (raw-ppstate->char i ppstate)))
    :inline t
    :prepwork ((local (in-theory (enable ppstate->chars-length)))))

  (define ppstate->chars-read (ppstate)
    :returns (chars-read natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (non-exec (raw-ppstate->chars-read (ppstate-fix ppstate)))
         :exec (raw-ppstate->chars-read ppstate))
    :inline t)

  (define ppstate->chars-unread (ppstate)
    :returns (chars-unread natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (non-exec (raw-ppstate->chars-unread (ppstate-fix ppstate)))
         :exec (raw-ppstate->chars-unread ppstate))
    :inline t)

  (define ppstate->lexmarks (ppstate)
    :returns (lexmarks lexmark-listp)
    (mbe :logic (non-exec (raw-ppstate->lexmarks (ppstate-fix ppstate)))
         :exec (raw-ppstate->lexmarks ppstate))
    :inline t)

  (define ppstate->size (ppstate)
    :returns (size natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (non-exec (raw-ppstate->size (ppstate-fix ppstate)))
         :exec (raw-ppstate->size ppstate))
    :inline t)

  (define ppstate->macros (ppstate)
    :returns (macros macro-tablep)
    (mbe :logic (non-exec (raw-ppstate->macros (ppstate-fix ppstate)))
         :exec (raw-ppstate->macros ppstate))
    :inline t)

  (define ppstate->hg (ppstate)
    :returns (hg hg-statep)
    (mbe :logic (non-exec (raw-ppstate->hg (ppstate-fix ppstate)))
         :exec (raw-ppstate->hg ppstate))
    :inline t)

  (define ppstate->options (ppstate)
    :returns (options ppoptionsp)
    (mbe :logic (non-exec (raw-ppstate->options (ppstate-fix ppstate)))
         :exec (raw-ppstate->options ppstate))
    :inline t)

  (define ppstate->ienv (ppstate)
    :returns (ienv ienvp)
    (mbe :logic (non-exec (raw-ppstate->ienv (ppstate-fix ppstate)))
         :exec (raw-ppstate->ienv ppstate))
    :inline t)

  ;; writers:

  (define update-ppstate->bytes ((bytes byte-listp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec (raw-update-ppstate->bytes (byte-list-fix bytes)
                                                     (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->bytes bytes ppstate))
    :inline t)

  (define update-ppstate->position ((position positionp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->position (position-fix position)
                                               (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->position position ppstate))
    :inline t)

  (define update-ppstate->chars-length ((length natp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->chars-length (nfix length)
                                                   (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->chars-length length ppstate))
    :inline t)

  (define update-ppstate->char ((i natp) (char+pos char+position-p) ppstate)
    :guard (< i (ppstate->chars-length ppstate))
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (if (< (nfix i) (ppstate->chars-length ppstate))
                     (raw-update-ppstate->char (nfix i)
                                               (char+position-fix char+pos)
                                               (ppstate-fix ppstate))
                   (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->char i char+pos ppstate))
    :inline t
    :prepwork ((local (in-theory (enable ppstate->chars-length)))))

  (define update-ppstate->chars-read ((chars-read natp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->chars-read (nfix chars-read)
                                                 (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->chars-read chars-read ppstate))
    :inline t)

  (define update-ppstate->chars-unread ((chars-unread natp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->chars-unread (nfix chars-unread)
                                                   (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->chars-unread chars-unread ppstate))
    :inline t)

  (define update-ppstate->lexmarks ((lexmarks lexmark-listp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->lexmarks (lexmark-list-fix lexmarks)
                                               (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->lexmarks lexmarks ppstate))
    :inline t)

  (define update-ppstate->size ((size natp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->size (nfix size) (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->size size ppstate))
    :inline t)

  (define update-ppstate->macros ((macros macro-tablep) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec (raw-update-ppstate->macros (macro-table-fix macros)
                                                      (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->macros macros ppstate))
    :inline t)

  (define update-ppstate->hg ((hg hg-statep) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec (raw-update-ppstate->hg (hg-state-fix hg)
                                                  (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->hg hg ppstate))
    :inline t)

  (define update-ppstate->options ((options ppoptionsp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->options (ppoptions-fix options)
                                              (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->options options ppstate))
    :inline t)

  (define update-ppstate->ienv ((ienv ienvp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->ienv (ienv-fix ienv)
                                           (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->ienv ienv ppstate))
    :inline t)

  ;; readers over writers:

  (defrule ppstate->chars-length-of-update-ppstate->bytes
    (equal (ppstate->chars-length (update-ppstate->bytes bytes ppstate))
           (ppstate->chars-length ppstate))
    :enable (ppstate->chars-length
             update-ppstate->bytes))

  (defrule ppstate->chars-length-of-update-ppstate->size
    (equal (ppstate->chars-length (update-ppstate->size size ppstate))
           (ppstate->chars-length ppstate))
    :enable (ppstate->chars-length
             update-ppstate->size))

  (defrule ppstate->chars-read-of-update-ppstate->bytes
    (equal (ppstate->chars-read (update-ppstate->bytes bytes ppstate))
           (ppstate->chars-read ppstate))
    :enable (ppstate->chars-read
             update-ppstate->bytes))

  (defrule ppstate->chars-read-of-update-ppstate->size
    (equal (ppstate->chars-read (update-ppstate->size size ppstate))
           (ppstate->chars-read ppstate))
    :enable (ppstate->chars-read
             update-ppstate->size))

  (defrule ppstate->lexmarks-of-update-ppstate->bytes
    (equal (ppstate->lexmarks (update-ppstate->bytes bytes ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->bytes))

  (defrule ppstate->lexmarks-of-update-ppstate->position
    (equal (ppstate->lexmarks
            (update-ppstate->position position ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->position))

  (defrule ppstate->lexmarks-of-update-ppstate->char
    (equal (ppstate->lexmarks (update-ppstate->char i char ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->char
             ppstate->chars-length))

  (defrule ppstate->lexmarks-of-update-ppstate->chars-read
    (equal (ppstate->lexmarks
            (update-ppstate->chars-read chars-read ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->chars-read))

  (defrule ppstate->lexmarks-of-update-ppstate->chars-unread
    (equal (ppstate->lexmarks
            (update-ppstate->chars-unread chars-unread ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->chars-unread))

  (defrule ppstate->lexmarks-of-update-ppstate->size
    (equal (ppstate->lexmarks (update-ppstate->size size ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->size))

  (defrule ppstate->size-of-update-ppstate->bytes
    (equal (ppstate->size (update-ppstate->bytes bytes ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->bytes))

  (defrule ppstate->size-of-update-ppstate->position
    (equal (ppstate->size (update-ppstate->position position ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->position))

  (defrule ppstate->size-of-update-ppstate->char
    (equal (ppstate->size (update-ppstate->char i char+pos ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->char
             ppstate->chars-length))

  (defrule ppstate->size-of-update-ppstate->chars-read
    (equal (ppstate->size (update-ppstate->chars-read chars-read ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->chars-read))

  (defrule ppstate->size-of-update-ppstate->chars-unread
    (equal (ppstate->size (update-ppstate->chars-unread chars-unread ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->chars-unread))

  (defrule ppstate->size-of-update-ppstate->lexmarks
    (equal (ppstate->size (update-ppstate->lexmarks lexmarks ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->lexmarks))

  (defrule ppstate->size-of-update-ppstate->size
    (equal (ppstate->size (update-ppstate->size size ppstate))
           (lnfix size))
    :enable (ppstate->size
             update-ppstate->size))

  (defrule ppstate->size-of-update-ppstate->macros
    (equal (ppstate->size (update-ppstate->macros macros ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->macros))

  ;; writers over readers:

  (defrule update-ppstate->chars-read-of-ppstate->chars-read
    (equal (update-ppstate->chars-read
            (ppstate->chars-read ppstate) ppstate)
           (ppstate-fix ppstate))
    :enable (update-ppstate->chars-read
             ppstate->chars-read))

  (defrule update-ppstate->chars-read-of-ppstate->chars-unread
    (equal (update-ppstate->chars-unread
            (ppstate->chars-unread ppstate) ppstate)
           (ppstate-fix ppstate))
    :enable (update-ppstate->chars-unread
             ppstate->chars-unread))

  ;; keep recognizer disabled:

  (in-theory (disable ppstatep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ppstate->gcc/clang ((ppstate ppstatep))
  :returns (gcc booleanp)
  :short "Flag saying whether GCC/Clang extensions are supported or not."
  (c::version-gcc/clangp (ienv->version (ppstate->ienv ppstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-ppstate ((data byte-listp)
                      (macros macro-tablep)
                      (options ppoptionsp)
                      (ienv ienvp)
                      ppstate)
  :returns (ppstate ppstatep)
  :short "Initialize the preprocessor state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the state when we start preprocessing a file.
     It is built from
     (the data of) a file to preprocess,
     the current table of macros in scope,
     the preprocessor options,
     and an implementation environment.")
   (xdoc::p
    "The array of byte lists is resized to the file recursion limit,
     which is set by the caller of this function.
     The bytes of the file are stored into the first element of the array,
     to which the current byte list index is set to point.
     The position is the initial one.
     There are no read or unread characters,
     and no lexmarks pending.
     We resize the arrays of characters to the number of bytes,
     which suffices because there are never more characters than bytes.
     We set the header guard state to be the initial one."))
  (b* ((ppstate (update-ppstate->bytes data ppstate))
       (ppstate (update-ppstate->position (position-init) ppstate))
       (ppstate (update-ppstate->chars-length (len data) ppstate))
       (ppstate (update-ppstate->chars-read 0 ppstate))
       (ppstate (update-ppstate->chars-unread 0 ppstate))
       (ppstate (update-ppstate->lexmarks nil ppstate))
       (ppstate (update-ppstate->size (len data) ppstate))
       (ppstate (update-ppstate->macros macros ppstate))
       (ppstate (update-ppstate->hg (hg-state-initial) ppstate))
       (ppstate (update-ppstate->options options ppstate))
       (ppstate (update-ppstate->ienv ienv ppstate)))
    ppstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define push-lexmark ((lexmark lexmarkp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Push a lexmark onto the pending lexmark list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when unreading a lexeme,
     and also when expaning a macro."))
  (b* ((new-lexmarks (cons lexmark (ppstate->lexmarks ppstate)))
       (new-size (1+ (ppstate->size ppstate)))
       (ppstate (update-ppstate->lexmarks new-lexmarks ppstate))
       (ppstate (update-ppstate->size new-size ppstate)))
    ppstate)

  ///

  (defret ppstate->size-of-push-lexmark
    (equal (ppstate->size new-ppstate)
           (1+ (ppstate->size ppstate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define push-lexmarks ((lexmarks lexmark-listp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Push a list of lexmarks onto the pending lexmark list."
  (b* ((new-lexmarks (append lexmarks (ppstate->lexmarks ppstate)))
       (new-size (+ (len lexmarks) (ppstate->size ppstate)))
       (ppstate (update-ppstate->lexmarks new-lexmarks ppstate))
       (ppstate (update-ppstate->size new-size ppstate)))
    ppstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define push-lexemes ((lexemes plexeme-listp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Push a list of lexemes onto the pending lexmark list."
  (b* ((new-lexmarks (append (lexeme-list-to-lexmark-list lexemes)
                             (ppstate->lexmarks ppstate)))
       (new-size (+ (len lexemes) (ppstate->size ppstate)))
       (ppstate (update-ppstate->lexmarks new-lexmarks ppstate))
       (ppstate (update-ppstate->size new-size ppstate)))
    ppstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hg-trans-ifndef ((name identp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Perform a header guard transition when encountering
          a @('#ifndef') directive."
  :long
  (xdoc::topstring
   (xdoc::p
    "If we are in the initial state,
     we move to the @(':ifndef') state.
     If we are in the @(':define') state,
     i.e. in the main content of the file,
     we stay in that state.
     If we are in the @(':not') state,
     we stay in that state (it is a final state).
     In all other states, we transition to @(':not'):
     if we were in @(':ifndef'),
     it means that we are not encountering @('#define');
     if we were in @(':endif'),
     it means that there is extra stuff after the @('#endif')."))
  (b* ((ppstate (ppstate-fix ppstate))
       (hg (ppstate->hg ppstate)))
    (hg-state-case
     hg
     :initial (update-ppstate->hg (hg-state-ifndef name) ppstate)
     :ifndef (update-ppstate->hg (hg-state-not) ppstate)
     :define ppstate
     :endif (update-ppstate->hg (hg-state-not) ppstate)
     :eof (prog2$ (raise "Internal error: header guard state ~x0." hg)
                  ppstate)
     :not ppstate))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;

(define hg-trans-elif/else ((cond-level natp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Perform a heaader guard transition when encountering
          a @('#elif') or @('#else') directive."
  :long
  (xdoc::topstring
   (xdoc::p
    "This should not happen at conditional nesting level 0.
     If we are at the conditional nesting level 1,
     and the header guard state is @(':ifndef') or @(':define'),
     it means that we are inside the top-level @('#ifndef'),
     but it contains a @('#elif') or @('#else');
     thus, we move to the @(':not') state.
     If we are at the conditional nesting level 1,
     and the header guard state is not @(':ifndef') or @(':define'),
     we must be in the @(':not') state, and the state does not change.
     If we are at a conditional nesting level 2 or more,
     we must be in either the @(':define') or @(':not') state,
     and the state does not change."))
  (b* ((ppstate (ppstate-fix ppstate))
       (hg (ppstate->hg ppstate)))
    (cond ((zp cond-level)
           (prog2$ (raise "Internal error: conditional level 0.")
                   ppstate))
          ((= cond-level 1)
           (case (hg-state-kind hg)
             ((:ifndef :define) (update-ppstate->hg (hg-state-not) ppstate))
             (:not ppstate)
             (t (prog2$ (raise "Internal error: ~
                                header guard state ~x0 at conditional level 1."
                               hg)
                        ppstate))))
          (t ; cond-level >= 2
           (if (member-eq (hg-state-kind hg) '(:define :not))
               ppstate
             (prog2$ (raise "Internal error: ~
                             header guard state ~x0 at conditional level ~x1."
                            hg cond-level)
                     ppstate)))))
  :no-function nil
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;

(define hg-trans-endif ((cond-level natp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Perform a header guard transition when encountering a @('#endif')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This should not happen at conditional nesting level 0.
     If we are at the conditional nesting level 1,
     and the header guard state is @(':define'),
     it means that we are inside the top-level @('#ifndef'),
     and it does not contain a @('#elif') or @('#else')
     (otherwise we would be in the @(':not') state);
     thus, we move to the @(':endif') state.
     If we are at the conditional nesting level 1,
     and the header guard state is @(':ifndef'),
     it means that we are missing the @('#define'),
     so we move to the @(':not') state.
     If the conditional level is 1
     and the header guard state is not @(':define') or @(':ifndef'),
     we must be in the @(':not') state, and the state does not change.
     If we are at a conditional nesting level 2 or more,
     we must be in either the @(':define') or @(':not') state,
     and the state does not change."))
  (b* ((ppstate (ppstate-fix ppstate))
       (hg (ppstate->hg ppstate)))
    (cond ((zp cond-level)
           (prog2$ (raise "Internal error: conditional level 0.")
                   ppstate))
          ((= cond-level 1)
           (case (hg-state-kind hg)
             (:define (b* ((name (hg-state-define->name hg))
                           (new-hg (hg-state-endif name)))
                        (update-ppstate->hg new-hg ppstate)))
             (:ifndef (update-ppstate->hg (hg-state-not) ppstate))
             (:not ppstate)
             (t (prog2$ (raise "Internal error: ~
                                header guard state ~x0 at conditional level 1."
                               hg)
                        ppstate))))
          (t ; cond-level >= 2
           (if (member-eq (hg-state-kind hg) '(:define :not))
               ppstate
             (prog2$ (raise "Internal error: ~
                             header guard state ~x0 at conditional level ~x1."
                            hg cond-level)
                     ppstate)))))
  :no-function nil
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;

(define hg-trans-define ((name identp)
                         (obj-empty-p booleanp)
                         (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Perform a header guard transition when encountering
          a @('#define') directive."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('obj-empty-p') flag says whether the @('#define') is for
     an object-like macro with an empty replacement list.")
   (xdoc::p
    "If we are in the @(':ifndef') state,
     the @('obj-empty-p') flag is @('t'),
     and the names match,
     we move to the @(':define') state;
     if the names do not match, we move to @(':not'),
     because we have not encountered the right @('#define').
     If we are in the @(':define') state,
     i.e. in the main content of the file,
     we stay in that state.
     If we are in the @(':not') state,
     we stay in that state (it is a final state).
     In all other states, we transition to @(':not'):
     if we were in @(':initial'),
     it means that we are not encountering @('#ifndef');
     if we were in @(':endif'),
     it means that there is extra stuff after the @('#endif')."))
  (b* ((ppstate (ppstate-fix ppstate))
       (hg (ppstate->hg ppstate)))
    (hg-state-case
     hg
     :initial (update-ppstate->hg (hg-state-not) ppstate)
     :ifndef (if (and obj-empty-p
                      (equal (ident-fix name) hg.name))
                 (update-ppstate->hg (hg-state-define name) ppstate)
               (update-ppstate->hg (hg-state-not) ppstate))
     :define ppstate
     :endif (update-ppstate->hg (hg-state-not) ppstate)
     :eof (prog2$ (raise "Internal error: header guard state ~x0." hg)
                  ppstate)
     :not ppstate))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;

(define hg-trans-non-ifndef/elif/else/define ((ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Perform a header guard transition when encountering something
          other than a @('#ifndef'), @('#elif'), @('#else'), or @('#define')."
  :long
  (xdoc::topstring
   (xdoc::p
    "By `something other' we man another kind of directive,
     or a text line with at least one token
     (i.e. not just comments and white space).")
   (xdoc::p
    "If we are in the @(':define') state,
     i.e. in the main content of the file,
     we stay in that state.
     If we are in the @(':not') state,
     we stay in that state (it is a final state).
     In all other states, we transition to @(':not'):
     if we were in @(':initial'),
     it means that we are not encountering @('#ifndef');
     if we were in @(':ifndef'),
     it means that we are not encountering @('#define');
     if we were in @(':endif'),
     it means that there is extra stuff after the @('#endif')."))
  (b* ((ppstate (ppstate-fix ppstate))
       (hg (ppstate->hg ppstate)))
    (hg-state-case
     hg
     :initial (update-ppstate->hg (hg-state-not) ppstate)
     :ifndef (update-ppstate->hg (hg-state-not) ppstate)
     :define ppstate
     :endif (update-ppstate->hg (hg-state-not) ppstate)
     :eof (prog2$ (raise "Internal error: header guard state ~x0." hg)
                  ppstate)
     :not ppstate))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;

(define hg-trans-eof ((ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Perform a header guard transition when encountering end of file."
  :long
  (xdoc::topstring
   (xdoc::p
    "If we are in the @(':endif') state,
     we transition to the @(':eof') state:
     the file has the header guard form.
     If we are in the @(':initial') state,
     we transition to the @(':not') state;
     the file does not have the required @('#ifndef').
     Otherwise, we must be in the @(':not') state, where we stay.."))
  (b* ((ppstate (ppstate-fix ppstate))
       (hg (ppstate->hg ppstate)))
    (case (hg-state-kind hg)
      (:endif (b* ((name (hg-state-endif->name hg))
                   (new-hg (hg-state-eof name)))
                (update-ppstate->hg new-hg ppstate)))
      (:initial (update-ppstate->hg (hg-state-not) ppstate))
      (:not ppstate)
      (t (prog2$ (raise "Internal error: header guard state ~x0." hg)
                 ppstate))))
  :no-function nil)
