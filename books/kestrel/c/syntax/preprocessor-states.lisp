; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "unicode-characters")
(include-book "preprocessor-options")
(include-book "preprocessor-lexemes")
(include-book "macro-tables")
(include-book "parser-states")
(include-book "implementation-environments")

(include-book "kestrel/fty/byte-list-list" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/no-duplicatesp" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "std/typed-lists/nat-listp" :dir :system))

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

(defsection ppstate
  :short "Fixtype of preprocessor states."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee parstate), but for the preprocessor.")
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
    "The preprocessor state consists of the following components:")
   (xdoc::ul
    (xdoc::li
     "An array of Unicode characters.
      The array is initialized from the Unicode characters obtained
      by UTF-8-decoding the bytes of the file to be preprocessed.
      Once initialized, this array never changes. ")
    (xdoc::li
     "An array of the positions of the characters in the array above,
      in the same order, i.e. the position at index @('i') is
      the one of the character at index @('i').
      This array is exactly one element longer than the array of characters:
      the last position is the one just past the end of file,
      which does not correspond to any character.
      Once initialized, this array never changes.")
    (xdoc::li
     "The index of the current character.
      This is initially 0, and is incremented as we read the characters.
      This is always an index into the character array,
      or equal to the length of that array when we reach the end of the file.
      This is always an index into the position array,
      which is one element longer than the character array as noted above.")
    (xdoc::li
     "A list of lexemes to be read next,
      before lexing lexemes from the character array.
      Conceptually, this list is in front of the remaining characters,
      i.e. the ones starting at the current character index.
      The list of lexemes is initially empty,
      and gets extended when unreading lexemes,
      but also when expanding macros.
      When a macro is expanded, the expansion is added to this list,
      so that preprocessing continues with the expansion,
      thus realizing rescanning and further replacement [C17:6.10.3.4].")
    (xdoc::li
     "A list of spans of the lexemes in the previous component,
      in the same number and in the same order.")
    (xdoc::li
     "The current size of the input,
      defined as the sum of the remaining characters to be read
      and the lexemes in the pending list.
      This is derivable from other components,
      but it is cached for efficiency.")
    (xdoc::li
     "The macro table that consists of all the macros in scope.")
    (xdoc::li
     "The options supplied to the preprocessor.
      This is set when the stobj is initialized, and never changes.")
    (xdoc::li
     "The implementation environment,
      which affects certain aspects of preprocessing.")))

  ;; needed for DEFSTOBJ and reader/writer proofs:

  (local (in-theory (enable length)))

  ;; stobj definition:

  (make-event
   `(defstobj ppstate
      (chars :type (array (satisfies unicharp) (0))
             :initially 0
             :resizable t)
      (positions :type (array (satisfies positionp) (1))
                 :initially ,(irr-position)
                 :resizable t)
      (char-index :type (integer 0 *)
                  :initially 0)
      (lexemes :type (satisfies plexeme-listp)
               :initially nil)
      (spans :type (satisfies span-listp)
             :initially nil)
      (size :type (integer 0 *)
            :initially 0)
      (macros :type (satisfies macro-tablep)
              :initially ,(macro-table nil nil))
      (options :type (satisfies ppoptionsp)
               :initially ,(irr-ppoptions))
      (ienv :type (satisfies ienvp)
            :initially ,(irr-ienv))
      :renaming (;; field recognizers:
                 (charsp raw-ppstate->chars-p)
                 (positionsp raw-ppstate->positions-p)
                 (char-indexp raw-ppstate->char-index-p)
                 (lexemesp raw-ppstate->lexemes-p)
                 (spansp raw-ppstate->spans-p)
                 (sizep raw-ppstate->size-p)
                 (macrosp raw-ppstate->macros-p)
                 (optionsp raw-ppstate->options-p)
                 (ienvp raw-ppstate->ienvp)
                 ;; field readers:
                 (chars-length raw-ppstate->chars-length)
                 (charsi raw-ppstate->char)
                 (positions-length raw-ppstate->positions-length)
                 (positionsi raw-ppstate->position)
                 (char-index raw-ppstate->char-index)
                 (lexemes raw-ppstate->lexemes)
                 (spans raw-ppstate->spans)
                 (size raw-ppstate->size)
                 (macros raw-ppstate->macros)
                 (options raw-ppstate->options)
                 (ienv raw-ppstate->ienv)
                 ;; field writers:
                 (resize-chars raw-update-ppstate->chars-length)
                 (update-charsi raw-update-ppstate->char)
                 (resize-positions raw-update-ppstate->positions-length)
                 (update-positionsi raw-update-ppstate->position)
                 (update-char-index raw-update-ppstate->char-index)
                 (update-lexemes raw-update-ppstate->lexemes)
                 (update-spans raw-update-ppstate->spans)
                 (update-size raw-update-ppstate->size)
                 (update-macros raw-update-ppstate->macros)
                 (update-options raw-update-ppstate->options)
                 (update-ienv raw-update-ppstate->ienv))
      :non-executable t))

  ;; fixer:

  (define ppstate-fix ((ppstate ppstatep))
    :returns (new-ppstate ppstatep)
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

  (defrule raw-ppstate->chars-p-to-unichar-listp
    (equal (raw-ppstate->chars-p x)
           (unichar-listp x))
    :induct t)

  (defrule raw-ppstate->positions-p-to-position-listp
    (equal (raw-ppstate->positions-p x)
           (position-listp x))
    :induct t)

  ;; needed for subsequent proofs:

  (local (in-theory (enable ppstate-fix nfix ifix)))

  ;; readers:

  (define ppstate->chars-length ((ppstate ppstatep))
    :returns (length natp)
    (mbe :logic (non-exec (raw-ppstate->chars-length (ppstate-fix ppstate)))
         :exec (raw-ppstate->chars-length ppstate))
    :inline t)

  (define ppstate->char ((i natp) (ppstate ppstatep))
    :guard (< i (ppstate->chars-length ppstate))
    :returns (char unicharp)
    (mbe :logic (non-exec
                 (unichar-fix
                  (raw-ppstate->char (nfix i) (ppstate-fix ppstate))))
         :exec (raw-ppstate->char i ppstate))
    :inline t
    :prepwork ((local (in-theory (enable ppstate->chars-length))))
    :guard-hints
    (("Goal" :in-theory (enable raw-ppstate->chars-p-to-unichar-listp)))

    ///

    (more-returns
     (char natp :rule-classes :type-prescription
           :hints (("Goal" :in-theory (enable natp-when-unicharp))))))

  (define ppstate->positions-length ((ppstate ppstatep))
    :returns (length natp)
    (mbe :logic (non-exec (raw-ppstate->positions-length (ppstate-fix ppstate)))
         :exec (raw-ppstate->positions-length ppstate))
    :inline t)

  (define ppstate->position ((i natp) (ppstate ppstatep))
    :guard (< i (ppstate->positions-length ppstate))
    :returns (pos positionp)
    (mbe :logic (non-exec
                 (position-fix
                  (raw-ppstate->position (nfix i) (ppstate-fix ppstate))))
         :exec (raw-ppstate->position i ppstate))
    :inline t
    :prepwork ((local (in-theory (enable ppstate->positions-length))))
    :guard-hints
    (("Goal" :in-theory (enable raw-ppstate->positions-p-to-position-listp))))

  (define ppstate->char-index ((ppstate ppstatep))
    :returns (char-index natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (non-exec (raw-ppstate->char-index (ppstate-fix ppstate)))
         :exec (raw-ppstate->char-index ppstate))
    :inline t)

  (define ppstate->lexemes ((ppstate ppstatep))
    :returns (lexemes plexeme-listp)
    (mbe :logic (non-exec (raw-ppstate->lexemes (ppstate-fix ppstate)))
         :exec (raw-ppstate->lexemes ppstate))
    :inline t)

  (define ppstate->spans ((ppstate ppstatep))
    :returns (spans span-listp)
    (mbe :logic (non-exec (raw-ppstate->spans (ppstate-fix ppstate)))
         :exec (raw-ppstate->spans ppstate))
    :inline t)

  (define ppstate->size ((ppstate ppstatep))
    :returns (size natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (non-exec (raw-ppstate->size (ppstate-fix ppstate)))
         :exec (raw-ppstate->size ppstate))
    :inline t)

  (define ppstate->macros ((ppstate ppstatep))
    :returns (macros macro-tablep)
    (mbe :logic (non-exec (raw-ppstate->macros (ppstate-fix ppstate)))
         :exec (raw-ppstate->macros ppstate))
    :inline t)

  (define ppstate->options ((ppstate ppstatep))
    :returns (options ppoptionsp)
    (mbe :logic (non-exec (raw-ppstate->options (ppstate-fix ppstate)))
         :exec (raw-ppstate->options ppstate))
    :inline t)

  (define ppstate->ienv ((ppstate ppstatep))
    :returns (ienv ienvp)
    (mbe :logic (non-exec (raw-ppstate->ienv (ppstate-fix ppstate)))
         :exec (raw-ppstate->ienv ppstate))
    :inline t)

  ;; needed for subsequent proofs:

  (local (in-theory (enable update-nth-array)))

  ;; writers:

  (define update-ppstate->chars-length ((length natp) (ppstate ppstatep))
    :returns (new-ppstate ppstatep
                          :hints
                          (("Goal"
                            :in-theory (enable unichar-listp-of-resize-list))))
    (mbe :logic (non-exec
                 (raw-update-ppstate->chars-length (nfix length)
                                                   (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->chars-length length ppstate))
    :inline t)

  (define update-ppstate->char ((i natp) (char unicharp) (ppstate ppstatep))
    :guard (< i (ppstate->chars-length ppstate))
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec
                 (if (< (nfix i) (ppstate->chars-length ppstate))
                     (raw-update-ppstate->char
                      (nfix i) (unichar-fix char) (ppstate-fix ppstate))
                   (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->char i char ppstate))
    :inline t
    :prepwork ((local (in-theory (enable ppstate->chars-length)))))

  (define update-ppstate->positions-length ((length natp) (ppstate ppstatep))
    :returns (new-ppstate ppstatep
                          :hints
                          (("Goal"
                            :in-theory (enable position-listp-of-resize-list))))
    (mbe :logic (non-exec
                 (raw-update-ppstate->positions-length (nfix length)
                                                       (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->positions-length length ppstate))
    :inline t)

  (define update-ppstate->position ((i natp) (pos positionp) (ppstate ppstatep))
    :guard (< i (ppstate->positions-length ppstate))
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec
                 (if (< (nfix i) (ppstate->positions-length ppstate))
                     (raw-update-ppstate->position
                      (nfix i) (position-fix pos) (ppstate-fix ppstate))
                   (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->position i pos ppstate))
    :inline t
    :prepwork ((local (in-theory (enable ppstate->positions-length)))))

  (define update-ppstate->char-index ((char-index natp) (ppstate ppstatep))
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec (raw-update-ppstate->char-index
                           (nfix char-index) (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->char-index char-index ppstate))
    :inline t)

  (define update-ppstate->lexemes ((lexemes plexeme-listp) (ppstate ppstatep))
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->lexemes (plexeme-list-fix lexemes)
                                              (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->lexemes lexemes ppstate))
    :inline t)

  (define update-ppstate->spans ((spans span-listp) (ppstate ppstatep))
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->spans (span-list-fix spans)
                                            (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->spans spans ppstate))
    :inline t)

  (define update-ppstate->size ((size natp) (ppstate ppstatep))
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->size (nfix size) (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->size size ppstate))
    :inline t)

  (define update-ppstate->macros ((macros macro-tablep) (ppstate ppstatep))
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec (raw-update-ppstate->macros (macro-table-fix macros)
                                                      (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->macros macros ppstate))
    :inline t)

  (define update-ppstate->options ((options ppoptionsp) (ppstate ppstatep))
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->options (ppoptions-fix options)
                                              (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->options options ppstate))
    :inline t)

  (define update-ppstate->ienv ((ienv ienvp) (ppstate ppstatep))
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->ienv (ienv-fix ienv)
                                           (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->ienv ienv ppstate))
    :inline t)

  ;; readers over writers:

  (defrule ppstate->chars-length-of-update-ppstate->chars-length
    (equal (ppstate->chars-length (update-ppstate->chars-length length ppstate))
           (nfix length))
    :enable (ppstate->chars-length
             update-ppstate->chars-length
             unichar-listp-of-resize-list))

  (defrule ppstate->chars-length-of-update-ppstate->char
    (equal (ppstate->chars-length (update-ppstate->char i char ppstate))
           (ppstate->chars-length ppstate))
    :enable (ppstate->chars-length
             update-ppstate->char
             max
             len))

  (defrule ppstate->chars-length-of-update-ppstate->size
    (equal (ppstate->chars-length (update-ppstate->size size ppstate))
           (ppstate->chars-length ppstate))
    :enable (ppstate->chars-length
             update-ppstate->size))

  (defrule ppstate->positions-length-of-update-ppstate->positions-length
    (equal (ppstate->positions-length
            (update-ppstate->positions-length length ppstate))
           (nfix length))
    :enable (ppstate->positions-length
             update-ppstate->positions-length
             position-listp-of-resize-list))

  (defrule ppstate->positions-length-of-update-ppstate->position
    (equal (ppstate->positions-length (update-ppstate->position i pos ppstate))
           (ppstate->positions-length ppstate))
    :enable (ppstate->positions-length
             update-ppstate->position
             max
             len))

  (defrule ppstate->positions-length-of-update-ppstate->char-index
    (equal (ppstate->positions-length
            (update-ppstate->char-index char-index ppstate))
           (ppstate->positions-length ppstate))
    :enable (ppstate->positions-length
             update-ppstate->char-index))

  (defrule ppstate->positions-length-of-update-ppstate->size
    (equal (ppstate->positions-length (update-ppstate->size size ppstate))
           (ppstate->positions-length ppstate))
    :enable (ppstate->positions-length
             update-ppstate->size))

  (defrule ppstate->char-index-of-update-ppstate->char-index
    (equal (ppstate->char-index (update-ppstate->char-index char-index ppstate))
           (nfix char-index))
    :enable (ppstate->char-index
             update-ppstate->char-index))

  (defrule ppstate->char-index-of-update-ppstate->size
    (equal (ppstate->char-index (update-ppstate->size size ppstate))
           (ppstate->char-index ppstate))
    :enable (ppstate->char-index
             update-ppstate->size))

  (defrule ppstate->lexemes-of-update-ppstate->char-index
    (equal (ppstate->lexemes (update-ppstate->char-index char-index ppstate))
           (ppstate->lexemes ppstate))
    :enable (ppstate->lexemes
             update-ppstate->char-index))

  (defrule ppstate->lexemes-of-update-ppstate->size
    (equal (ppstate->lexemes (update-ppstate->size size ppstate))
           (ppstate->lexemes ppstate))
    :enable (ppstate->lexemes
             update-ppstate->size))

  (defrule ppstate->size-of-update-ppstate->char-index
    (equal (ppstate->size (update-ppstate->char-index char-index ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->char-index))

  (defrule ppstate->size-of-update-ppstate->lexemes
    (equal (ppstate->size (update-ppstate->lexemes lexemes ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->lexemes))

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

  (defrule update-ppstate->chars-index-of-ppstate->chars-index
    (equal (update-ppstate->char-index (ppstate->char-index ppstate)
                                       ppstate)
           (ppstate-fix ppstate))
    :enable (update-ppstate->char-index
             ppstate->char-index
             nfix))

  (defrule update-ppstate->size-of-ppstate->size
    (equal (update-ppstate->size (ppstate->size ppstate) ppstate)
           (ppstate-fix ppstate))
    :enable (update-ppstate->size
             ppstate->size
             nfix))

  ;; writers over writers:

  (defrule update-ppstate->char-index-of-update-ppstate->char-index
    (equal (update-ppstate->char-index char-index
                                       (update-ppstate->char-index char-index2
                                                                   ppstate))
           (update-ppstate->char-index char-index ppstate))
    :enable update-ppstate->char-index)

  (defrule update-ppstate->size-of-update-ppstate->size
    (equal (update-ppstate->size size (update-ppstate->size size2 ppstate))
           (update-ppstate->size size ppstate))
    :enable update-ppstate->size)

  (defruled update-ppstate->size-of-update-ppstate->char-index
    (equal (update-ppstate->size size
                                 (update-ppstate->char-index char-index
                                                             ppstate))
           (update-ppstate->char-index char-index
                                       (update-ppstate->size size
                                                             ppstate)))
    :enable (update-ppstate->char-index
             update-ppstate->size))

  ;; keep recognizer disabled:

  (in-theory (disable ppstatep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ppstate->gcc/clang ((ppstate ppstatep))
  :returns (gcc booleanp)
  :short "Flag saying whether GCC/Clang extensions are supported or not."
  (c::dialect-gcc/clangp (ienv->dialect (ppstate->ienv ppstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ppstate->current-position ((ppstate ppstatep))
  :returns (pos positionp)
  :short "Current position in the preprocessor state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the position of the current character,
     or one past the end of the file."))
  (b* ((index (ppstate->char-index ppstate))
       ((unless (< index (ppstate->positions-length ppstate)))
        (raise "Internal error: ~
                the index ~x0 is not below ~
                the length ~x1 of the positions array."
               index
               (ppstate->positions-length ppstate))
        (irr-position)))
    (ppstate->position index ppstate))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-ppstate ((chars unichar-listp)
                      (poss position-listp)
                      (macros macro-tablep)
                      (options ppoptionsp)
                      (ienv ienvp)
                      (ppstate ppstatep))
  :guard (equal (len poss) (1+ (len chars)))
  :returns (new-ppstate ppstatep)
  :short "Initialize the preprocessor state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the state when we start preprocessing a file.
     It is built from
     the characters read from the file,
     their positions,
     the current table of macros in scope,
     the preprocessor options,
     and the implementation environment.")
   (xdoc::p
    "We resize the character and position arrays
     to the lengths of the lists,
     which are related as expressed in the guard,
     and as explained in @(tsee ppstate).
     The character index is set to 0, i.e. the beginning.
     There are no pending lexemes and spans."))
  (b* ((ppstate (update-ppstate->chars-length (len chars) ppstate))
       (ppstate (init-ppstate-chars-loop chars 0 ppstate))
       (ppstate (update-ppstate->positions-length (len poss) ppstate))
       (ppstate (init-ppstate-positions-loop poss 0 ppstate))
       (ppstate (update-ppstate->char-index 0 ppstate))
       (ppstate (update-ppstate->lexemes nil ppstate))
       (ppstate (update-ppstate->spans nil ppstate))
       (ppstate (update-ppstate->size (len chars) ppstate))
       (ppstate (update-ppstate->macros macros ppstate))
       (ppstate (update-ppstate->options options ppstate))
       (ppstate (update-ppstate->ienv ienv ppstate)))
    ppstate)

  :prepwork

  ((define init-ppstate-chars-loop ((chars unichar-listp)
                                    (i natp)
                                    (ppstate ppstatep))
     :guard (<= (+ i (len chars))
                (ppstate->chars-length ppstate))
     :returns (new-ppstate ppstatep)
     :parents nil
     (b* ((ppstate (ppstate-fix ppstate))
          ((when (endp chars)) ppstate)
          (ppstate (update-ppstate->char i (car chars) ppstate)))
       (init-ppstate-chars-loop (cdr chars) (1+ (lnfix i)) ppstate)))

   (define init-ppstate-positions-loop ((poss position-listp)
                                        (i natp)
                                        (ppstate ppstatep))
     :guard (<= (+ i (len poss))
                (ppstate->positions-length ppstate))
     :returns (new-ppstate ppstatep)
     :parents nil
     (b* ((ppstate (ppstate-fix ppstate))
          ((when (endp poss)) ppstate)
          (ppstate (update-ppstate->position i (car poss) ppstate)))
       (init-ppstate-positions-loop (cdr poss) (1+ (lnfix i)) ppstate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define push-lexeme ((lexeme plexemep) (span spanp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Push a lexeme, with a span, onto the pending lists."
  (b* ((lexemes (ppstate->lexemes ppstate))
       (spans (ppstate->spans ppstate))
       (new-lexemes (cons (plexeme-fix lexeme) lexemes))
       (new-spans (cons (span-fix span) spans))
       (new-size (1+ (ppstate->size ppstate)))
       (ppstate (update-ppstate->lexemes new-lexemes ppstate))
       (ppstate (update-ppstate->spans new-spans ppstate))
       (ppstate (update-ppstate->size new-size ppstate)))
    ppstate)

  ///

  (defret ppstate->size-of-push-lexeme
    (equal (ppstate->size new-ppstate)
           (1+ (ppstate->size ppstate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define push-lexemes ((lexemes plexeme-listp) (span spanp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Push a list of lexemes, all with the same span,
          onto the pending lists."
  (b* ((old-lexemes (ppstate->lexemes ppstate))
       (old-spans (ppstate->spans ppstate))
       (new-lexemes (append (plexeme-list-fix lexemes) old-lexemes))
       (new-spans (append (repeat (len lexemes) (span-fix span)) old-spans))
       (new-size (+ (len lexemes) (ppstate->size ppstate)))
       (ppstate (update-ppstate->lexemes new-lexemes ppstate))
       (ppstate (update-ppstate->spans new-spans ppstate))
       (ppstate (update-ppstate->size new-size ppstate)))
    ppstate)

  ///

  (defret ppstate->size-of-push-lexemes
    (equal (ppstate->size new-ppstate)
           (+ (len lexemes) (ppstate->size ppstate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pop-lexeme ((ppstate ppstatep))
  :returns (mv (lexeme? plexeme-optionp) (span spanp) (new-ppstate ppstatep))
  :short "Pop a lexemes, with a span, from the pending lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the lists are empty,
     we retun @('nil') as first result,
     and an irrelevant span as second result.
     It is an invariant that the two lists always have the same length,
     but currently we do not have that invariant statically available,
     so we make a check that is never expected to fail."))
  (b* ((ppstate (ppstate-fix ppstate))
       (lexemes (ppstate->lexemes ppstate))
       (size (ppstate->size ppstate))
       (spans (ppstate->spans ppstate))
       ((unless (consp lexemes)) (mv nil (irr-span) ppstate))
       ((unless (consp spans))
        (raise "Internal error: non-empty lexemes but empty spans.")
        (mv nil (irr-span) ppstate))
       ((cons lexeme new-lexemes) lexemes)
       ((cons span new-spans) spans)
       ((unless (> size 0))
        (raise "Internal error: non-empty lexemes but zero size.")
        (mv nil (irr-span) ppstate))
       (new-size (1- (ppstate->size ppstate)))
       (ppstate (update-ppstate->lexemes new-lexemes ppstate))
       (ppstate (update-ppstate->spans new-spans ppstate))
       (ppstate (update-ppstate->size new-size ppstate)))
    (mv lexeme span ppstate))
  :no-function nil
  :prepwork
  ((defrulel lemma
     (implies (and (plexeme-listp x)
                   (consp x))
              (car x))))

  ///

  (defret ppstate->size-of-pop-lexemes
    (equal (ppstate->size new-ppstate)
           (if lexeme?
               (1- (ppstate->size ppstate))
             (ppstate->size ppstate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define change-presumed-line ((line posp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Change the presumed line at the current position."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is always called after preprocessing a @('#line') directive.
     So the current position is normally
     the start of the line just after the directive,
     except when the directive ends with the file (without a new line);
     the latter is possible only if GCC or Clang extensions are enabled.
     If we are indeed at the end of the file,
     there is no need to change anything
     in the positions in the preprocessor state,
     because the change must apply to subsequent lines [C17:6.10.4/3],
     but there are no subsequent lines.
     If we are not at the end of the file,
     we double-check that we are at column 0,
     throwing a hard error if not
     (this should be a static invariant eventually).")
   (xdoc::p
    "This is used just after preprocessing a @('#line') directive,
     so that the current position is the start of the line just after that
     (which could be past the end of the file
     if the @('#line') directive ends with the file without a new line).
     The @('#line') directive [C17:6.10.4] changes the `presumed' line number,
     starting at the line just after the directive.
     We implement this by adjusting all the lines in the positions array,
     by the offset between the presumed line (passed as input to this function)
     and the line number in the current position:
     this is because changing the line just after the directive
     must affect all the subsequent lines as well.")
   (xdoc::p
    "Note that this operation could be performed multiple times,
     for different @('#line') directives in a file,
     each time adjusting all the line numbers
     from the position just after the directive to the end of the file.")
   (xdoc::p
    "Since the line number passed as input is a positive integer,
     and since line number do not decrease in the positions array,
     adding the offset (which may be positive or negative or zero)
     to all the subsequent positions in the array
     always results in a positive integer.
     But we do not the non-decreasing line numbers invariant available,
     so we coerce each result with @(tsee pos-fix) for now."))
  (b* ((ppstate (ppstate-fix ppstate))
       (index (ppstate->char-index ppstate))
       (positions-length (ppstate->positions-length ppstate))
       ((unless (< index positions-length))
        (raise "Internal error: ~
                the index ~x0 is not below ~
                the length ~x1 of the positions array."
               index
               positions-length)
        ppstate)
       ((when (= index (1- positions-length))) ppstate) ; no change
       (pos (ppstate->position index ppstate))
       ((unless (= (position->column pos) 0))
        (raise "Internal error: current column is ~x0."
               (position->column pos))
        ppstate)
       (offset (- (pos-fix line) (position->line pos))))
    (change-presumed-line-loop index offset ppstate))
  :no-function nil

  :prepwork
  ((define change-presumed-line-loop ((index natp)
                                      (offset integerp)
                                      (ppstate ppstatep))
     :guard (<= (nfix index) (ppstate->positions-length ppstate))
     :returns (new-ppstate ppstatep)
     :parents nil
     (b* ((ppstate (ppstate-fix ppstate))
          ((when (>= (lnfix index) (ppstate->positions-length ppstate)))
           ppstate)
          (pos (ppstate->position index ppstate))
          (pos-line (position->line pos))
          (new-pos-line (pos-fix (+ pos-line (lifix offset))))
          (new-pos (change-position pos :line new-pos-line))
          (ppstate (update-ppstate->position index new-pos ppstate)))
       (change-presumed-line-loop (1+ (lnfix index)) offset ppstate))
     :measure (nfix (- (ppstate->positions-length ppstate) (nfix index)))
     :hints (("Goal" :in-theory (enable nfix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define change-presumed-line+file ((line posp)
                                   (file stringp)
                                   (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Change the presumed line and file at the current position."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee change-presumed-line),
     but it also affects the presumed file,
     which the @('#line') directive can do, in addition to the line
     [C17:6.10.4]."))
  (b* ((ppstate (ppstate-fix ppstate))
       (index (ppstate->char-index ppstate))
       (positions-length (ppstate->positions-length ppstate))
       ((unless (< index positions-length))
        (raise "Internal error: ~
                the index ~x0 is not below ~
                the length ~x1 of the positions array."
               index
               positions-length)
        ppstate)
       ((when (= index (1- positions-length))) ppstate) ; no change
       (pos (ppstate->position index ppstate))
       ((unless (= (position->column pos) 0))
        (raise "Internal error: current column is ~x0."
               (position->column pos))
        ppstate)
       (offset (- (pos-fix line) (position->line pos))))
    (change-presumed-line+file-loop index offset file ppstate))
  :no-function nil

  :prepwork
  ((define change-presumed-line+file-loop ((index natp)
                                           (offset integerp)
                                           (file stringp)
                                           (ppstate ppstatep))
     :guard (<= (nfix index) (ppstate->positions-length ppstate))
     :returns (new-ppstate ppstatep)
     :parents nil
     (b* ((ppstate (ppstate-fix ppstate))
          ((when (>= (lnfix index) (ppstate->positions-length ppstate)))
           ppstate)
          (pos (ppstate->position index ppstate))
          (pos-line (position->line pos))
          (new-pos-line (pos-fix (+ pos-line (lifix offset))))
          (new-pos (change-position pos
                                    :file (str-fix file)
                                    :line new-pos-line))
          (ppstate (update-ppstate->position index new-pos ppstate)))
       (change-presumed-line+file-loop (1+ (lnfix index)) offset file ppstate))
     :measure (nfix (- (ppstate->positions-length ppstate) (nfix index)))
     :hints (("Goal" :in-theory (enable nfix))))))
