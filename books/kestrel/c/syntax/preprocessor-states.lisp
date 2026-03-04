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
     "An integer offset for the line number.
      This is the difference between
      the presumed line number and the actual line number.
      The actual line number is the one in the current position,
      i.e. the element of the positions arrays
      at the index of the current character.
      A @('#line') directive [C17:6.10.4] may set the presumed line number,
      i.e. ``pretend'' that the number of the line following the directive
      is the one specified by the directive.
      When this happens, we set the integer offset for line number
      to the difference between the number specified by the directive
      and the actual line number recorded in the positions array.
      The offset can be positive or negative
      (or null, in which case the directive has no effect).
      This way, as we proceed through the file,
      and as the current position according to the positions array changes,
      we always have an offset with which we can compute
      the presumed line number.")
    (xdoc::li
     "A list of lexmarks to be read next,
      before lexing lexemes from the character array.
      Conceptually, this list is in front of the remaining characters,
      i.e. the ones starting at the current character index.
      The list of lexmarks is initially empty,
      and gets extended when unreading lexemes,
      but also when expanding macros.
      When a macro is expanded, the expansion is added to this list,
      so that preprocessing continues with the expansion,
      thus realizing rescanning and further replacement [C17:6.10.3.4].
      The @(':start') and @(':end') markers are added around that expansion,
      to delimit that the expansion comes from a certain macro,
      so that we can prevent recursive expansion,
      as explained in more detail elsewhere.")
    (xdoc::li
     "The current size of the input,
      defined as the sum of the remaining characters to be read
      and the lexmarks in the pending list.
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
      (chars :type (array (satisfies ucharp) (0))
             :initially 0
             :resizable t)
      (positions :type (array (satisfies positionp) (1))
                 :initially ,(irr-position)
                 :resizable t)
      (char-index :type (integer 0 *)
                  :initially 0)
      (line-offset :type integer
                   :initially 0)
      (lexmarks :type (satisfies lexmark-listp)
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
                 (line-offsetp raw-ppstate->line-offset-p)
                 (lexmarksp raw-ppstate->lexmarks-p)
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
                 (line-offset raw-ppstate->line-offset)
                 (lexmarks raw-ppstate->lexmarks)
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
                 (update-line-offset raw-update-ppstate->line-offset)
                 (update-lexmarks raw-update-ppstate->lexmarks)
                 (update-size raw-update-ppstate->size)
                 (update-macros raw-update-ppstate->macros)
                 (update-options raw-update-ppstate->options)
                 (update-ienv raw-update-ppstate->ienv))))

  ;; fixer:

  (define ppstate-fix (ppstate)
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

  (defrule raw-ppstate->chars-p-to-uchar-listp
    (equal (raw-ppstate->chars-p x)
           (uchar-listp x))
    :induct t)

  (defrule raw-ppstate->positions-p-to-position-listp
    (equal (raw-ppstate->positions-p x)
           (position-listp x))
    :induct t)

  ;; needed for subsequent proofs:

  (local (in-theory (enable ppstate-fix nfix ifix)))

  ;; readers:

  (define ppstate->chars-length (ppstate)
    :returns (length natp)
    (mbe :logic (non-exec (raw-ppstate->chars-length (ppstate-fix ppstate)))
         :exec (raw-ppstate->chars-length ppstate))
    :inline t)

  (define ppstate->char ((i natp) ppstate)
    :guard (< i (ppstate->chars-length ppstate))
    :returns (char ucharp)
    (mbe :logic (non-exec
                 (uchar-fix
                  (raw-ppstate->char (nfix i) (ppstate-fix ppstate))))
         :exec (raw-ppstate->char i ppstate))
    :inline t
    :prepwork ((local (in-theory (enable ppstate->chars-length))))
    :guard-hints
    (("Goal" :in-theory (enable raw-ppstate->chars-p-to-uchar-listp)))

    ///

    (more-returns
     (char natp :rule-classes :type-prescription
           :hints (("Goal" :in-theory (enable natp-when-ucharp))))))

  (define ppstate->positions-length (ppstate)
    :returns (length natp)
    (mbe :logic (non-exec (raw-ppstate->positions-length (ppstate-fix ppstate)))
         :exec (raw-ppstate->positions-length ppstate))
    :inline t)

  (define ppstate->position ((i natp) ppstate)
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

  (define ppstate->char-index (ppstate)
    :returns (char-index natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (non-exec (raw-ppstate->char-index (ppstate-fix ppstate)))
         :exec (raw-ppstate->char-index ppstate))
    :inline t)

  (define ppstate->line-offset (ppstate)
    :returns (line-offset integerp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (non-exec (raw-ppstate->line-offset (ppstate-fix ppstate)))
         :exec (raw-ppstate->line-offset ppstate))
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

  ;; needed for subsequent proofs:

  (local (in-theory (enable update-nth-array)))

  ;; writers:

  (define update-ppstate->chars-length ((length natp) ppstate)
    :returns (new-ppstate ppstatep
                          :hints
                          (("Goal"
                            :in-theory (enable uchar-listp-of-resize-list))))
    (mbe :logic (non-exec
                 (raw-update-ppstate->chars-length (nfix length)
                                                   (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->chars-length length ppstate))
    :inline t)

  (define update-ppstate->char ((i natp) (char ucharp) ppstate)
    :guard (< i (ppstate->chars-length ppstate))
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec
                 (if (< (nfix i) (ppstate->chars-length ppstate))
                     (raw-update-ppstate->char
                      (nfix i) (uchar-fix char) (ppstate-fix ppstate))
                   (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->char i char ppstate))
    :inline t
    :prepwork ((local (in-theory (enable ppstate->chars-length)))))

  (define update-ppstate->positions-length ((length natp) ppstate)
    :returns (new-ppstate ppstatep
                          :hints
                          (("Goal"
                            :in-theory (enable position-listp-of-resize-list))))
    (mbe :logic (non-exec
                 (raw-update-ppstate->positions-length (nfix length)
                                                       (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->positions-length length ppstate))
    :inline t)

  (define update-ppstate->position ((i natp) (pos positionp) ppstate)
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

  (define update-ppstate->char-index ((char-index natp) ppstate)
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec (raw-update-ppstate->char-index
                           (nfix char-index) (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->char-index char-index ppstate))
    :inline t)

  (define update-ppstate->line-offset ((line-offset integerp) ppstate)
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec (raw-update-ppstate->line-offset
                           (ifix line-offset) (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->line-offset line-offset ppstate))
    :inline t)

  (define update-ppstate->lexmarks ((lexmarks lexmark-listp) ppstate)
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->lexmarks (lexmark-list-fix lexmarks)
                                               (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->lexmarks lexmarks ppstate))
    :inline t)

  (define update-ppstate->size ((size natp) ppstate)
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->size (nfix size) (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->size size ppstate))
    :inline t)

  (define update-ppstate->macros ((macros macro-tablep) ppstate)
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec (raw-update-ppstate->macros (macro-table-fix macros)
                                                      (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->macros macros ppstate))
    :inline t)

  (define update-ppstate->options ((options ppoptionsp) ppstate)
    :returns (new-ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->options (ppoptions-fix options)
                                              (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->options options ppstate))
    :inline t)

  (define update-ppstate->ienv ((ienv ienvp) ppstate)
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
             uchar-listp-of-resize-list))

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

  (defrule ppstate->lexmarks-of-update-ppstate->char-index
    (equal (ppstate->lexmarks (update-ppstate->char-index char-index ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->char-index))

  (defrule ppstate->lexmarks-of-update-ppstate->size
    (equal (ppstate->lexmarks (update-ppstate->size size ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->size))

  (defrule ppstate->size-of-update-ppstate->char-index
    (equal (ppstate->size (update-ppstate->char-index char-index ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->char-index))

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
  (c::version-gcc/clangp (ienv->version (ppstate->ienv ppstate))))

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

;;;;;;;;;;;;;;;;;;;;

(define ppstate->presumed-position ((ppstate ppstatep))
  :returns (pos positionp)
  :short "Presumed position in the preprocesor state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is explained in @(tsee ppstate).
     We add the offset to the line of the current position.
     We throw a hard error if the result is not a positive integer;
     this should never happen,
     because the @('#line') directive must always specify a positive integer
     [C17:6.10.4],
     and thus adding the offset would never result in
     a non-positive integer."))
  (b* ((pos (ppstate->current-position ppstate))
       (line (position->line pos))
       (offset (ppstate->line-offset ppstate))
       (presumed-line (+ line offset))
       ((unless (posp presumed-line))
        (raise "Internal error: presumed line is ~x0." presumed-line)
        (irr-position)))
    (change-position pos :line (+ line offset)))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-ppstate ((chars uchar-listp)
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
     The line offset is 0.
     The size is set to the number of unread characters (all)."))
  (b* ((ppstate (update-ppstate->chars-length (len chars) ppstate))
       (ppstate (init-ppstate-chars-loop chars 0 ppstate))
       (ppstate (update-ppstate->positions-length (len poss) ppstate))
       (ppstate (init-ppstate-positions-loop poss 0 ppstate))
       (ppstate (update-ppstate->char-index 0 ppstate))
       (ppstate (update-ppstate->line-offset 0 ppstate))
       (ppstate (update-ppstate->size (len chars) ppstate))
       (ppstate (update-ppstate->macros macros ppstate))
       (ppstate (update-ppstate->options options ppstate))
       (ppstate (update-ppstate->ienv ienv ppstate)))
    ppstate)

  :prepwork

  ((define init-ppstate-chars-loop ((chars uchar-listp)
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
