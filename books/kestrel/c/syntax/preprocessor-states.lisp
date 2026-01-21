; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

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

(defruledl assoc-equal-iff-member-equal-of-strip-cars
  (implies (alistp alist)
           (iff (assoc-equal key alist)
                (member-equal key (strip-cars alist))))
  :induct t
  :enable (assoc-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(fty::deflist lexmark-list
  :short "Fixtype of lists of lexmarks."
  :elt-type lexmark
  :true-listp t
  :elementp-of-nil nil
  :pred lexmark-listp)

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
     "The bytes being read are organized as an array of lists
      (the @('ss') in @('bytess') conveys the ``double plural'').
      Conceptually, it is equivalent to concatenating the lists in order,
      but the nested structure derives from file inclusion via @('#include'),
      and plays a role in the termination argument of the preprocessor.
      When starting to read a top-level file,
      there is just one list with the bytes of the file.
      When a @('#include') directive is encountered,
      unless certain conditions (specific to our preprocessor) are satisfied,
      the contents of the included file must be expanded in place,
      i.e. the @('#include') directive must be replaced
      with the content of the file [C17:6.10.2],
      and preprocessing continues on that content,
      and then eventually with the content of the including file
      after the @('#include') directive;
      this is the normal behavior of C preprocessors, in fact.
      When that happens,
      instead of @(tsee append)ing the bytes of the included file
      in front of the remaining bytes in the stobj,
      we store the bytes of the included file
      into the next element of the array,
      i.e. one more than the current index @('bytess-current'),
      which is also part of the stobj,
      and keeps track of the current byte list being read.
      If the included file's bytes, when parsed/preprocessed,
      contain more @('#include') directives,
      more lists of bytes are added to the array,
      and @('bytess-current') advanced accordingly.
      This is more efficient than @(tsee append)ing to one list of bytes.
      We use an array instead of a list of lists so that
      we can efficiently read and remove bytes:
      @(tsee cdr) on a list is efficient (no memory allocation),
      but if we had a list of lists instead of an array of lists,
      we would have to create a new list of lists
      with the first list resulting from the @(tsee cdr),
      i.e. we would have to execute a @(tsee cons);
      this is avoided with an array, since the lists in it are independent.
      As bytes are read from the current list of the array,
      when that list becomes empty, the @('bytess-current') is decremented:
      that happens when the bytes of the latest included file
      have been completely preprocessed;
      the reduced @('bytess-current') reflects
      the reduced depth of the file inclusion.")
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
      a macro table that consists of all the macros in scope.")))

  ;; needed for DEFSTOBJ and reader/writer proofs:

  (local (in-theory (enable length)))

  ;; stobj definition:

  (make-event
   `(defstobj ppstate
      (bytess :type (array (satisfies byte-listp) (1))
              :initially nil
              :resizable t)
      (bytess-current :type (integer 0 *)
                      :initially 0)
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
              :initially ,(macro-table-init))
      (ienv :type (satisfies ienvp)
            :initially ,(irr-ienv))
      :renaming (;; field recognizers:
                 (bytessp raw-ppstate->bytess-p)
                 (bytess-currentp raw-ppstate->bytess-current-p)
                 (positionp raw-ppstate->position-p)
                 (charsp raw-ppstate->chars-p)
                 (chars-readp raw-ppstate->chars-read-p)
                 (chars-unreadp raw-ppstate->chars-unread-p)
                 (lexmarksp raw-ppstate->lexmarks-p)
                 (sizep raw-ppstate->size-p)
                 (macrosp raw-ppstate->macros-p)
                 (ienvp raw-ppstate->ienvp)
                 ;; field readers:
                 (bytess-length raw-ppstate->bytess-length)
                 (bytessi raw-ppstate->bytes)
                 (bytess-current raw-ppstate->bytess-current)
                 (position raw-ppstate->position)
                 (chars-length raw-ppstate->chars-length)
                 (charsi raw-ppstate->char)
                 (chars-read raw-ppstate->chars-read)
                 (chars-unread raw-ppstate->chars-unread)
                 (lexmarks raw-ppstate->lexmarks)
                 (size raw-ppstate->size)
                 (macros raw-ppstate->macros)
                 (ienv raw-ppstate->ienv)
                 ;; field writers:
                 (resize-bytess raw-update-ppstate->bytess-length)
                 (update-bytessi raw-update-ppstate->bytes)
                 (update-bytess-current raw-update-ppstate->bytess-current)
                 (update-position raw-update-ppstate->position)
                 (resize-chars raw-update-ppstate->chars-length)
                 (update-charsi raw-update-ppstate->char)
                 (update-chars-read raw-update-ppstate->chars-read)
                 (update-chars-unread raw-update-ppstate->chars-unread)
                 (update-lexmarks raw-update-ppstate->lexmarks)
                 (update-size raw-update-ppstate->size)
                 (update-macros raw-update-ppstate->macros)
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

  (defrule raw-ppstate->bytess-p-becomes-byte-list-listp
    (equal (raw-ppstate->bytess-p x)
           (byte-list-listp x))
    :induct t
    :enable (raw-ppstate->bytess-p
             byte-list-listp))

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

  (define ppstate->bytess-length (ppstate)
    :returns (length natp)
    (mbe :logic (non-exec (raw-ppstate->bytess-length (ppstate-fix ppstate)))
         :exec (raw-ppstate->bytess-length ppstate))
    :inline t)

  (define ppstate->bytes ((i natp) ppstate)
    :guard (< i (ppstate->bytess-length ppstate))
    :returns (bytes byte-listp)
    (mbe :logic (non-exec (raw-ppstate->bytes (nfix i) (ppstate-fix ppstate)))
         :exec (raw-ppstate->bytes i ppstate))
    :inline t
    :prepwork ((local (in-theory (enable ppstate->bytess-length)))))

  (define ppstate->bytess-current (ppstate)
    :returns (bytess-current natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (non-exec (raw-ppstate->bytess-current (ppstate-fix ppstate)))
         :exec (raw-ppstate->bytess-current ppstate))
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

  (define ppstate->ienv (ppstate)
    :returns (ienv ienvp)
    (mbe :logic (non-exec (raw-ppstate->ienv (ppstate-fix ppstate)))
         :exec (raw-ppstate->ienv ppstate))
    :inline t)

  ;; writers:

  (define update-ppstate->bytess-length ((length natp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->bytess-length (nfix length)
                                                    (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->bytess-length length ppstate))
    :inline t)

  (define update-ppstate->bytes ((i natp) (bytes byte-listp) ppstate)
    :guard (< i (ppstate->bytess-length ppstate))
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec (raw-update-ppstate->bytes (nfix i)
                                                     (byte-list-fix bytes)
                                                     (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->bytes i bytes ppstate))
    :inline t
    :guard-hints (("Goal" :in-theory (enable ppstate->bytess-length))))

  (define update-ppstate->bytess-current ((bytess-current natp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->bytess-current (nfix bytess-current)
                                                     (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->bytess-current bytess-current ppstate))
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
    (mbe :logic (non-exec
                 (raw-update-ppstate->macros (macro-table-fix macros)
                                             (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->macros macros ppstate))
    :inline t)

  (define update-ppstate->ienv ((ienv ienvp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->ienv (ienv-fix ienv)
                                           (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->ienv ienv ppstate))
    :inline t)

  ;; readers over writers:

  (defrule ppstate->bytess-length-of-update-ppstate->bytess-length
    (equal (ppstate->bytess-length
            (update-ppstate->bytess-length length ppstate))
           (lnfix length))
    :enable (ppstate->bytess-length
             update-ppstate->bytess-length))

  (defrule ppstate->bytess-current-of-update-ppstate->bytess-current
    (equal (ppstate->bytess-current
            (update-ppstate->bytess-current bytess-current ppstate))
           (nfix bytess-current))
    :enable (ppstate->bytess-current
             update-ppstate->bytess-current))

  (defrule ppstate->chars-length-of-update-ppstate->bytes
    (equal (ppstate->chars-length (update-ppstate->bytes i bytes ppstate))
           (ppstate->chars-length ppstate))
    :enable (ppstate->chars-length
             update-ppstate->bytes
             ppstate->bytess-length))

  (defrule ppstate->chars-length-of-update-ppstate->bytess-current
    (equal (ppstate->chars-length
            (update-ppstate->bytess-current bytess-current ppstate))
           (ppstate->chars-length ppstate))
    :enable (ppstate->chars-length
             update-ppstate->bytess-current))

  (defrule ppstate->chars-length-of-update-ppstate->size
    (equal (ppstate->chars-length (update-ppstate->size size ppstate))
           (ppstate->chars-length ppstate))
    :enable (ppstate->chars-length
             update-ppstate->size))

  (defrule ppstate->chars-read-of-update-ppstate->bytes
    (equal (ppstate->chars-read (update-ppstate->bytes i bytes ppstate))
           (ppstate->chars-read ppstate))
    :enable (ppstate->chars-read
             update-ppstate->bytes
             ppstate->bytess-length))

  (defrule ppstate->chars-read-of-update-ppstate->bytess-current
    (equal (ppstate->chars-read
            (update-ppstate->bytess-current bytess-current ppstate))
           (ppstate->chars-read ppstate))
    :enable (ppstate->chars-read
             update-ppstate->bytess-current))

  (defrule ppstate->chars-read-of-update-ppstate->size
    (equal (ppstate->chars-read (update-ppstate->size size ppstate))
           (ppstate->chars-read ppstate))
    :enable (ppstate->chars-read
             update-ppstate->size))

  (defrule ppstate->lexmarks-of-update-ppstate->bytes
    (equal (ppstate->lexmarks (update-ppstate->bytes i bytes ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->bytes
             ppstate->bytess-length))

  (defrule ppstate->lexmarks-of-update-ppstate->bytess-current
    (equal (ppstate->lexmarks
            (update-ppstate->bytess-current bytess-current ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->bytess-current))

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
    (equal (ppstate->size (update-ppstate->bytes i bytes ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->bytes
             ppstate->bytess-length))

  (defrule ppstate->size-of-update-ppstate->bytess-current
    (equal (ppstate->size
            (update-ppstate->bytess-current bytess-current ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->bytess-current))

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

(define ppstate->gcc ((ppstate ppstatep))
  :returns (gcc booleanp)
  :short "Flag saying whether GCC extensions are supported or not."
  (c::version-gccp (ienv->version (ppstate->ienv ppstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-ppstate ((data byte-listp)
                      (file-recursion-limit posp)
                      (macros macro-tablep)
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
     a limit on the number of files recursively preprocessed/included,
     the current table of macros in scope,
     and an implementation environment.")
   (xdoc::p
    "The array of byte lists is resized to the file recursion limit,
     which is set by the caller of this function.
     The bytes of the file are stored into the first element of the array,
     to which the current byte list index is set to point.
     The position is the initial one.
     There are no read or unread characters,
     and no lexmarks pending.
     The macro table is obtained by pushing a new scope for the file.
     We also resize the arrays of characters to the number of data bytes,
     which is sufficient because each character takes at least one byte."))
  (b* ((ppstate (update-ppstate->bytess-length (pos-fix file-recursion-limit)
                                               ppstate))
       (ppstate (update-ppstate->bytes 0 (byte-list-fix data) ppstate))
       (ppstate (update-ppstate->bytess-current 0 ppstate))
       (ppstate (update-ppstate->position (position-init) ppstate))
       (ppstate (update-ppstate->chars-length (len data) ppstate))
       (ppstate (update-ppstate->chars-read 0 ppstate))
       (ppstate (update-ppstate->chars-unread 0 ppstate))
       (ppstate (update-ppstate->lexmarks nil ppstate))
       (ppstate (update-ppstate->ienv ienv ppstate))
       (ppstate (update-ppstate->size (len data) ppstate))
       (ppstate (update-ppstate->macros (macro-table-push macros) ppstate)))
    ppstate)
  :guard-hints
  (("Goal"
    :in-theory
    (enable ppstate->bytess-length-of-update-ppstate->bytess-length))))

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

(define ppstate-add-bytes ((bytes byte-listp) (ppstate ppstatep))
  :returns (mv erp (new-ppstate ppstatep))
  :short "Add some input bytes to a preprocessing state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when a file included via a @('#include') directive
     is expanded in place:
     as explained in @(tsee ppstate),
     we put its bytes into the next element of the array of byte lists.
     It is an internal error if there is no next element in the array:
     the file recursion limit has been exceeded."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) ppstate)
       (bytess-length (ppstate->bytess-length ppstate))
       (bytess-current (ppstate->bytess-current ppstate))
       (size (ppstate->size ppstate))
       (bytess-current (1+ bytess-current))
       ((unless (< bytess-current bytess-length))
        (reterr (msg "Exceeded file recursion limit of ~x0." bytess-length)))
       (ppstate (update-ppstate->bytes bytess-current bytes ppstate))
       (ppstate (update-ppstate->bytess-current bytess-current ppstate))
       (ppstate (update-ppstate->size (+ size (len bytes)) ppstate)))
    (retok ppstate)))
