; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "formalized")

(include-book "../language/abstract-syntax")

(include-book "std/util/error-value-tuples" :dir :system)

(local (in-theory (enable* abstract-syntax-unambp-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ mapping-to-language-definition
  :parents (syntax-for-tools)
  :short "Mapping from the tool-oriented syntax to the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in @(see syntax-for-tools),
     we plan to provide formal connections between
     the tool-oriented abstract syntax
     and the formal language definition in @(see c::language).
     Towards that goal, we provide a partial mapping
     from the tool-oriented abstract syntax
     to the abstract syntax of the formal language definition.
     This mapping is partial because currently the latter
     only covers a subset of C.")
   (xdoc::p
    "The proper way to relate the two abstract syntaxes would be
     in terms of the file sets that they reduce to in concrete syntax.
     The current mapping between the abstract syntaxes
     is like a ``shortcut''.")
   (xdoc::p
    "The functions that map
     from the tool-oriented abstract syntax
     to the language definition abstract syntax
     all start with @('ldm'), for `language definition mapping'.")
   (xdoc::p
    "We use "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuples")
    " when we encounter constructs that do not map
     (due to the language definition abstract syntax being a subset).
     So the mapping functions can be used also to check whether
     the syntax is within the subset of the language definition.")
   (xdoc::p
    "We accompany these mapping functions with theorems showing that
     the functions always succeed (i.e. never return errors)
     on constructs in the subset of C with formal dynamic semantics,
     as characterized by the @(see formalized-subset).
     Recall that the subset of C with formal dynamic semantics
     is a strict subset of the subset of C
     over which the mapping functions succeed.
     Some mapping functions have no accompanying theorems,
     because the constructs they operate on are never
     in the subset of C with formal dynamic semantics."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-ident ((ident identp))
  :returns (mv erp (ident1 c::identp))
  :short "Map an identiifer to an identifier in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the language definition requires ACL2 strings,
     we throw an error if the identifier is not an ACL2 string."))
  (b* (((reterr) (c::ident "irrelevant"))
       (string (ident->unwrap ident))
       ((unless (stringp string))
        (reterr (msg "Unsupported identifier with non-string ~x0." string))))
    (retok (c::ident string)))
  :hooks (:fix)

  ///

  (defret ldm-ident-ok-when-ident-formalp
    (not erp)
    :hyp (ident-formalp ident)
    :hints (("Goal" :in-theory (enable ident-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-lsuffix ((lsuffix lsuffixp))
  :returns (ilen c::iconst-lengthp)
  :short "Map a length suffix to an integer constant length
          in the language definition."
  (lsuffix-case
   lsuffix
   :locase-l (c::iconst-length-long)
   :upcase-l (c::iconst-length-long)
   :locase-ll (c::iconst-length-llong)
   :upcase-ll (c::iconst-length-llong))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-isuffix ((isuffix isuffixp))
  :returns (mv (ilen c::iconst-lengthp)
               (unsignedp booleanp))
  :short "Map an integer suffix
          to an integer constant length in the language definition
          and to an unsigned flag."
  (isuffix-case
   isuffix
   :u (mv (c::iconst-length-none) t)
   :l (mv (ldm-lsuffix isuffix.length) nil)
   :ul (mv (ldm-lsuffix isuffix.length) t)
   :lu (mv (ldm-lsuffix isuffix.length) t))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-isuffix-option ((isuffix? isuffix-optionp))
  :returns (mv (ilen c::iconst-lengthp)
               (unsignedp booleanp))
  :short "Map an optional integer suffix
          to an integer constant length in the language definition
          and to an unsigned flag."
  (isuffix-option-case
   isuffix?
   :some (ldm-isuffix isuffix?.val)
   :none (mv (c::iconst-length-none) nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-dec/oct/hex-const ((const dec/oct/hex-constp))
  :returns (mv (value natp) (base c::iconst-basep))
  :short "Map a decimal, octal, or hexadecimal constant
          to a value
          and to an integer constant base in the language definition."
  (dec/oct/hex-const-case
   const
   :dec (mv const.value (c::iconst-base-dec))
   :oct (mv const.value (c::iconst-base-oct))
   :hex (mv (str::hex-digit-chars-value const.digits) (c::iconst-base-hex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-iconst ((iconst iconstp))
  :returns (iconst1 c::iconstp)
  :short "Map an integer constant to
          an integer constant in the language definition."
  (b* (((iconst iconst) iconst)
       ((mv value base) (ldm-dec/oct/hex-const iconst.core))
       ((mv length unsignedp) (ldm-isuffix-option iconst.suffix?)))
    (c::make-iconst :value value
                    :base base
                    :unsignedp unsignedp
                    :length length))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-const ((const constp))
  :returns (mv erp (const1 c::constp))
  :short "Map a constant to
          a constant in the language definition."
  (b* (((reterr) (c::const-enum (c::ident "irrelevant"))))
    (const-case
     const
     :int (retok (c::const-int (ldm-iconst const.unwrap)))
     :float (reterr (msg "Unsupported floating constant ~x0." const.unwrap))
     :enum (b* (((erp ident1) (ldm-ident const.unwrap)))
             (retok (c::const-enum ident1)))
     :char (reterr (msg "Unsupported character constant ~x0." const.unwrap))))
  :hooks (:fix)

  ///

  (defret ldm-const-ok-when-const-formalp
    (not erp)
    :hyp (const-formalp const)
    :hints (("Goal" :in-theory (enable const-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-type-spec-list ((tyspecs type-spec-listp))
  :guard (type-spec-list-unambp tyspecs)
  :returns (mv erp (tyspecseq c::tyspecseqp))
  :short "Map a list of type specifiers to
          a type specifier sequence in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The language definition only supports certain type specifier sequences.
     This mapping function recognizes the lists of type specifiers
     that correspond to the ones supported in the language definition."))
  (b* (((reterr) (c::tyspecseq-void))
       (tyspecs (type-spec-list-fix tyspecs)))
    (cond
     ((equal tyspecs (list (type-spec-void)))
      (retok (c::tyspecseq-void)))
     ((equal tyspecs (list (type-spec-char)))
      (retok (c::tyspecseq-char)))
     ((equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                           (type-spec-char)))
      (retok (c::tyspecseq-schar)))
     ((equal tyspecs (list (type-spec-unsigned)
                           (type-spec-char)))
      (retok (c::tyspecseq-uchar)))
     ((equal tyspecs (list (type-spec-short)))
      (retok (c::make-tyspecseq-sshort :signed nil :int nil)))
     ((equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                           (type-spec-short)))
      (retok (c::make-tyspecseq-sshort :signed t :int nil)))
     ((equal tyspecs (list (type-spec-short)
                           (type-spec-int)))
      (retok (c::make-tyspecseq-sshort :signed nil :int t)))
     ((equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                           (type-spec-short)
                           (type-spec-int)))
      (retok (c::make-tyspecseq-sshort :signed t :int t)))
     ((equal tyspecs (list (type-spec-unsigned)
                           (type-spec-short)))
      (retok (c::make-tyspecseq-ushort :int nil)))
     ((equal tyspecs (list (type-spec-unsigned)
                           (type-spec-short)
                           (type-spec-int)))
      (retok (c::make-tyspecseq-ushort :int t)))
     ((equal tyspecs (list (type-spec-int)))
      (retok (c::make-tyspecseq-sint :signed nil :int t)))
     ((equal tyspecs (list (type-spec-signed (keyword-uscores-none))))
      (retok (c::make-tyspecseq-sint :signed t :int nil)))
     ((equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                           (type-spec-int)))
      (retok (c::make-tyspecseq-sint :signed t :int t)))
     ((equal tyspecs (list (type-spec-unsigned)))
      (retok (c::make-tyspecseq-uint :int nil)))
     ((equal tyspecs (list (type-spec-unsigned)
                           (type-spec-int)))
      (retok (c::make-tyspecseq-uint :int t)))
     ((equal tyspecs (list (type-spec-long)))
      (retok (c::make-tyspecseq-slong :signed nil :int nil)))
     ((equal tyspecs (list (type-spec-long)
                           (type-spec-int)))
      (retok (c::make-tyspecseq-slong :signed nil :int t)))
     ((equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                           (type-spec-long)))
      (retok (c::make-tyspecseq-slong :signed t :int nil)))
     ((equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                           (type-spec-long)
                           (type-spec-int)))
      (retok (c::make-tyspecseq-slong :signed t :int t)))
     ((equal tyspecs (list (type-spec-unsigned)
                           (type-spec-long)))
      (retok (c::make-tyspecseq-ulong :int nil)))
     ((equal tyspecs (list (type-spec-unsigned)
                           (type-spec-long)
                           (type-spec-int)))
      (retok (c::make-tyspecseq-ulong :int t)))
     ((equal tyspecs (list (type-spec-long)
                           (type-spec-long)))
      (retok (c::make-tyspecseq-sllong :signed nil :int nil)))
     ((equal tyspecs (list (type-spec-long)
                           (type-spec-long)
                           (type-spec-int)))
      (retok (c::make-tyspecseq-sllong :signed nil :int t)))
     ((equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                           (type-spec-long)
                           (type-spec-long)))
      (retok (c::make-tyspecseq-sllong :signed t :int nil)))
     ((equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                           (type-spec-long)
                           (type-spec-long)
                           (type-spec-int)))
      (retok (c::make-tyspecseq-sllong :signed t :int t)))
     ((equal tyspecs (list (type-spec-unsigned)
                           (type-spec-long)
                           (type-spec-long)))
      (retok (c::make-tyspecseq-ullong :int nil)))
     ((equal tyspecs (list (type-spec-unsigned)
                           (type-spec-long)
                           (type-spec-long)
                           (type-spec-int)))
      (retok (c::make-tyspecseq-ullong :int t)))
     ((equal tyspecs (list (type-spec-bool)))
      (retok (c::tyspecseq-bool)))
     ((equal tyspecs (list (type-spec-float)))
      (retok (c::make-tyspecseq-float :complex nil)))
     ((equal tyspecs (list (type-spec-float)
                           (type-spec-complex)))
      (retok (c::make-tyspecseq-float :complex t)))
     ((equal tyspecs (list (type-spec-double)))
      (retok (c::make-tyspecseq-double :complex nil)))
     ((equal tyspecs (list (type-spec-double)
                           (type-spec-complex)))
      (retok (c::make-tyspecseq-double :complex t)))
     ((equal tyspecs (list (type-spec-long)
                           (type-spec-double)))
      (retok (c::make-tyspecseq-ldouble :complex nil)))
     ((equal tyspecs (list (type-spec-long)
                           (type-spec-double)
                           (type-spec-complex)))
      (retok (c::make-tyspecseq-ldouble :complex t)))
     ((and (consp tyspecs)
           (endp (cdr tyspecs))
           (type-spec-case (car tyspecs) :struct))
      (b* ((tyspec (car tyspecs))
           (ident (check-struni-spec-no-members
                   (type-spec-struct->spec tyspec)))
           ((when (not ident))
            (reterr (msg "Unsupported type specifier ~x0 that is ~
                          a structure specifier with members."
                         tyspec)))
           ((erp ident1) (ldm-ident ident)))
        (retok (c::make-tyspecseq-struct :tag ident1))))
     ((and (consp tyspecs)
           (endp (cdr tyspecs))
           (type-spec-case (car tyspecs) :union))
      (b* ((tyspec (car tyspecs))
           (ident (check-struni-spec-no-members
                   (type-spec-union->spec tyspec)))
           ((when (not ident))
            (reterr (msg "Unsupported type specifier ~x0 that is ~
                          a union specifier with members."
                         tyspec)))
           ((erp ident1) (ldm-ident ident)))
        (retok (c::make-tyspecseq-union :tag ident1))))
     ((and (consp tyspecs)
           (endp (cdr tyspecs))
           (type-spec-case (car tyspecs) :enum))
      (b* ((tyspec (car tyspecs))
           (ident (check-enumspec-no-list
                   (type-spec-enum->spec tyspec)))
           ((when (not ident))
            (reterr (msg "Unsupported type specifier ~x0 that is ~
                          an enumeration specifier with enumerators."
                         tyspec)))
           ((erp ident1) (ldm-ident ident)))
        (retok (c::make-tyspecseq-enum :tag ident1))))
     ((and (consp tyspecs)
           (endp (cdr tyspecs))
           (type-spec-case (car tyspecs) :typedef))
      (b* ((tyspec (car tyspecs))
           (ident (type-spec-typedef->name tyspec))
           ((erp ident1) (ldm-ident ident)))
        (retok (c::make-tyspecseq-typedef :name ident1))))
     (t (reterr (msg "Unsupported type specifier sequence ~x0." tyspecs)))))
  :hooks (:fix)

  ///

  (defret ldm-type-spec-list-ok-when-type-spec-list-integer-formalp
    (not erp)
    :hyp (type-spec-list-integer-formalp tyspecs)
    :hints (("Goal" :in-theory (enable type-spec-list-integer-formalp))))

  (defret ldm-type-spec-list-ok-when-type-spec-list-formalp
    (not erp)
    :hyp (type-spec-list-formalp tyspecs)
    :hints (("Goal" :in-theory (enable type-spec-list-formalp
                                       type-spec-list-integer-formalp
                                       check-struni-spec-no-members)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-stor-spec-list ((stor-specs stor-spec-listp))
  :returns (mv erp (scspecseq c::scspecseqp))
  :short "Map a list of storage class specifiers to
          a storage class specifier sequence in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list must be empty,
     or a singleton with the @('extern') specifier."))
  (b* (((reterr) (c::scspecseq-none))
       (stor-specs (stor-spec-list-fix stor-specs)))
    (cond
     ((equal stor-specs nil)
      (retok (c::scspecseq-none)))
     ((equal stor-specs (list (stor-spec-extern)))
      (retok (c::scspecseq-extern)))
     (t
      (reterr (msg "Unsupported storage class specifier sequence ~x0."
                   stor-specs)))))
  :hooks (:fix)

  ///

  (defret ldm-stor-spec-list-ok-when-stor-spec-list-formalp
    (not erp)
    :hyp (stor-spec-list-formalp stor-specs)
    :hints (("Goal" :in-theory (enable stor-spec-list-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines ldm-declors/dirdeclors-obj
  :short "Map declarators and direct declarators to
          object declarators and direct declarators in the language definition."

  (define ldm-declor-obj ((declor declorp))
    :guard (declor-unambp declor)
    :returns (mv erp (declor1 c::obj-declorp))
    :parents (mapping-to-language-definition ldm-declors/dirdeclors-obj)
    :short "Map a declarator to
            an object declarator in the language definition."
    :long
    (xdoc::topstring
     (xdoc::p
      "We map the direct declarator to an object declarator,
       and then we recursively add pointer layers
       based on the pointer part of the declarator.")
     (xdoc::p
      "This function is called when we expect an object declarator,
       not a function declarator, for which we have a separate function."))
    (b* (((reterr) (c::obj-declor-ident (c::ident "irrelevant")))
         ((declor declor) declor)
         ((erp declor1) (ldm-dirdeclor-obj declor.direct)))
      (ldm-declor-obj-loop declor1 declor.pointers))
    :measure (declor-count declor))

  (define ldm-dirdeclor-obj ((dirdeclor dirdeclorp))
    :guard (dirdeclor-unambp dirdeclor)
    :returns (mv erp (declor1 c::obj-declorp))
    :parents (mapping-to-language-definition ldm-declors/dirdeclors-obj)
    :short "Map a direct declarator to
            an object declarator in the language definition."
    :long
    (xdoc::topstring
     (xdoc::p
      "The abstract syntax in the language definition
       does not have a separate type for direct object declarators,
       so we return an object declarator here.
       The input direct declarator may be an identifier followed by
       zero or more square-bracketed optional integer constant expressions;
       these zero or more array declarator constructs are handled recursively.
       We also allow a parenthesized declarator,
       which we handle with the mutually recursive function.")
     (xdoc::p
      "This function will always result in a @(tsee c::obj-declor)
       of the @(':ident') or @(':array') kind;
       the @(':pointer') kind is generated by @(tsee ldm-declor-obj).")
     (xdoc::p
      "This function is called when we expect an object declarator,
       not a function declarator, for which we have a separate function."))
    (b* (((reterr) (c::obj-declor-ident (c::ident "irrelevant")))
         ((when (dirdeclor-case dirdeclor :ident))
          (b* ((ident (dirdeclor-ident->ident dirdeclor))
               ((erp ident1) (ldm-ident ident)))
            (retok (c::obj-declor-ident ident1))))
         ((when (dirdeclor-case dirdeclor :array))
          (b* (((dirdeclor-array dirdeclor) dirdeclor)
               ((erp declor1) (ldm-dirdeclor-obj dirdeclor.declor))
               ((when dirdeclor.qualspecs)
                (reterr (msg "Unsupported type qualifiers ~
                              or attribute specifiers ~
                              in direct declarator ~x0 for object."
                             (dirdeclor-fix dirdeclor))))
               ((when (not dirdeclor.size?))
                (retok (c::make-obj-declor-array :decl declor1
                                                 :size nil)))
               (iconst (check-expr-iconst dirdeclor.size?))
               ((unless iconst)
                (reterr (msg "Unsupported non-integer-constant size ~
                              in direct declarator ~x0 for object."
                             (dirdeclor-fix dirdeclor))))
               (iconst1 (ldm-iconst iconst)))
            (retok (c::make-obj-declor-array :decl declor1
                                             :size iconst1)))))
      (reterr (msg "Unsupported direct declarator ~x0 for object."
                   (dirdeclor-fix dirdeclor))))
    :measure (dirdeclor-count dirdeclor))

  :verify-guards :after-returns

  :prepwork
  ((define ldm-declor-obj-loop ((declor1 c::obj-declorp)
                                (pointers typequal/attribspec-list-listp))
     :returns (mv erp (declor2 c::obj-declorp))
     :parents nil
     (b* (((reterr) (c::obj-declor-ident (c::ident "irrelevant")))
          ((when (endp pointers)) (retok (c::obj-declor-fix declor1)))
          (tyqualattribs (car pointers))
          ((unless (endp tyqualattribs))
           (reterr (msg "Unsupported type qualifiers ~
                         or attribute specifiers ~
                         ~x0 in pointer."
                        (typequal/attribspec-list-fix tyqualattribs))))
          ((erp declor2) (ldm-declor-obj-loop declor1 (cdr pointers))))
       (retok (c::obj-declor-pointer declor2)))
     :hooks (:fix)

     ///

     (defret ldm-declor-obj-loop-ok-when-pointers-formalp
       (not erp)
       :hyp (pointers-formalp pointers)
       :hints (("Goal" :induct t :in-theory (enable pointers-formalp))))))

  ///

  (defret-mutual ldm-declors/dirdeclors-ok-when-declors/dirdeclors-obj-formalp
    (defret ldm-declor-obj-ok-when-declor-obj-formalp
      (not erp)
      :hyp (declor-obj-formalp declor)
      :fn ldm-declor-obj)
    (defret ldm-dirdeclor-obj-ok-when-dirdeclor-obj-formalp
      (not erp)
      :hyp (dirdeclor-obj-formalp dirdeclor)
      :fn ldm-dirdeclor-obj)
    :hints (("Goal" :in-theory (enable declor-obj-formalp
                                       dirdeclor-obj-formalp))))

  (defret-mutual
    ldm-declors/dirdeclors-obj-ok-when-declors/dirdeclors-block-formalp
    (defret ldm-declor-obj-ok-when-declor-block-formalp
      (not erp)
      :hyp (declor-block-formalp declor)
      :fn ldm-declor-obj)
    (defret ldm-dirdeclor-obj-ok-when-dirdeclor-block-formalp
      (not erp)
      :hyp (dirdeclor-block-formalp dirdeclor)
      :fn ldm-dirdeclor-obj)
    :hints (("Goal" :in-theory (enable declor-block-formalp
                                       dirdeclor-block-formalp))))

  (fty::deffixequiv-mutual ldm-declors/dirdeclors-obj))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-dirabsdeclor-obj ((dirabsdeclor dirabsdeclorp))
  :guard (dirabsdeclor-unambp dirabsdeclor)
  :returns (mv erp (adeclor1 c::obj-adeclorp))
  :short "Map a direct abstract declarator to
          an abstract object declarator in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee ldm-dirdeclor-obj),
     but for abstract declarators.
     But it has a different recursive structure because
     we must always have an array declarator,
     and the recursion ends when the nested direct declarator is absent.")
   (xdoc::p
    "This function is called when we expect an abstract object declarator,
     not a function declarator, for which we have a separate function."))
  (b* (((reterr) (c::obj-adeclor-none))
       ((unless (dirabsdeclor-case dirabsdeclor :array))
        (reterr (msg "Unsupported direct abstract declarator ~x0 for object."
                     (dirabsdeclor-fix dirabsdeclor))))
       ((dirabsdeclor-array dirabsdeclor) dirabsdeclor)
       ((when dirabsdeclor.qualspecs)
        (reterr (msg "Unsupported type qualifiers ~
                      or attribute specifiers ~
                      in direct abstract declarator ~x0 for object."
                     (dirabsdeclor-fix dirabsdeclor))))
       ((erp iconst?)
        (if dirabsdeclor.size?
            (b* ((iconst (check-expr-iconst dirabsdeclor.size?)))
              (if iconst
                  (retok (ldm-iconst iconst))
                (reterr (msg "Unsupported non-integer-constant size ~
                              in direct abstract declarator ~x0 for object."
                             (dirabsdeclor-fix dirabsdeclor)))))
          (retok nil)))
       ((when (dirabsdeclor-option-case dirabsdeclor.declor? :none))
        (retok (c::make-obj-adeclor-array :decl (c::obj-adeclor-none)
                                          :size iconst?)))
       (dirabsdeclor.decl (dirabsdeclor-option-some->val dirabsdeclor.declor?))
       ((erp adeclor1) (ldm-dirabsdeclor-obj dirabsdeclor.decl)))
    (retok (c::make-obj-adeclor-array :decl adeclor1
                                      :size iconst?)))
  :measure (dirabsdeclor-count dirabsdeclor)
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-absdeclor-obj ((absdeclor absdeclorp))
  :guard (absdeclor-unambp absdeclor)
  :returns (mv erp (adeclor1 c::obj-adeclorp))
  :short "Map an abstract declarator to
          an abstract object declarator in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee ldm-declor-obj),
     but for abstract declarators.
     But there is a difference in how we handle the direct abstract declarator,
     since that may be present or not.
     If not present, we wrap pointers around
     the @(':none') case of @(tsee c::obj-adeclor).")
   (xdoc::p
    "This function is called when we expect an abstract object declarator,
     not a function declarator, for which we have a separate function."))
  (b* (((reterr) (c::obj-adeclor-none))
       ((absdeclor absdeclor) absdeclor)
       ((erp adeclor1)
        (if absdeclor.direct?
            (ldm-dirabsdeclor-obj absdeclor.direct?)
          (retok (c::obj-adeclor-none)))))
    (ldm-absdeclor-obj-loop adeclor1 absdeclor.pointers))
  :hooks (:fix)

  :prepwork
  ((define ldm-absdeclor-obj-loop ((adeclor1 c::obj-adeclorp)
                                   (pointers typequal/attribspec-list-listp))
     :returns (mv erp (adeclor2 c::obj-adeclorp))
     :parents nil
     (b* (((reterr) (c::obj-adeclor-none))
          ((when (endp pointers)) (retok (c::obj-adeclor-fix adeclor1)))
          (qualspecs (car pointers))
          ((unless (endp qualspecs))
           (reterr (msg "Unsupported type qualifiers ~
                         or attribute specifiers ~
                         ~x0 in pointer."
                        (typequal/attribspec-list-fix qualspecs))))
          ((erp adeclor2) (ldm-absdeclor-obj-loop adeclor1 (cdr pointers))))
       (retok (c::obj-adeclor-pointer adeclor2)))
     :hooks (:fix)

     ///

     (defret ldm-absdeclor-obj-loop-ok-when-pointers-formalp
       (not erp)
       :hyp (pointers-formalp pointers)
       :hints (("Goal" :in-theory (enable pointers-formalp)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-tyname ((tyname tynamep))
  :guard (tyname-unambp tyname)
  :returns (mv erp (tyname1 c::tynamep))
  :short "Map a type name to a type name in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The specifiers and qualifiers must be all type specifiers,
     and must form a supported sequence."))
  (b* (((reterr) (c::tyname (c::tyspecseq-void) (c::obj-adeclor-none)))
       ((tyname tyname) tyname)
       ((mv okp tyspecs) (check-spec/qual-list-all-typespec tyname.specquals))
       ((when (not okp))
        (reterr (msg "Unsupported specifiers and qualifiers ~
                      in type name ~x0."
                     (tyname-fix tyname))))
       ((erp tyspecseq) (ldm-type-spec-list tyspecs))
       ((when (not tyname.declor?))
        (retok (c::make-tyname :tyspec tyspecseq
                               :declor (c::obj-adeclor-none))))
       ((erp adeclor1) (ldm-absdeclor-obj tyname.declor?)))
    (retok (c::make-tyname :tyspec tyspecseq
                           :declor adeclor1)))
  :hooks (:fix)

  ///

  (defret ldm-tyname-ok-when-tyname-formalp
    (not erp)
    :hyp (tyname-formalp tyname)
    :hints (("Goal" :in-theory (enable tyname-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-binop ((binop binopp))
  :returns (binop1 c::binopp)
  :short "Map a binary operator to
          a binary operator in the language definition."
  (binop-case
   binop
   :mul (c::binop-mul)
   :div (c::binop-div)
   :rem (c::binop-rem)
   :add (c::binop-add)
   :sub (c::binop-sub)
   :shl (c::binop-shl)
   :shr (c::binop-shr)
   :lt (c::binop-lt)
   :gt (c::binop-gt)
   :le (c::binop-le)
   :ge (c::binop-ge)
   :eq (c::binop-eq)
   :ne (c::binop-ne)
   :bitand (c::binop-bitand)
   :bitxor (c::binop-bitxor)
   :bitior (c::binop-bitior)
   :logand (c::binop-logand)
   :logor (c::binop-logor)
   :asg (c::binop-asg)
   :asg-mul (c::binop-asg-mul)
   :asg-div (c::binop-asg-div)
   :asg-rem (c::binop-asg-rem)
   :asg-add (c::binop-asg-add)
   :asg-sub (c::binop-asg-sub)
   :asg-shl (c::binop-asg-shl)
   :asg-shr (c::binop-asg-shr)
   :asg-and (c::binop-asg-and)
   :asg-xor (c::binop-asg-xor)
   :asg-ior (c::binop-asg-ior))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines ldm-exprs
  :short "Map expressions to expressions in the language definition."

  (define ldm-expr ((expr exprp))
    :guard (expr-unambp expr)
    :returns (mv erp (expr1 c::exprp))
    :parents (mapping-to-language-definition ldm-exprs)
    :short "Map an expression to an expression in the language definition."
    (b* (((reterr) (c::expr-ident (c::ident "irrelevant"))))
      (expr-case
       expr
       :ident (b* (((erp ident1) (ldm-ident expr.ident)))
                (retok (c::expr-ident ident1)))
       :const (b* (((erp const1) (ldm-const expr.const)))
                (retok (c::expr-const const1)))
       :string (reterr (msg "Unsupported expression ~x0." (expr-fix expr)))
       :paren (ldm-expr expr.inner)
       :gensel (reterr (msg "Unsupported expression ~x0." (expr-fix expr)))
       :arrsub (b* (((erp arr1) (ldm-expr expr.arg1))
                    ((erp sub1) (ldm-expr expr.arg2)))
                 (retok (c::make-expr-arrsub :arr arr1 :sub sub1)))
       :funcall (b* ((ident (check-expr-ident expr.fun))
                     ((when (not ident))
                      (reterr (msg "Unsupported non-identifier function ~x0."
                                   expr.fun)))
                     ((erp ident1) (ldm-ident ident))
                     ((erp args1) (ldm-expr-list expr.args)))
                  (retok (c::make-expr-call :fun ident1 :args args1)))
       :member (b* (((erp target1) (ldm-expr expr.arg))
                    ((erp ident1) (ldm-ident expr.name)))
                 (retok (c::make-expr-member :target target1 :name ident1)))
       :memberp (b* (((erp target1) (ldm-expr expr.arg))
                     ((erp ident1) (ldm-ident expr.name)))
                  (retok (c::make-expr-memberp :target target1 :name ident1)))
       :complit (reterr (msg "Unsupported expression ~x0." (expr-fix expr)))
       :unary
       (b* (((erp arg) (ldm-expr expr.arg)))
         (unop-case
          expr.op
          :address (retok (c::make-expr-unary :op (c::unop-address) :arg arg))
          :indir (retok (c::make-expr-unary :op (c::unop-indir) :arg arg))
          :plus (retok (c::make-expr-unary :op (c::unop-plus) :arg arg))
          :minus (retok (c::make-expr-unary :op (c::unop-minus) :arg arg))
          :bitnot (retok (c::make-expr-unary :op (c::unop-bitnot) :arg arg))
          :lognot (retok (c::make-expr-unary :op (c::unop-lognot) :arg arg))
          :preinc (retok (c::expr-preinc arg))
          :predec (retok (c::expr-predec arg))
          :postinc (retok (c::expr-postinc arg))
          :postdec (retok (c::expr-postdec arg))
          :sizeof (reterr (msg "Unsupported sizeof operator."))))
       :sizeof (reterr (msg "Unsupported expression ~x0." (expr-fix expr)))
       :sizeof-ambig (prog2$ (impossible) (reterr t))
       :alignof (reterr (msg "Unsupported expression ~x0." (expr-fix expr)))
       :cast (b* (((erp tyname) (ldm-tyname expr.type))
                  ((erp arg) (ldm-expr expr.arg)))
               (retok (c::make-expr-cast :type tyname :arg arg)))
       :binary (b* (((erp arg1) (ldm-expr expr.arg1))
                    ((erp arg2) (ldm-expr expr.arg2))
                    (op (ldm-binop expr.op)))
                 (retok (c::make-expr-binary :op op :arg1 arg1 :arg2 arg2)))
       :cond (b* (((erp test) (ldm-expr expr.test))
                  ((when (expr-option-case expr.then :none))
                   (reterr (msg "Unsupported conditional expression ~
                                 with omitted operand ~x0."
                                (expr-fix expr))))
                  (expr.then (expr-option-some->val expr.then))
                  ((erp then) (ldm-expr expr.then))
                  ((erp else) (ldm-expr expr.else)))
               (retok (c::make-expr-cond :test test :then then :else else)))
       :comma (reterr (msg "Unsupported expression ~x0." (expr-fix expr)))
       :cast/call-ambig (prog2$ (impossible) (reterr t))
       :cast/mul-ambig (prog2$ (impossible) (reterr t))
       :cast/add-ambig (prog2$ (impossible) (reterr t))
       :cast/sub-ambig (prog2$ (impossible) (reterr t))
       :cast/and-ambig (prog2$ (impossible) (reterr t))
       :stmt (reterr (msg "Unsupported expression ~x0." (expr-fix expr)))
       :tycompat (reterr (msg "Unsupported expression ~x0." (expr-fix expr)))
       :offsetof (reterr (msg "Unsupported expression ~x0." (expr-fix expr)))
       :va-arg (reterr (msg "Unsupported expression ~x0." (expr-fix expr)))
       :extension (reterr (msg "Unsupported expression ~x0." (expr-fix expr)))))
    :measure (expr-count expr))

  (define ldm-expr-list ((exprs expr-listp))
    :guard (expr-list-unambp exprs)
    :returns (mv erp (exprs1 c::expr-listp))
    :parents (mapping-to-language-definition ldm-exprs)
    :short "Map a list of expressions to
            a list of expressions in the language definition."
    (b* (((reterr) nil)
         ((when (endp exprs)) (retok nil))
         ((erp expr1) (ldm-expr (car exprs)))
         ((erp exprs1) (ldm-expr-list (cdr exprs))))
      (retok (cons expr1 exprs1)))
    :measure (expr-list-count exprs))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual ldm-exprs)

  (defret-mutual ldm-exprs-ok-when-exprs-formalp
    (defret ldm-expr-ok-when-expr-pure-formalp
      (not erp)
      :hyp (expr-pure-formalp expr)
      :fn ldm-expr)
    (defret ldm-expr-list-ok-when-expr-list-pure-formalp
      (not erp)
      :hyp (expr-list-pure-formalp exprs)
      :fn ldm-expr-list)
    :hints (("Goal"
             :expand (expr-pure-formalp expr)
             :in-theory (enable expr-pure-formalp
                                expr-list-pure-formalp))))

  (defret ldm-expr-ok-when-expr-call-formalp
    (not erp)
    :hyp (expr-call-formalp expr)
    :fn ldm-expr
    :hints (("Goal"
             :in-theory (enable expr-call-formalp
                                check-expr-ident)
             :expand (ldm-expr expr))))

  (defret ldm-expr-ok-when-expr-asg-formalp
    (not erp)
    :hyp (expr-asg-formalp expr)
    :fn ldm-expr
    :hints (("Goal"
             :in-theory (enable expr-asg-formalp
                                expr-pure-formalp)
             :expand (ldm-expr expr)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-expr-option ((expr? expr-optionp))
  :guard (expr-option-unambp expr?)
  :returns (mv erp (expr?1 c::expr-optionp))
  :short "Map an optional expression to
          an optional expression in the language definition."
  (b* (((reterr) nil))
    (expr-option-case
     expr?
     :some (ldm-expr expr?.val)
     :none (retok nil)))
  :hooks (:fix)

  ///

  (defret ldm-expr-option-ok-when-expr-pure-formalp
    (not erp)
    :hyp (expr-pure-formalp expr?)
    :hints (("Goal" :in-theory (enable expr-option-some->val))))

  (defret ldm-expr-option-ok-when-expr-call-formalp
    (not erp)
    :hyp (expr-call-formalp expr?)
    :hints (("Goal" :in-theory (enable expr-option-some->val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-structdecl ((structdecl structdeclp))
  :guard (structdecl-unambp structdecl)
  :returns (mv erp (structdecl1 c::struct-declonp))
  :short "Map a structure declaration to
          a structure declaration in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The specifiers and qualifiers must be all type specifiers,
     and must form a supported type specifier sequence.")
   (xdoc::p
    "There must be a single structure declarator,
     which must have a declarator and no constant expression."))
  (b* (((reterr) (c::struct-declon (c::tyspecseq-void)
                                   (c::obj-declor-ident
                                    (c::ident "irrelevant"))))
       ((when (structdecl-case structdecl :empty))
        (reterr (msg "Unsupported empty structure declaration.")))
       ((when (structdecl-case structdecl :statassert))
        (reterr (msg "Unsupported structure declaration ~x0."
                     (structdecl-fix structdecl))))
       (extension (structdecl-member->extension structdecl))
       ((when extension)
        (reterr (msg "Unsupported GCC extension keyword ~
                      in structure declaration ~x0."
                     (structdecl-fix structdecl))))
       (specquals (structdecl-member->specqual structdecl))
       (declors (structdecl-member->declor structdecl))
       ((mv okp tyspecs) (check-spec/qual-list-all-typespec specquals))
       ((unless okp)
        (reterr (msg "Unsupported specifier and qualifier list ~
                      in structure declaration ~x0."
                     (structdecl-fix structdecl))))
       ((erp tyspecseq) (ldm-type-spec-list tyspecs))
       ((unless (and (consp declors)
                     (endp (cdr declors))))
        (reterr (msg "Unsupported number of declarators ~
                      in structure declaration ~x0."
                     (structdecl-fix structdecl))))
       ((structdeclor declor) (car declors))
       ((unless declor.declor?)
        (reterr (msg "Unsupported structure declarator ~
                      in structure declaration ~x0."
                     (structdecl-fix structdecl))))
       ((when declor.expr?)
        (reterr (msg "Unsupported structure declarator ~
                      in structure declaration ~x0."
                     (structdecl-fix structdecl))))
       ((erp objdeclor) (ldm-declor-obj declor.declor?))
       (attrib (structdecl-member->attrib structdecl))
       ((when attrib)
        (reterr (msg "Unsupporte GCC attributes ~
                      in structure declaration ~x0."
                     (structdecl-fix structdecl)))))
    (retok (c::make-struct-declon :tyspec tyspecseq :declor objdeclor)))
  :hooks (:fix)

  ///

  (defret ldm-structdecl-ok-when-structdecl-formalp
    (not erp)
    :hyp (structdecl-formalp structdecl)
    :hints (("Goal" :in-theory (enable structdecl-formalp
                                       structdeclor-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-structdecl-list ((structdecls structdecl-listp))
  :guard (structdecl-list-unambp structdecls)
  :returns (mv erp (structdecls1 c::struct-declon-listp))
  :short "Map a list of structure declarations to
          a list of structure declarations in the language definition."
  (b* (((reterr) nil)
       ((when (endp structdecls)) (retok nil))
       ((erp structdecl1) (ldm-structdecl (car structdecls)))
       ((erp structdecls1) (ldm-structdecl-list (cdr structdecls))))
    (retok (cons structdecl1 structdecls1)))
  :hooks (:fix)

  ///

  (defret ldm-structdecl-list-ok-when-structdecl-list-formalp
    (not erp)
    :hyp (structdecl-list-formalp structdecls)
    :hints (("Goal" :induct t :in-theory (enable structdecl-list-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-enumer ((enumer enumerp))
  :guard (enumer-unambp enumer)
  :returns (mv erp (ident c::identp))
  :short "Map an enumerator to
          an identifier in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only support enumerators without expression,
     so they are really just identifiers."))
  (b* (((reterr) (c::ident "irrelevant"))
       ((enumer enumer) enumer)
       ((when enumer.value)
        (reterr (msg "Unsupported enumerator ~x0." (enumer-fix enumer)))))
    (ldm-ident enumer.name))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-enumer-list ((enumers enumer-listp))
  :guard (enumer-list-unambp enumers)
  :returns (mv erp (idents c::ident-listp))
  :short "Map a list of enumerators to
          a list of identifiers in the language definition."
  (b* (((reterr) nil)
       ((when (endp enumers)) (retok nil))
       ((erp ident) (ldm-enumer (car enumers)))
       ((erp idents) (ldm-enumer-list (cdr enumers))))
    (retok (cons ident idents)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-decl-tag ((decl declp))
  :guard (decl-unambp decl)
  :returns (mv erp (tagdeclon c::tag-declonp))
  :short "Map a declaration to
          a tag declaration in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declaration must not be a static assertion declaration,
     and must consists of a single type specifier without declarators.
     The type specifier must be a structure, union, or enumeration specifier
     with members/elements."))
  (b* (((reterr) (c::tag-declon-enum (c::ident "irrelevant") nil))
       ((when (decl-case decl :statassert))
        (reterr (msg "Unsupported static assertion declaration ~x0."
                     (decl-fix decl))))
       (extension (decl-decl->extension decl))
       (declspecs (decl-decl->specs decl))
       (initdeclors (decl-decl->init decl))
       ((when extension)
        (reterr (msg "Unsupported GCC extension keyword ~
                      for tag (i.e. structure/union/enumeration) ~
                      declaration.")))
       ((when initdeclors)
        (reterr (msg "Unsupported initialization declarators ~x0 ~
                      for tag (i.e. structure/union/enumeration) declaration."
                     initdeclors)))
       ((unless (and (consp declspecs)
                     (endp (cdr declspecs))))
        (reterr (msg "Unsupported number of declaration specifiers ~x0 ~
                      for tag (i.e. structure/union/enumeration) declaration."
                     declspecs)))
       (declspec (car declspecs))
       ((unless (decl-spec-case declspec :typespec))
        (reterr (msg "Unsupported declaration specifier ~x0 ~
                      for tag (i.e. structure/union/enumeration) declaration."
                     declspec)))
       (tyspec (decl-spec-typespec->spec declspec))
       ((when (type-spec-case tyspec :struct))
        (b* (((struni-spec struni-spec) (type-spec-struct->spec tyspec))
             ((unless struni-spec.name?)
              (reterr (msg "Unsupported structure declaration without name.")))
             ((erp name1) (ldm-ident struni-spec.name?))
             ((erp members1) (ldm-structdecl-list struni-spec.members)))
          (retok (c::make-tag-declon-struct :tag name1 :members members1))))
       ((when (type-spec-case tyspec :union))
        (b* (((struni-spec struni-spec) (type-spec-union->spec tyspec))
             ((unless struni-spec.name?)
              (reterr (msg "Unsupported union declaration without name.")))
             ((erp name1) (ldm-ident struni-spec.name?))
             ((erp members1) (ldm-structdecl-list struni-spec.members)))
          (retok (c::make-tag-declon-union :tag name1 :members members1))))
       ((when (type-spec-case tyspec :enum))
        (b* (((enumspec enumspec) (type-spec-enum->spec tyspec))
             ((unless enumspec.name)
              (reterr
               (msg "Unsupported enumeration declaration without name.")))
             ((erp name1) (ldm-ident enumspec.name))
             ((erp idents1) (ldm-enumer-list enumspec.list)))
          (retok (c::make-tag-declon-enum :tag name1 :enumerators idents1)))))
    (reterr (msg "Unsupported type specifier ~x0 ~
                  for tag (i.e. structure/union/enumeration) declaration."
                 tyspec)))
  :hooks (:fix)

  ///

  (defret ldm-decl-tag-ok-when-decl-struct-formalp
    (not erp)
    :hyp (decl-struct-formalp decl)
    :hints (("Goal" :in-theory (enable decl-struct-formalp
                                       struni-spec-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-param-declor ((paramdeclor param-declorp))
  :guard (param-declor-unambp paramdeclor)
  :returns (mv erp (objdeclor c::obj-declorp))
  :short "Map a parameter declarator to
          an object declarator in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The parameter declarator must be present and not abstract.
     The declarator must be for an object,
     which we map to an object declarator."))
  (b* (((reterr) (c::obj-declor-ident (c::ident "irrelevant")))
       ((when (param-declor-case paramdeclor :abstract))
        (reterr (msg "Unsupported parameter declarator ~x0 ~
                      with abstract declarator."
                     (param-declor-fix paramdeclor))))
       ((when (param-declor-case paramdeclor :none))
        (reterr (msg "Unsupported absent parameter declarator ~x0.")))
       ((when (param-declor-case paramdeclor :ambig))
        (prog2$ (impossible) (reterr t)))
       (declor (param-declor-nonabstract->declor paramdeclor)))
    (ldm-declor-obj declor))
  :hooks (:fix)

  ///

  (defret ldm-param-declor-ok-when-param-declor-formalp
    (not erp)
    :hyp (param-declor-formalp paramdeclor)
    :hints (("Goal" :in-theory (enable param-declor-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-param-declon ((paramdecl param-declonp))
  :guard (param-declon-unambp paramdecl)
  :returns (mv erp (paramdecl1 c::param-declonp))
  :short "Map a parameter declaration to
          a parameter declaration in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declaration specifiers must be all type specifiers,
     and must form a supported type specifier sequence.")
   (xdoc::p
    "The parameter declarator must map to an object declarator.")
   (xdoc::p
    "There must be no ending attribute specifiers."))
  (b* (((reterr) (c::param-declon (c::tyspecseq-void)
                                  (c::obj-declor-ident
                                   (c::ident "irrelevant"))))
       ((when (param-declon->attribs paramdecl))
        (reterr (msg "Unsupported attribute specifiers ~
                      in parameter declaration ~x0."
                     (param-declon-fix paramdecl))))
       (declspecs (param-declon->specs paramdecl))
       (declor (param-declon->declor paramdecl))
       ((mv okp tyspecs) (check-decl-spec-list-all-typespec declspecs))
       ((unless okp)
        (reterr (msg "Unsupported declaration specifier list ~
                      in parameter declaration ~x0."
                     (param-declon-fix paramdecl))))
       ((erp tyspecseq) (ldm-type-spec-list tyspecs))
       ((erp objdeclor) (ldm-param-declor declor)))
    (retok (c::make-param-declon :tyspec tyspecseq :declor objdeclor)))
  :hooks (:fix)

  ///

  (defret ldm-param-declon-ok-when-param-declon-formalp
    (not erp)
    :hyp (param-declon-formalp paramdecl)
    :hints (("Goal" :in-theory (enable param-declon-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-param-declon-list ((paramdecls param-declon-listp))
  :guard (param-declon-list-unambp paramdecls)
  :returns (mv erp (paramdecls1 c::param-declon-listp))
  :short "Map a list of parameter declarations to
          a list of parameter declarations in the language definition."
  (b* (((reterr) nil)
       ((when (endp paramdecls)) (retok nil))
       ((erp paramdecl1) (ldm-param-declon (car paramdecls)))
       ((erp paramdecls1) (ldm-param-declon-list (cdr paramdecls))))
    (retok (cons paramdecl1 paramdecls1)))
  :hooks (:fix)

  ///

  (defret ldm-param-declon-list-ok-when-param-declon-list-formalp
    (not erp)
    :hyp (param-declon-list-formalp paramdecls)
    :hints (("Goal" :in-theory (enable param-declon-list-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-dirdeclor-fun ((dirdeclor dirdeclorp))
  :guard (dirdeclor-unambp dirdeclor)
  :returns (mv erp (fundeclor c::fun-declorp))
  :short "Map a direct declarator to
          a function declarator in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The abstract syntax in the language definition
     does not have a separate type for direct function declarators,
     so we return a function declarator here.
     The input direct declarator must be an identifier
     followed by a single parenthesized list of parameter declarations,
     or an empty list of parameter names.")
   (xdoc::p
    "This function will always result in a @(tsee c::fun-declor)
     of the @(':base') kind;
     the @(':pointer') kind is generated by @(tsee ldm-declor-fun).")
   (xdoc::p
    "This function is called when we expect a function declarator,
     not an object declarator, for which we have a separate function."))
  (b* (((reterr) (c::fun-declor-base (c::ident "irrelevant") nil))
       ((unless (or (dirdeclor-case dirdeclor :function-params)
                    (and (dirdeclor-case dirdeclor :function-names)
                         (endp (dirdeclor-function-names->names dirdeclor)))))
        (reterr (msg "Unsupported direct declarator ~x0 for function."
                     (dirdeclor-fix dirdeclor))))
       ((mv inner-dirdeclor params)
        (if (dirdeclor-case dirdeclor :function-params)
            (mv (dirdeclor-function-params->declor dirdeclor)
                (dirdeclor-function-params->params dirdeclor))
          (mv (dirdeclor-function-names->declor dirdeclor)
              nil)))
       ((unless (dirdeclor-case inner-dirdeclor :ident))
        (reterr (msg "Unsupported direct declarator ~x0 for function."
                     (dirdeclor-fix dirdeclor))))
       (ident (dirdeclor-ident->ident inner-dirdeclor))
       ((erp ident1) (ldm-ident ident))
       ((erp params1) (ldm-param-declon-list params)))
    (retok (c::make-fun-declor-base :name ident1 :params params1)))
  :hooks (:fix)

  ///

  (defret ldm-dirdeclor-fun-ok-when-dirdeclor-fun-formalp
    (not erp)
    :hyp (dirdeclor-fun-formalp dirdeclor)
    :hints (("Goal" :in-theory (enable dirdeclor-fun-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-declor-fun ((declor declorp))
  :guard (declor-unambp declor)
  :returns (mv erp (fundeclor c::fun-declorp))
  :short "Map a declarator to
          a function declarator in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "We map the direct declarator to a function declarator,
     and then we recursively add pointer layers
     based on the pointer part of the declarator.")
   (xdoc::p
    "This function is called when we expect a function declarator,
     not an object declarator, for which we have a separate function."))
  (b* (((reterr) (c::fun-declor-base (c::ident "irrelevant") nil))
       ((declor declor) declor)
       ((erp declor1) (ldm-dirdeclor-fun declor.direct)))
    (ldm-declor-fun-loop declor1 declor.pointers))
  :hooks (:fix)

  :prepwork
  ((define ldm-declor-fun-loop ((declor1 c::fun-declorp)
                                (pointers typequal/attribspec-list-listp))
     :returns (mv erp (declor2 c::fun-declorp))
     :parents nil
     (b* (((reterr) (c::fun-declor-base (c::ident "irrelevant") nil))
          ((when (endp pointers)) (retok (c::fun-declor-fix declor1)))
          (qualspecs (car pointers))
          ((unless (endp qualspecs))
           (reterr (msg "Unsupported type qualifiers ~x0 in pointer."
                        (typequal/attribspec-list-fix qualspecs))))
          ((erp declor2) (ldm-declor-fun-loop declor1 (cdr pointers))))
       (retok (c::fun-declor-pointer declor2)))
     :hooks (:fix)

     ///

     (defret ldm-declor-fun-loop-ok-when-pointers-formalp
       (not erp)
       :hyp (pointers-formalp pointers)
       :hints (("Goal" :induct t :in-theory (enable pointers-formalp))))))

  ///

  (defret ldm-declor-fun-ok-when-declor-fun-formalp
    (not erp)
    :hyp (declor-fun-formalp declor)
    :hints (("Goal" :in-theory (enable declor-fun-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-decl-fun ((decl declp))
  :guard (decl-unambp decl)
  :returns (mv erp (fundeclon c::fun-declonp))
  :short "Map a declaration to
          a function declaration in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declaration must not be a static assertion declaration.")
   (xdoc::p
    "The declaration specifiers must be all type specifiers,
     and form a supported sequence.")
   (xdoc::p
    "The initialization declarator must be a declarator,
     without initializer,
     and it must be a supported declarator for a function."))
  (b* (((reterr) (c::fun-declon (c::tyspecseq-void)
                                (c::fun-declor-base
                                 (c::ident "irrelevant") nil)))
       ((when (decl-case decl :statassert))
        (reterr (msg "Unsupported static assertion declaration ~x0."
                     (decl-fix decl))))
       (extension (decl-decl->extension decl))
       (declspecs (decl-decl->specs decl))
       (initdeclors (decl-decl->init decl))
       ((when extension)
        (reterr (msg "Unsupported GCC extension keyword ~
                      for tag (i.e. structure/union/enumeration) ~
                      declaration.")))
       ((mv okp tyspecs) (check-decl-spec-list-all-typespec declspecs))
       ((when (not okp))
        (reterr (msg "Unsupported declaration specifier list ~
                      in declaration ~x0 for function."
                     (decl-fix decl))))
       ((erp tyspecseq) (ldm-type-spec-list tyspecs))
       ((unless (and (consp initdeclors)
                     (endp (cdr initdeclors))))
        (reterr (msg "Unsupported number of declarators ~x0 ~
                      for function declaration."
                     initdeclors)))
       ((initdeclor initdeclor) (car initdeclors))
       ((when initdeclor.init?)
        (reterr (msg "Unsupported initializer ~x0 ~
                      for function declaration."
                     initdeclor.init?)))
       ((when initdeclor.asm?)
        (reterr (msg "Unsupported assembler name specifier ~x0 ~
                      for function declaration."
                     initdeclor.asm?)))
       ((unless (endp initdeclor.attribs))
        (reterr (msg "Unsupported attribute specifiers ~x0 ~
                      for function declaration."
                     initdeclor.attribs)))
       ((erp fundeclor) (ldm-declor-fun initdeclor.declor)))
    (retok (c::make-fun-declon :tyspec tyspecseq :declor fundeclor)))
  :hooks (:fix)

  ///

  (defret ldm-decl-fun-ok-when-decl-fun-formalp
    (not erp)
    :hyp (decl-fun-formalp decl)
    :hints (("Goal" :in-theory (enable decl-fun-formalp
                                       initdeclor-fun-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-desiniter ((desiniter desiniterp))
  :guard (desiniter-unambp desiniter)
  :returns (mv erp (expr c::exprp))
  :short "Map an initializer with optional designations
          to an initializer expression in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be no designators,
     and the nested initializer must be for a single expression."))
  (b* (((reterr) (c::expr-ident (c::ident "irrelevant")))
       ((desiniter desiniter) desiniter)
       ((when desiniter.designors)
        (reterr (msg "Unsupported designators ~x0." desiniter.designors)))
       ((unless (initer-case desiniter.initer :single))
        (reterr (msg "Unsupported nested initializer ~x0." desiniter.initer))))
    (ldm-expr (initer-single->expr desiniter.initer)))
  :hooks (:fix)

  ///

  (defret ldm-desiniter-ok-when-desiniter-formalp
    (not erp)
    :hyp (desiniter-formalp desiniter)
    :hints (("Goal" :in-theory (enable desiniter-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-desiniter-list ((desiniters desiniter-listp))
  :guard (desiniter-list-unambp desiniters)
  :returns (mv erp (exprs c::expr-listp))
  :short "Map a list of initializers with optional designations to
          a list of initializer expressions in the language definition."
  (b* (((reterr) nil)
       ((when (endp desiniters)) (retok nil))
       ((erp expr1) (ldm-desiniter (car desiniters)))
       ((erp exprs1) (ldm-desiniter-list (cdr desiniters))))
    (retok (cons expr1 exprs1)))
  :hooks (:fix)

  ///

  (defret ldm-desiniter-list-ok-when-desiniter-list-formalp
    (not erp)
    :hyp (desiniter-list-formalp desiniters)
    :hints (("Goal" :in-theory (enable desiniter-list-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-initer ((initer initerp))
  :guard (initer-unambp initer)
  :returns (mv erp (initer1 c::initerp))
  :short "Map an initializer to
          an initializer in the language definition."
  (b* (((reterr) (c::initer-list nil)))
    (initer-case
     initer
     :single (b* (((erp expr1) (ldm-expr initer.expr)))
               (retok (c::initer-single expr1)))
     :list (b* (((erp exprs1) (ldm-desiniter-list initer.elems)))
             (retok (c::initer-list exprs1)))))
  :hooks (:fix)

  ///

  (defret ldm-initer-ok-when-initer-formalp
    (not erp)
    :hyp (initer-formalp initer)
    :hints (("Goal" :in-theory (enable initer-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-decl-obj ((decl declp))
  :guard (decl-unambp decl)
  :returns (mv erp (objdeclon c::obj-declonp))
  :short "Map a declaration to
          an object declaration in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declaration must not be a static assertion declaration.")
   (xdoc::p
    "The declaration specifiers must include only
     type specifiers and storage class specifiers,
     each of which must form a supported sequence.")
   (xdoc::p
    "There must be a single initializer declarator."))
  (b* (((reterr) (c::obj-declon (c::scspecseq-none)
                                (c::tyspecseq-void)
                                (c::obj-declor-ident (c::ident "irrelevant"))
                                nil))
       ((when (decl-case decl :statassert))
        (reterr (msg "Unsupported static assertion declaration ~x0."
                     (decl-fix decl))))
       (extension (decl-decl->extension decl))
       (declspecs (decl-decl->specs decl))
       (initdeclors (decl-decl->init decl))
       ((when extension)
        (reterr (msg "Unsupported GCC extension keyword ~
                      for tag (i.e. structure/union/enumeration) ~
                      declaration.")))
       ((mv okp tyspecs stor-specs)
        (check-decl-spec-list-all-typespec/stoclass declspecs))
       ((unless okp)
        (reterr (msg "Unsupported declaration specifiers ~x0 ~
                      for object declaration."
                     declspecs)))
       ((erp tyspecseq) (ldm-type-spec-list tyspecs))
       ((erp scspecseq) (ldm-stor-spec-list stor-specs))
       ((unless (and (consp initdeclors)
                     (endp (cdr initdeclors))))
        (reterr (msg "Unsupported number of initializer declarators ~x0 ~
                      for object declaration."
                     initdeclors)))
       ((initdeclor initdeclor) (car initdeclors))
       ((erp objdeclor) (ldm-declor-obj initdeclor.declor))
       ((when initdeclor.asm?)
        (reterr (msg "Unsupported assembler name specifier ~x0 ~
                      for object declaration."
                     initdeclor.asm?)))
       ((unless (endp initdeclor.attribs))
        (reterr (msg "Unsupported attribute specifiers ~x0 ~
                      for function declaration."
                     initdeclor.attribs)))
       ((when (not initdeclor.init?))
        (retok (c::make-obj-declon :scspec scspecseq
                                   :tyspec tyspecseq
                                   :declor objdeclor
                                   :init? nil)))
       ((erp init) (ldm-initer initdeclor.init?)))
    (retok (c::make-obj-declon :scspec scspecseq
                               :tyspec tyspecseq
                               :declor objdeclor
                               :init? init)))
  :hooks (:fix)

  ///

  (defret ldm-decl-obj-ok-when-decl-obj-formalp
    (not erp)
    :hyp (decl-obj-formalp decl)
    :hints (("Goal" :in-theory (enable decl-obj-formalp
                                       initdeclor-obj-formalp))))

  (defret ldm-decl-obj-ok-when-decl-block-formalp
    (not erp)
    :hyp (decl-block-formalp decl)
    :hints
    (("Goal"
      :in-theory
      (enable decl-block-formalp
              initdeclor-block-formalp
              check-decl-spec-list-all-typespec/stoclass-when-all-typespec)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-label ((label labelp))
  :guard (label-unambp label)
  :returns (mv erp (label1 c::labelp))
  :short "Map a label to a label in the language definition."
  (b* (((reterr) (c::label-default)))
    (label-case
     label
     :name (b* (((erp ident1) (ldm-ident label.unwrap)))
             (retok (c::label-name ident1)))
     :casexpr (b* (((erp expr) (ldm-expr (const-expr->expr label.expr)))
                   ((when label.range?)
                    (reterr (msg "Unsupported case range ~x0."
                                 (label-fix label)))))
                (retok (c::label-cas expr)))
     :default (retok (c::label-default))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines ldm-stmts/blocks
  :short "Map statements and blocks to
          statements and blocks in the language definition."

  (define ldm-stmt ((stmt stmtp))
    :guard (stmt-unambp stmt)
    :returns (mv erp (stmt1 c::stmtp))
    :parents (mapping-to-language-definition ldm-stmts/blocks)
    :short "Map a statement to a statement in the language definition."
    (b* (((reterr) (c::stmt-null)))
      (stmt-case
       stmt
       :labeled (b* (((erp label1) (ldm-label stmt.label))
                     ((erp stmt1) (ldm-stmt stmt.stmt)))
                  (retok (c::make-stmt-labeled :label label1 :body stmt1)))
       :compound (b* (((erp items1) (ldm-block-item-list stmt.items)))
                   (retok (c::make-stmt-compound :items items1)))
       :expr (expr-option-case
              stmt.expr?
              :some (b* (((erp expr1) (ldm-expr stmt.expr?.val)))
                      (retok (c::stmt-expr expr1)))
              :none (retok (c::make-stmt-null)))
       :if (b* (((erp test1) (ldm-expr stmt.test))
                ((erp then1) (ldm-stmt stmt.then)))
             (retok (c::make-stmt-if :test test1 :then then1)))
       :ifelse (b* (((erp test1) (ldm-expr stmt.test))
                    ((erp then1) (ldm-stmt stmt.then))
                    ((erp else1) (ldm-stmt stmt.else)))
                 (retok (c::make-stmt-ifelse :test test1
                                             :then then1
                                             :else else1)))
       :switch (b* (((erp ctrl1) (ldm-expr stmt.target))
                    ((erp body1) (ldm-stmt stmt.body)))
                 (retok (c::make-stmt-switch :ctrl ctrl1 :body body1)))
       :while (b* (((erp test1) (ldm-expr stmt.test))
                   ((erp body1) (ldm-stmt stmt.body)))
                (retok (c::make-stmt-while :test test1 :body body1)))
       :dowhile (b* (((erp body1) (ldm-stmt stmt.body))
                     ((erp test1) (ldm-expr stmt.test)))
                  (retok (c::make-stmt-dowhile :body body1 :test test1)))
       :for-expr (b* (((erp init1) (ldm-expr-option stmt.init))
                      ((erp test1) (ldm-expr-option stmt.test))
                      ((erp next1) (ldm-expr-option stmt.next))
                      ((erp body1) (ldm-stmt stmt.body)))
                   (retok (c::make-stmt-for :init init1
                                            :test test1
                                            :next next1
                                            :body body1)))
       :for-decl (reterr (msg "Unsupported 'for' loop ~x0 ~
                               with initializing declaration."
                              (stmt-fix stmt)))
       :for-ambig (prog2$ (impossible) (reterr t))
       :goto (b* (((erp ident1) (ldm-ident stmt.label)))
               (retok (c::make-stmt-goto :target ident1)))
       :continue (retok (c::stmt-continue))
       :break (retok (c::stmt-break))
       :return (b* (((erp expr?) (ldm-expr-option stmt.expr?)))
                 (retok (c::make-stmt-return :value expr?)))
       :asm (reterr (msg "Unsupported assembler statement ~x0."
                         (stmt-fix stmt)))))
    :measure (stmt-count stmt))

  (define ldm-block-item ((item block-itemp))
    :guard (block-item-unambp item)
    :returns (mv erp (item1 c::block-itemp))
    :parents (mapping-to-language-definition ldm-stmts/blocks)
    :short "Map a block item to a block item in the language definition."
    (b* (((reterr) (c::block-item-stmt (c::stmt-null))))
      (block-item-case
       item
       :decl (b* (((erp objdeclon) (ldm-decl-obj item.decl)))
               (retok (c::block-item-declon objdeclon)))
       :stmt (b* (((erp stmt) (ldm-stmt item.stmt)))
               (retok (c::block-item-stmt stmt)))
       :ambig (prog2$ (impossible) (reterr t))))
    :measure (block-item-count item))

  (define ldm-block-item-list ((items block-item-listp))
    :guard (block-item-list-unambp items)
    :returns (mv erp (items1 c::block-item-listp))
    :parents (mapping-to-language-definition ldm-stmts/blocks)
    :short "Map a list of block items to
            a list of block items in the language definition."
    (b* (((reterr) nil)
         ((when (endp items)) (retok nil))
         ((erp item1) (ldm-block-item (car items)))
         ((erp items1) (ldm-block-item-list (cdr items))))
      (retok (cons item1 items1)))
    :measure (block-item-list-count items))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual ldm-stmts/blocks)

  (defret-mutual ldm-stmts/blocks-ok-when-stmts/blocks-formalp
    (defret ldm-stmt-ok-when-stmt-formalp
      (not erp)
      :hyp (stmt-formalp stmt)
      :fn ldm-stmt)
    (defret ldm-block-item-ok-when-block-item-formalp
      (not erp)
      :hyp (block-item-formalp item)
      :fn ldm-block-item)
    (defret ldm-block-item-list-ok-when-block-item-list-formalp
      (not erp)
      :hyp (block-item-list-formalp items)
      :fn ldm-block-item-list)
    :hints (("Goal"
             :expand (stmt-formalp stmt)
             :in-theory (enable stmt-formalp
                                block-item-formalp
                                block-item-list-formalp
                                expr-option-some->val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-fundef ((fundef fundefp))
  :guard (fundef-unambp fundef)
  :returns (mv erp (fundef1 c::fundefp))
  :short "Map a function definition to the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declaration specifiers must be all type specifiers,
     and their list must form a supported sequence.")
   (xdoc::p
    "The declarator must be a supported function declarator.")
   (xdoc::p
    "There must be no declarations (between declarator and body)."))
  (b* (((reterr) (c::fundef (c::tyspecseq-void)
                            (c::fun-declor-base (c::ident "irrelevant") nil)
                            nil))
       ((fundef fundef) fundef)
       ((mv okp tyspecs) (check-decl-spec-list-all-typespec fundef.spec))
       ((when (not okp))
        (reterr (msg "Unsupported declaration specifiers ~
                      in function definition ~x0."
                     (fundef-fix fundef))))
       ((erp tyspecseq) (ldm-type-spec-list tyspecs))
       ((erp fundeclor) (ldm-declor-fun fundef.declor))
       ((when fundef.asm?)
        (reterr (msg "Unsupported assembler name specifier ~
                      in function definition ~x0."
                     (fundef-fix fundef))))
       ((when fundef.attribs)
        (reterr (msg "Unsupported attribute specifiers ~
                      in function definition ~x0."
                     (fundef-fix fundef))))
       ((when fundef.decls)
        (reterr (msg "Unsupported declarations ~
                      in function definition ~x0."
                     (fundef-fix fundef))))
       ((erp body) (ldm-block-item-list fundef.body)))
    (retok (c::make-fundef :tyspec tyspecseq
                           :declor fundeclor
                           :body body)))
  :hooks (:fix)

  ///

  (defret ldm-fundef-ok-when-fundef-formalp
    (not erp)
    :hyp (fundef-formalp fundef)
    :hints (("Goal" :in-theory (enable fundef-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-extdecl ((extdecl extdeclp))
  :guard (extdecl-unambp extdecl)
  :returns (mv erp (extdecl1 c::ext-declonp))
  :short "Map an external declaration to
          an external declaration in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides supporting function definitions,
     we support three kinds of declarations:
     for functions, for objects, and for tags.
     We try these three mapping functions in turn,
     but instead of just propagating the errors they may return,
     we catch them and use them to try the next mapping."))
  (b* (((reterr) (c::ext-declon-fundef
                  (c::fundef (c::tyspecseq-void)
                             (c::fun-declor-base (c::ident "irrelevant") nil)
                             nil)))
       ((when (extdecl-case extdecl :empty))
        (reterr (msg "Unsupported empty external declaration.")))
       ((when (extdecl-case extdecl :asm))
        (reterr (msg "Unsupported assembler statement at the top level.")))
       ((when (extdecl-case extdecl :fundef))
        (b* (((erp fundef) (ldm-fundef (extdecl-fundef->unwrap extdecl))))
          (retok (c::ext-declon-fundef fundef))))
       (decl (extdecl-decl->unwrap extdecl))
       ((mv erp fundeclon) (ldm-decl-fun decl))
       ((when (not erp))
        (retok (c::ext-declon-fun-declon fundeclon)))
       ((mv erp objdeclon) (ldm-decl-obj decl))
       ((when (not erp))
        (retok (c::ext-declon-obj-declon objdeclon)))
       ((mv erp tagdeclon) (ldm-decl-tag decl))
       ((when (not erp))
        (retok (c::ext-declon-tag-declon tagdeclon))))
    (reterr (msg "Unsupported external declaration ~x0."
                 (extdecl-fix extdecl))))
  :hooks (:fix)

  ///

  (defret ldm-extdecl-ok-when-extdecl-formalp
    (not erp)
    :hyp (extdecl-formalp extdecl)
    :hints (("Goal" :in-theory (enable extdecl-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-extdecl-list ((extdecls extdecl-listp))
  :guard (extdecl-list-unambp extdecls)
  :returns (mv erp (extdecls1 c::ext-declon-listp))
  :short "Map a list of external declarations to the language definition."
  (b* (((reterr) nil)
       ((when (endp extdecls)) (retok nil))
       ((erp extdecl1) (ldm-extdecl (car extdecls)))
       ((erp extdecls1) (ldm-extdecl-list (cdr extdecls))))
    (retok (cons extdecl1 extdecls1)))
  :hooks (:fix)

  ///

  (defret ldm-extdecl-list-ok-when-extdecl-list-formalp
    (not erp)
    :hyp (extdecl-list-formalp extdecls)
    :hints (("Goal" :induct t :in-theory (enable extdecl-list-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-transunit ((tunit transunitp))
  :guard (transunit-unambp tunit)
  :returns (mv erp (file c::filep))
  :short "Map a translation unit to the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "A translation unit consists of a list of external declarations.
     We map all of them to the language definition (if possible),
     obtaining a corresponding list of external declaration,
     which we put into a @(tsee c::file)."))
  (b* (((reterr) (c::file nil))
       (extdecls (transunit->decls tunit))
       ((erp extdecls1) (ldm-extdecl-list extdecls)))
    (retok (c::make-file :declons extdecls1)))
  :hooks (:fix)

  ///

  (defret ldm-transunit-ok-when-transunit-formalp
    (not erp)
    :hyp (transunit-formalp tunit)
    :hints (("Goal" :in-theory (enable transunit-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-transunit-ensemble ((tunits transunit-ensemblep))
  :guard (transunit-ensemble-unambp tunits)
  :returns (mv erp (fileset c::filesetp))
  :short "Map a translation unit ensemble to the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently we only support translation unit ensembles
     consisting of a single translation unit.
     We map that to a @(tsee c::fileset)
     without header, just with a source file
     that corresponds to the translation unit.
     We set the path of the @(tsee c::fileset) to the empty string for now,
     as we are not concerned with any actual interaction with the file system.")
   (xdoc::p
    "Note that @(tsee c::fileset) is quite different from @(tsee c$::fileset).
     We plan to make the terminology more consistent."))
  (b* (((reterr) (c::fileset "" nil (c::file nil)))
       (map (transunit-ensemble->unwrap tunits))
       ((unless (= (omap::size map) 1))
        (reterr (msg "Unsupported translation unit ensemble ~
                      with ~x0 translation units."
                     (omap::size map))))
       (tunit (omap::head-val map))
       ((erp file) (ldm-transunit tunit)))
    (retok (c::make-fileset :path-wo-ext ""
                            :dot-h nil
                            :dot-c file)))
  :guard-hints (("Goal" :in-theory (enable omap::unfold-equal-size-const)))
  :hooks (:fix)

  ///

  (defret ldm-transunit-ensemble-ok-when-transunit-ensemble-formalp
    (not erp)
    :hyp (transunit-ensemble-formalp tunits)
    :hints (("Goal" :in-theory (enable transunit-ensemble-formalp)))))
