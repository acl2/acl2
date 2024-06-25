; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-operations")

(include-book "../language/abstract-syntax")

(include-book "kestrel/std/util/error-value-tuples" :dir :system)

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
     the syntax is within the subset of the language definition."))
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
  :hooks (:fix))

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
       ((mv value base) (ldm-dec/oct/hex-const iconst.dec/oct/hex))
       ((mv length unsignedp) (ldm-isuffix-option iconst.suffix)))
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
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-tyspec-list ((tyspecs tyspec-listp))
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
       (tyspecs (tyspec-list-fix tyspecs)))
    (cond
     ((equal tyspecs (list (tyspec-void)))
      (retok (c::tyspecseq-void)))
     ((equal tyspecs (list (tyspec-char)))
      (retok (c::tyspecseq-char)))
     ((equal tyspecs (list (tyspec-signed) (tyspec-char)))
      (retok (c::tyspecseq-schar)))
     ((equal tyspecs (list (tyspec-unsigned) (tyspec-char)))
      (retok (c::tyspecseq-uchar)))
     ((equal tyspecs (list (tyspec-short)))
      (retok (c::make-tyspecseq-sshort :signed nil :int nil)))
     ((equal tyspecs (list (tyspec-signed) (tyspec-short)))
      (retok (c::make-tyspecseq-sshort :signed t :int nil)))
     ((equal tyspecs (list (tyspec-short) (tyspec-int)))
      (retok (c::make-tyspecseq-sshort :signed nil :int t)))
     ((equal tyspecs (list (tyspec-signed) (tyspec-short) (tyspec-int)))
      (retok (c::make-tyspecseq-sshort :signed t :int t)))
     ((equal tyspecs (list (tyspec-unsigned) (tyspec-short)))
      (retok (c::make-tyspecseq-ushort :int nil)))
     ((equal tyspecs (list (tyspec-unsigned) (tyspec-short) (tyspec-int)))
      (retok (c::make-tyspecseq-ushort :int t)))
     ((equal tyspecs (list (tyspec-int)))
      (retok (c::make-tyspecseq-sint :signed nil :int t)))
     ((equal tyspecs (list (tyspec-signed)))
      (retok (c::make-tyspecseq-sint :signed t :int nil)))
     ((equal tyspecs (list (tyspec-signed) (tyspec-int)))
      (retok (c::make-tyspecseq-sint :signed t :int t)))
     ((equal tyspecs (list (tyspec-unsigned)))
      (retok (c::make-tyspecseq-uint :int nil)))
     ((equal tyspecs (list (tyspec-unsigned) (tyspec-int)))
      (retok (c::make-tyspecseq-uint :int t)))
     ((equal tyspecs (list (tyspec-long)))
      (retok (c::make-tyspecseq-slong :signed nil :int nil)))
     ((equal tyspecs (list (tyspec-long) (tyspec-int)))
      (retok (c::make-tyspecseq-slong :signed nil :int t)))
     ((equal tyspecs (list (tyspec-signed) (tyspec-long)))
      (retok (c::make-tyspecseq-slong :signed t :int nil)))
     ((equal tyspecs (list (tyspec-signed) (tyspec-long) (tyspec-int)))
      (retok (c::make-tyspecseq-slong :signed t :int t)))
     ((equal tyspecs (list (tyspec-unsigned) (tyspec-long)))
      (retok (c::make-tyspecseq-ulong :int nil)))
     ((equal tyspecs (list (tyspec-unsigned) (tyspec-long) (tyspec-int)))
      (retok (c::make-tyspecseq-ulong :int t)))
     ((equal tyspecs (list (tyspec-long) (tyspec-long)))
      (retok (c::make-tyspecseq-sllong :signed nil :int nil)))
     ((equal tyspecs (list (tyspec-long) (tyspec-long) (tyspec-int)))
      (retok (c::make-tyspecseq-sllong :signed nil :int t)))
     ((equal tyspecs (list (tyspec-signed) (tyspec-long) (tyspec-long)))
      (retok (c::make-tyspecseq-sllong :signed t :int nil)))
     ((equal tyspecs
             (list (tyspec-signed) (tyspec-long) (tyspec-long) (tyspec-int)))
      (retok (c::make-tyspecseq-sllong :signed t :int t)))
     ((equal tyspecs (list (tyspec-unsigned) (tyspec-long) (tyspec-long)))
      (retok (c::make-tyspecseq-ullong :int nil)))
     ((equal tyspecs
             (list (tyspec-unsigned) (tyspec-long) (tyspec-long) (tyspec-int)))
      (retok (c::make-tyspecseq-ullong :int t)))
     ((equal tyspecs (list (tyspec-bool)))
      (retok (c::tyspecseq-bool)))
     ((equal tyspecs (list (tyspec-float)))
      (retok (c::make-tyspecseq-float :complex nil)))
     ((equal tyspecs (list (tyspec-float) (tyspec-complex)))
      (retok (c::make-tyspecseq-float :complex t)))
     ((equal tyspecs (list (tyspec-double)))
      (retok (c::make-tyspecseq-double :complex nil)))
     ((equal tyspecs (list (tyspec-double) (tyspec-complex)))
      (retok (c::make-tyspecseq-double :complex t)))
     ((equal tyspecs (list (tyspec-long) (tyspec-double)))
      (retok (c::make-tyspecseq-ldouble :complex nil)))
     ((equal tyspecs (list (tyspec-long) (tyspec-double) (tyspec-complex)))
      (retok (c::make-tyspecseq-ldouble :complex t)))
     ((and (consp tyspecs)
           (endp (cdr tyspecs))
           (tyspec-case (car tyspecs) :struct))
      (b* ((tyspec (car tyspecs))
           (ident (check-strunispec-no-members (tyspec-struct->unwrap tyspec)))
           ((when (not ident))
            (reterr (msg "Unsupported type specifier ~x0 that is ~
                          a structure specifier with members."
                         tyspec)))
           ((erp ident1) (ldm-ident ident)))
        (retok (c::make-tyspecseq-struct :tag ident1))))
     ((and (consp tyspecs)
           (endp (cdr tyspecs))
           (tyspec-case (car tyspecs) :union))
      (b* ((tyspec (car tyspecs))
           (ident (check-strunispec-no-members (tyspec-union->unwrap tyspec)))
           ((when (not ident))
            (reterr (msg "Unsupported type specifier ~x0 that is ~
                          a union specifier with members."
                         tyspec)))
           ((erp ident1) (ldm-ident ident)))
        (retok (c::make-tyspecseq-union :tag ident1))))
     ((and (consp tyspecs)
           (endp (cdr tyspecs))
           (tyspec-case (car tyspecs) :enum))
      (b* ((tyspec (car tyspecs))
           (ident (check-enumspec-no-list (tyspec-enum->unwrap tyspec)))
           ((when (not ident))
            (reterr (msg "Unsupported type specifier ~x0 that is ~
                          an enumeration specifier with enumerators."
                         tyspec)))
           ((erp ident1) (ldm-ident ident)))
        (retok (c::make-tyspecseq-enum :tag ident1))))
     ((and (consp tyspecs)
           (endp (cdr tyspecs))
           (tyspec-case (car tyspecs) :tydef))
      (b* ((tyspec (car tyspecs))
           (ident (tyspec-tydef->name tyspec))
           ((erp ident1) (ldm-ident ident)))
        (retok (c::make-tyspecseq-typedef :name ident1))))
     (t (reterr (msg "Unsupported type specifier sequence ~x0." tyspecs)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-stoclaspec-list ((stoclaspecs stoclaspec-listp))
  :returns (mv erp (scspecseq c::scspecseqp))
  :short "Map a list of storage class specifiers to
          a storage class specifier sequence in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list must be empty,
     or a singleton with the @('extern') specifier."))
  (b* (((reterr) (c::scspecseq-none))
       (stoclaspecs (stoclaspec-list-fix stoclaspecs)))
    (cond
     ((equal stoclaspecs nil)
      (retok (c::scspecseq-none)))
     ((equal stoclaspecs (list (stoclaspec-extern)))
      (retok (c::scspecseq-extern)))
     (t
      (reterr (msg "Unsupported storage class specifier sequence ~x0."
                   stoclaspecs)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-dirdeclor-obj ((dirdeclor dirdeclorp))
  :returns (mv erp (declor1 c::obj-declorp))
  :short "Map a direct declarator to
          an object declarator in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The abstract syntax in the language definition
     does not have a separate type for direct object declarators,
     so we return an object declarator here.
     The input direct declarator must be an identifier
     followed by zero or more
     square-bracketed optional integer constant expressions.
     These zero or more array declarator constructs
     are handled recursively.")
   (xdoc::p
    "This function will always result in a @(tsee c::obj-declor)
     of the @(':ident') or @(':array') kind;
     the @(':pointer') kind is generated by @(tsee ldm-declor-obj).")
   (xdoc::p
    "This function is called when we expect an object declarator,
     not a function declarator, for which we have a separate function."))
  (b* (((reterr) (c::obj-declor-ident (c::ident "irrelevant")))
       ((when (dirdeclor-case dirdeclor :ident))
        (b* ((ident (dirdeclor-ident->unwrap dirdeclor))
             ((erp ident1) (ldm-ident ident)))
          (retok (c::obj-declor-ident ident1))))
       ((when (dirdeclor-case dirdeclor :array))
        (b* (((dirdeclor-array dirdeclor) dirdeclor)
             ((erp declor1) (ldm-dirdeclor-obj dirdeclor.decl))
             ((when dirdeclor.tyquals)
              (reterr (msg "Unsupported type qualifiers ~
                            in direct declarator ~x0 for object."
                           (dirdeclor-fix dirdeclor))))
             ((when (not dirdeclor.expr?))
              (retok (c::make-obj-declor-array :decl declor1
                                               :size nil)))
             (iconst (check-expr-iconst dirdeclor.expr?))
             ((unless iconst)
              (reterr (msg "Unsupported non-integer-constant size ~
                            in direct declarator ~x0 for object."
                           (dirdeclor-fix dirdeclor))))
             (iconst1 (ldm-iconst iconst)))
          (retok (c::make-obj-declor-array :decl declor1
                                           :size iconst1)))))
    (reterr (msg "Unsupported direct declarator ~x0 for object."
                 (dirdeclor-fix dirdeclor))))
  :measure (dirdeclor-count dirdeclor)
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-declor-obj ((declor declorp))
  :returns (mv erp (declor1 c::obj-declorp))
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
       ((erp declor1) (ldm-dirdeclor-obj declor.decl)))
    (ldm-declor-obj-loop declor1 declor.pointers))
  :hooks (:fix)

  :prepwork
  ((define ldm-declor-obj-loop ((declor1 c::obj-declorp)
                                (pointers tyqual-list-listp))
     :returns (mv erp (declor2 c::obj-declorp))
     :parents nil
     (b* (((reterr) (c::obj-declor-ident (c::ident "irrelevant")))
          ((when (endp pointers)) (retok (c::obj-declor-fix declor1)))
          (tyquals (car pointers))
          ((unless (endp tyquals))
           (reterr (msg "Unsupported type qualifiers ~x0 in pointer."
                        (tyqual-list-fix tyquals))))
          ((erp declor2) (ldm-declor-obj-loop declor1 (cdr pointers))))
       (retok (c::obj-declor-pointer declor2)))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-dirabsdeclor-obj ((dirabsdeclor dirabsdeclorp))
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
       ((when dirabsdeclor.tyquals)
        (reterr (msg "Unsupported type qualifiers ~
                      in direct abstract declarator ~x0 for object."
                     (dirabsdeclor-fix dirabsdeclor))))
       ((erp iconst?)
        (if dirabsdeclor.expr?
            (b* ((iconst (check-expr-iconst dirabsdeclor.expr?)))
              (if iconst
                  (retok (ldm-iconst iconst))
                (reterr (msg "Unsupported non-integer-constant size ~
                              in direct abstract declarator ~x0 for object."
                             (dirabsdeclor-fix dirabsdeclor)))))
          (retok nil)))
       ((when (dirabsdeclor-option-case dirabsdeclor.decl? :none))
        (retok (c::make-obj-adeclor-array :decl (c::obj-adeclor-none)
                                          :size iconst?)))
       (dirabsdeclor.decl (dirabsdeclor-option-some->val dirabsdeclor.decl?))
       ((erp adeclor1) (ldm-dirabsdeclor-obj dirabsdeclor.decl)))
    (retok (c::make-obj-adeclor-array :decl adeclor1
                                      :size iconst?)))
  :measure (dirabsdeclor-count dirabsdeclor)
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-absdeclor-obj ((absdeclor absdeclorp))
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
        (if absdeclor.decl?
            (ldm-dirabsdeclor-obj absdeclor.decl?)
          (retok (c::obj-adeclor-none)))))
    (ldm-absdeclor-obj-loop adeclor1 absdeclor.pointers))
  :hooks (:fix)

  :prepwork
  ((define ldm-absdeclor-obj-loop ((adeclor1 c::obj-adeclorp)
                                   (pointers tyqual-list-listp))
     :returns (mv erp (adeclor2 c::obj-adeclorp))
     :parents nil
     (b* (((reterr) (c::obj-adeclor-none))
          ((when (endp pointers)) (retok (c::obj-adeclor-fix adeclor1)))
          (tyquals (car pointers))
          ((unless (endp tyquals))
           (reterr (msg "Unsupported type qualifiers ~x0 in pointer."
                        (tyqual-list-fix tyquals))))
          ((erp adeclor2) (ldm-absdeclor-obj-loop adeclor1 (cdr pointers))))
       (retok (c::obj-adeclor-pointer adeclor2)))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-tyname ((tyname tynamep))
  :returns (mv erp (tyname1 c::tynamep))
  :short "Map a type name to a type name in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The specifiers and qualifiers must be all type specifiers,
     and must form a supported sequence."))
  (b* (((reterr) (c::tyname (c::tyspecseq-void) (c::obj-adeclor-none)))
       ((tyname tyname) tyname)
       ((mv okp tyspecs) (check-specqual-list-all-tyspec tyname.specqual))
       ((when (not okp))
        (reterr (msg "Unsupported specifiers and qualifiers ~
                      in type name ~x0."
                     (tyname-fix tyname))))
       ((erp tyspecseq) (ldm-tyspec-list tyspecs))
       ((when (not tyname.decl?))
        (retok (c::make-tyname :tyspec tyspecseq
                               :declor (c::obj-adeclor-none))))
       ((erp adeclor1) (ldm-absdeclor-obj tyname.decl?)))
    (retok (c::make-tyname :tyspec tyspecseq
                           :declor adeclor1)))
  :hooks (:fix))

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
    :returns (mv erp (expr1 c::exprp))
    :parents (mapping-to-language-definition ldm-exprs)
    :short "Map an expression to an expression in the language definition."
    (b* (((reterr) (c::expr-ident (c::ident "irrelevant"))))
      (expr-case
       expr
       :ident (b* (((erp ident1) (ldm-ident expr.unwrap)))
                (retok (c::expr-ident ident1)))
       :const (b* (((erp const1) (ldm-const expr.unwrap)))
                (retok (c::expr-const const1)))
       :string (reterr (msg "Unsupported expression ~x0." (expr-fix expr)))
       :paren (ldm-expr expr.unwrap)
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
       :sizeof-ambig (prog2$
                      (raise "Misusage error: ambiguous expression ~x0."
                             (expr-fix expr))
                      (reterr t))
       :alignof (reterr (msg "Unsupported expression ~x0." (expr-fix expr)))
       :cast (b* (((erp tyname) (ldm-tyname expr.type))
                  ((erp arg) (ldm-expr expr.arg)))
               (retok (c::make-expr-cast :type tyname :arg arg)))
       :binary (b* (((erp arg1) (ldm-expr expr.arg1))
                    ((erp arg2) (ldm-expr expr.arg2))
                    (op (ldm-binop expr.op)))
                 (retok (c::make-expr-binary :op op :arg1 arg1 :arg2 arg2)))
       :cond (b* (((erp test) (ldm-expr expr.test))
                  ((erp then) (ldm-expr expr.then))
                  ((erp else) (ldm-expr expr.else)))
               (retok (c::make-expr-cond :test test :then then :else else)))
       :comma (reterr (msg "Unsupported expression ~x0." (expr-fix expr)))
       :cast/call-ambig (prog2$
                         (raise "Misusage error: ambiguous expression ~x0."
                                (expr-fix expr))
                         (reterr t))
       :cast/mul-ambig (prog2$
                        (raise "Misusage error: ambiguous expression ~x0."
                               (expr-fix expr))
                        (reterr t))
       :cast/add-ambig (prog2$
                        (raise "Misusage error: ambiguous expression ~x0."
                               (expr-fix expr))
                        (reterr t))
       :cast/sub-ambig (prog2$
                        (raise "Misusage error: ambiguous expression ~x0."
                               (expr-fix expr))
                        (reterr t))
       :cast/and-ambig (prog2$
                        (raise "Misusage error: ambiguous expression ~x0."
                               (expr-fix expr))
                        (reterr t))))
    :measure (expr-count expr))

  (define ldm-expr-list ((exprs expr-listp))
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

  :verify-guards nil ; done below

  ///

  (verify-guards ldm-expr)

  (fty::deffixequiv-mutual ldm-exprs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-expr-option ((expr? expr-optionp))
  :returns (mv erp (expr?1 c::expr-optionp))
  :short "Map an optional expression to
          an optional expression in the language definition."
  (b* (((reterr) nil))
    (expr-option-case
     expr?
     :some (ldm-expr expr?.val)
     :none (retok nil)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-structdecl ((structdecl structdeclp))
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
       ((when (structdecl-case structdecl :statassert))
        (reterr (msg "Unsupported structure declaration ~x0."
                     (structdecl-fix structdecl))))
       (specquals (structdecl-member->specqual structdecl))
       (declors (structdecl-member->declor structdecl))
       ((mv okp tyspecs) (check-specqual-list-all-tyspec specquals))
       ((unless okp)
        (reterr (msg "Unsupported specifier and qualifier list ~
                      in structure declaration ~x0."
                     (structdecl-fix structdecl))))
       ((erp tyspecseq) (ldm-tyspec-list tyspecs))
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
       ((erp objdeclor) (ldm-declor-obj declor.declor?)))
    (retok (c::make-struct-declon :tyspec tyspecseq :declor objdeclor)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-structdecl-list ((structdecls structdecl-listp))
  :returns (mv erp (structdecls1 c::struct-declon-listp))
  :short "Map a list of structure declarations to
          a list of structure declarations in the language definition."
  (b* (((reterr) nil)
       ((when (endp structdecls)) (retok nil))
       ((erp structdecl1) (ldm-structdecl (car structdecls)))
       ((erp structdecls1) (ldm-structdecl-list (cdr structdecls))))
    (retok (cons structdecl1 structdecls1)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-enumer ((enumer enumerp))
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
       (declspecs (decl-decl->specs decl))
       (initdeclors (decl-decl->init decl))
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
       ((unless (declspec-case declspec :tyspec))
        (reterr (msg "Unsupported declaration specifier ~x0 ~
                      for tag (i.e. structure/union/enumeration) declaration."
                     declspec)))
       (tyspec (declspec-tyspec->unwrap declspec))
       ((when (tyspec-case tyspec :struct))
        (b* (((strunispec strunispec) (tyspec-struct->unwrap tyspec))
             ((unless strunispec.name)
              (reterr (msg "Unsupported structure declaration without name.")))
             ((erp name1) (ldm-ident strunispec.name))
             ((erp members1) (ldm-structdecl-list strunispec.members)))
          (retok (c::make-tag-declon-struct :tag name1 :members members1))))
       ((when (tyspec-case tyspec :union))
        (b* (((strunispec strunispec) (tyspec-union->unwrap tyspec))
             ((unless strunispec.name)
              (reterr (msg "Unsupported union declaration without name.")))
             ((erp name1) (ldm-ident strunispec.name))
             ((erp members1) (ldm-structdecl-list strunispec.members)))
          (retok (c::make-tag-declon-union :tag name1 :members members1))))
       ((when (tyspec-case tyspec :enum))
        (b* (((enumspec enumspec) (tyspec-enum->unwrap tyspec))
             ((unless enumspec.name)
              (reterr (msg "Unsupported enumeration declaration without name.")))
             ((erp name1) (ldm-ident enumspec.name))
             ((erp idents1) (ldm-enumer-list enumspec.list)))
          (retok (c::make-tag-declon-enum :tag name1 :enumerators idents1)))))
    (reterr (msg "Unsupported type specifier ~x0 ~
                  for tag (i.e. structure/union/enumeration) declaration."
                 tyspec)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-paramdeclor ((paramdeclor paramdeclorp))
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
       ((when (paramdeclor-case paramdeclor :absdeclor))
        (reterr (msg "Unsupported parameter declarator ~x0 ~
                      with abstract declarator."
                     (paramdeclor-fix paramdeclor))))
       ((when (paramdeclor-case paramdeclor :none))
        (reterr (msg "Unsupported absent parameter declarator ~x0.")))
       (declor (paramdeclor-declor->unwrap paramdeclor)))
    (ldm-declor-obj declor))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-paramdecl ((paramdecl paramdeclp))
  :returns (mv erp (paramdecl1 c::param-declonp))
  :short "Map a parameter declaration to
          a parameter declaration in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declaration specifiers must be all type specifiers,
     and must form a supported type specifier sequence.")
   (xdoc::p
    "The parameter declarator must map to an object declarator."))
  (b* (((reterr) (c::param-declon (c::tyspecseq-void)
                                  (c::obj-declor-ident
                                   (c::ident "irrelevant"))))
       (declspecs (paramdecl->spec paramdecl))
       (declor (paramdecl->decl paramdecl))
       ((mv okp tyspecs) (check-declspec-list-all-tyspec declspecs))
       ((unless okp)
        (reterr (msg "Unsupported declaration specifier list ~
                      in parameter declaration ~x0."
                     (paramdecl-fix paramdecl))))
       ((erp tyspecseq) (ldm-tyspec-list tyspecs))
       ((erp objdeclor) (ldm-paramdeclor declor)))
    (retok (c::make-param-declon :tyspec tyspecseq :declor objdeclor)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-paramdecl-list ((paramdecls paramdecl-listp))
  :returns (mv erp (paramdecls1 c::param-declon-listp))
  :short "Map a list of parameter declarations to
          a list of parameter declarations in the language definition."
  (b* (((reterr) nil)
       ((when (endp paramdecls)) (retok nil))
       ((erp paramdecl1) (ldm-paramdecl (car paramdecls)))
       ((erp paramdecls1) (ldm-paramdecl-list (cdr paramdecls))))
    (retok (cons paramdecl1 paramdecls1)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-dirdeclor-fun ((dirdeclor dirdeclorp))
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
     followed by a single parenthesized list of parameter declarations.")
   (xdoc::p
    "This function will always result in a @(tsee c::fun-declor)
     of the @(':base') kind;
     the @(':pointer') kind is generated by @(tsee ldm-declor-fun).")
   (xdoc::p
    "This function is called when we expect a function declarator,
     not an object declarator, for which we have a separate function."))
  (b* (((reterr) (c::fun-declor-base (c::ident "irrelevant") nil))
       ((unless (dirdeclor-case dirdeclor :function-params))
        (reterr (msg "Unsupported direct declarator ~x0 for function."
                     (dirdeclor-fix dirdeclor))))
       (inner-dirdeclor (dirdeclor-function-params->decl dirdeclor))
       (params (dirdeclor-function-params->params dirdeclor))
       ((unless (dirdeclor-case inner-dirdeclor :ident))
        (reterr (msg "Unsupported direct declarator ~x0 for function."
                     (dirdeclor-fix dirdeclor))))
       (ident (dirdeclor-ident->unwrap inner-dirdeclor))
       ((erp ident1) (ldm-ident ident))
       ((erp params1) (ldm-paramdecl-list params)))
    (retok (c::make-fun-declor-base :name ident1 :params params1)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-declor-fun ((declor declorp))
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
       ((erp declor1) (ldm-dirdeclor-fun declor.decl)))
    (ldm-declor-fun-loop declor1 declor.pointers))
  :hooks (:fix)

  :prepwork
  ((define ldm-declor-fun-loop ((declor1 c::fun-declorp)
                                (pointers tyqual-list-listp))
     :returns (mv erp (declor2 c::fun-declorp))
     :parents nil
     (b* (((reterr) (c::fun-declor-base (c::ident "irrelevant") nil))
          ((when (endp pointers)) (retok (c::fun-declor-fix declor1)))
          (tyquals (car pointers))
          ((unless (endp tyquals))
           (reterr (msg "Unsupported type qualifiers ~x0 in pointer."
                        (tyqual-list-fix tyquals))))
          ((erp declor2) (ldm-declor-fun-loop declor1 (cdr pointers))))
       (retok (c::fun-declor-pointer declor2)))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-decl-fun ((decl declp))
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
       (declspecs (decl-decl->specs decl))
       (initdeclors (decl-decl->init decl))
       ((when initdeclors)
        (reterr (msg "Unsupported initialization declarators ~x0 ~
                      for function declaration."
                     initdeclors)))
       ((mv okp tyspecs) (check-declspec-list-all-tyspec declspecs))
       ((when (not okp))
        (reterr (msg "Unsupported declaration specifier list ~
                      in declaration ~x0 for function."
                     (decl-fix decl))))
       ((erp tyspecseq) (ldm-tyspec-list tyspecs))
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
       ((erp fundeclor) (ldm-declor-fun initdeclor.declor)))
    (retok (c::make-fun-declon :tyspec tyspecseq :declor fundeclor)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-desiniter ((desiniter desiniterp))
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
       ((when desiniter.design)
        (reterr (msg "Unsupported designators ~x0." desiniter.design)))
       ((unless (initer-case desiniter.init :single))
        (reterr (msg "Unsupported nested initializer ~x0." desiniter.init))))
    (ldm-expr (initer-single->expr desiniter.init)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-desiniter-list ((desiniters desiniter-listp))
  :returns (mv erp (exprs c::expr-listp))
  :short "Map a list of initializers with optional designations to
          a list of initializer expressions in the language definition."
  (b* (((reterr) nil)
       ((when (endp desiniters)) (retok nil))
       ((erp expr1) (ldm-desiniter (car desiniters)))
       ((erp exprs1) (ldm-desiniter-list (cdr desiniters))))
    (retok (cons expr1 exprs1)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-initer ((initer initerp))
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
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-decl-obj ((decl declp))
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
       (declspecs (decl-decl->specs decl))
       (initdeclors (decl-decl->init decl))
       ((mv okp tyspecs stoclaspecs)
        (check-declspec-list-all-tyspec/stoclaspec declspecs))
       ((unless okp)
        (reterr (msg "Unsupported declaration specifiers ~x0 ~
                      for object declaration."
                     declspecs)))
       ((erp tyspecseq) (ldm-tyspec-list tyspecs))
       ((erp scspecseq) (ldm-stoclaspec-list stoclaspecs))
       ((unless (and (consp initdeclors)
                     (endp (cdr initdeclors))))
        (reterr (msg "Unsupported number of initializer declarators ~x0 ~
                      for object declaration."
                     initdeclors)))
       ((initdeclor initdeclor) (car initdeclors))
       ((erp objdeclor) (ldm-declor-obj initdeclor.declor))
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
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-label ((label labelp))
  :returns (mv erp (label1 c::labelp))
  :short "Map a label to a label in the language definition."
  (b* (((reterr) (c::label-default)))
    (label-case
     label
     :name (b* (((erp ident1) (ldm-ident label.unwrap)))
             (retok (c::label-name ident1)))
     :const (b* (((erp expr1) (ldm-expr (const-expr->unwrap label.unwrap))))
              (retok (c::label-cas expr1)))
     :default (retok (c::label-default))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines ldm-stmts/blocks
  :short "Map statements and blocks to
          statements and blocks in the language definition."

  (define ldm-stmt ((stmt stmtp))
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
       :for (b* (((erp init1) (ldm-expr-option stmt.init))
                 ((erp test1) (ldm-expr-option stmt.test))
                 ((erp next1) (ldm-expr-option stmt.next))
                 ((erp body1) (ldm-stmt stmt.body)))
              (retok (c::make-stmt-for :init init1
                                       :test test1
                                       :next next1
                                       :body body1)))
       :fordecl (reterr (msg "Unsupported 'for' loop ~x0 ~
                              with initializing declaration."
                             (stmt-fix stmt)))
       :goto (b* (((erp ident1) (ldm-ident stmt.label)))
               (retok (c::make-stmt-goto :target ident1)))
       :continue (retok (c::stmt-continue))
       :break (retok (c::stmt-break))
       :return (b* (((erp expr?) (ldm-expr-option stmt.expr?)))
                 (retok (c::make-stmt-return :value expr?)))))
    :measure (stmt-count stmt))

  (define ldm-block-item ((item block-itemp))
    :returns (mv erp (item1 c::block-itemp))
    :parents (mapping-to-language-definition ldm-stmts/blocks)
    :short "Map a block item to a block item in the language definition."
    (b* (((reterr) (c::block-item-stmt (c::stmt-null))))
      (block-item-case
       item
       :decl (b* (((erp objdeclon) (ldm-decl-obj item.unwrap)))
               (retok (c::block-item-declon objdeclon)))
       :stmt (b* (((erp stmt) (ldm-stmt item.unwrap)))
               (retok (c::block-item-stmt stmt)))))
    :measure (block-item-count item))

  (define ldm-block-item-list ((items block-item-listp))
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

  :verify-guards nil ; done below

  ///

  (verify-guards ldm-stmt)

  (fty::deffixequiv-mutual ldm-stmts/blocks))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-fundef ((fundef fundefp))
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
       ((mv okp tyspecs) (check-declspec-list-all-tyspec fundef.spec))
       ((when (not okp))
        (reterr (msg "Unsupported declaration specifiers ~
                      in function definition ~x0."
                     (fundef-fix fundef))))
       ((erp tyspecseq) (ldm-tyspec-list tyspecs))
       ((erp fundeclor) (ldm-declor-fun fundef.declor))
       ((when fundef.decls)
        (reterr (msg "Unsupported declarations ~
                      in function definition ~x0."
                     (fundef-fix fundef))))
       ((erp body) (ldm-stmt fundef.body))
       ((unless (c::stmt-case body :compound))
        (reterr (msg "Unsupported non-compound statement body ~
                      in function definition ~x0."
                     (fundef-fix fundef)))))
    (retok (c::make-fundef :tyspec tyspecseq
                           :declor fundeclor
                           :body (c::stmt-compound->items body))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-extdecl ((extdecl extdeclp))
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
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-extdecl-list ((extdecls extdecl-listp))
  :returns (mv erp (extdecls1 c::ext-declon-listp))
  :short "Map a list of external declarations to the language definition."
  (b* (((reterr) nil)
       ((when (endp extdecls)) (retok nil))
       ((erp extdecl1) (ldm-extdecl (car extdecls)))
       ((erp extdecls1) (ldm-extdecl-list (cdr extdecls))))
    (retok (cons extdecl1 extdecls1)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-transunit ((tunit transunitp))
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
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-transunit-ensemble ((tunits transunit-ensemblep))
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
  :hooks (:fix))
