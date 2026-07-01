; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "types")

(include-book "abstract-syntax-operations")

(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ types-to-tynames
  :parents (validation)
  :short "Conversion of validator @(see types) to abstract syntax type names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The validator @(tsee type) fixtype models C types semantically,
     in a form that is convenient for validation but not directly printable.
     Here we provide @(tsee type-to-tyname),
     which turns a (representable) @(tsee type)
     into a type name (@(tsee tyname)) in the abstract syntax.
     The resulting type name can be printed by the @(see printer),
     e.g. in error or warning messages.")
   (xdoc::p
    "Not every @(tsee type) has a source-level representation as a type name.
     The collective enumeration type (@(':enum')) carries no tag,
     and the various @('unknown') types are artifacts of our approximation.
     For these, @(tsee type-to-tyname) returns an error.")
   (xdoc::p
    "When a type is representable,
     we pick one particular type name for it,
     out of the possibly several equivalent ones.
     For instance, the type @('(type-slong)') is rendered as @('long int'),
     even though @('long') alone would also denote it."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pos-to-size-expr ((size posp) (ienv ienvp))
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (expr exprp))
  :short "Build an expression denoting an array size from a positive integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee nat-to-iconst) to build the integer constant,
     which adds a length (and possibly unsigned) suffix if needed
     for the size to be representable.
     This needs an implementation environment.
     If the size is too large to be represented by any integer type,
     @(tsee nat-to-iconst) returns @('nil'), and we return an error."))
  (b* (((reterr) (irr-expr))
       (iconst? (nat-to-iconst (pos-fix size) ienv))
       ((unless iconst?) (reterr t)))
    (retok (make-expr-const :const (const-int iconst?)
                            :info nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines push-pointer
  :short "Push a pointer layer onto an abstract declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The outermost type constructor sits at the innermost (deepest) position
     of a C declarator, so this descends to the base of the declarator
     and inserts the new pointer there.")
   (xdoc::p
    "Pointers are prefixes, while arrays and functions are postfixes,
     and the latter bind more tightly.
     So a pointer pushed below an existing postfix must be parenthesized
     (e.g. @('int (*)[3]') for a pointer to an array),
     while pointers at the top level, or nested directly under other pointers,
     are collected into the @('pointers') list of an abstract declarator
     (e.g. @('int **'))."))

  (define push-pointer-absdeclor ((absdeclor absdeclorp))
    :returns (new-absdeclor absdeclorp)
    (b* (((absdeclor absdeclor) absdeclor))
      (if (dirabsdeclor-option-case absdeclor.direct? :none)
          (change-absdeclor absdeclor
                            :pointers (cons nil absdeclor.pointers))
        (change-absdeclor absdeclor
                          :direct? (push-pointer-dirabsdeclor-option
                                     absdeclor.direct?))))
    :measure (absdeclor-count absdeclor))

  (define push-pointer-dirabsdeclor-option ((dirabsdeclor? dirabsdeclor-optionp))
    :returns (new-dirabsdeclor dirabsdeclorp)
    (if (dirabsdeclor-option-case dirabsdeclor? :none)
        (dirabsdeclor-paren (make-absdeclor :pointers (list nil)
                                            :direct? nil))
      (b* ((dirabsdeclor (dirabsdeclor-option-some->val dirabsdeclor?)))
        (dirabsdeclor-case
          dirabsdeclor
          :dummy-base (dirabsdeclor-paren (make-absdeclor :pointers (list nil)
                                                          :direct? nil))
          :paren (dirabsdeclor-paren
                   (push-pointer-absdeclor dirabsdeclor.inner))
          :array (change-dirabsdeclor-array
                   dirabsdeclor
                   :declor? (push-pointer-dirabsdeclor-option
                              dirabsdeclor.declor?))
          :array-static1 (change-dirabsdeclor-array-static1
                           dirabsdeclor
                           :declor? (push-pointer-dirabsdeclor-option
                                      dirabsdeclor.declor?))
          :array-static2 (change-dirabsdeclor-array-static2
                           dirabsdeclor
                           :declor? (push-pointer-dirabsdeclor-option
                                      dirabsdeclor.declor?))
          :array-star (change-dirabsdeclor-array-star
                        dirabsdeclor
                        :declor? (push-pointer-dirabsdeclor-option
                                   dirabsdeclor.declor?))
          :function (change-dirabsdeclor-function
                      dirabsdeclor
                      :declor? (push-pointer-dirabsdeclor-option
                                 dirabsdeclor.declor?)))))
    :measure (dirabsdeclor-option-count dirabsdeclor?))

  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(define push-pointer ((declor? absdeclor-optionp))
  :returns (new-declor absdeclorp)
  :short "Push a pointer onto an optional abstract declarator."
  (if (absdeclor-option-case declor? :none)
      (make-absdeclor :pointers (list nil) :direct? nil)
    (push-pointer-absdeclor (absdeclor-option-some->val declor?))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define push-postfix-dirabsdeclor-option ((dirabsdeclor? dirabsdeclor-optionp)
                                          (post dirabsdeclorp))
  :returns (new-dirabsdeclor dirabsdeclorp)
  :short "Insert a postfix (array or function) layer
          at the base of an optional direct abstract declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('post') argument is the new postfix node,
     whose nested declarator is expected to be absent (i.e. @('nil'));
     it is placed at the deepest position of @('dirabsdeclor?')."))
  (if (dirabsdeclor-option-case dirabsdeclor? :none)
      (dirabsdeclor-fix post)
    (b* ((dirabsdeclor (dirabsdeclor-option-some->val dirabsdeclor?)))
      (dirabsdeclor-case
        dirabsdeclor
        :dummy-base (dirabsdeclor-fix post)
        :paren (dirabsdeclor-paren
                 (b* (((absdeclor inner) dirabsdeclor.inner))
                   (change-absdeclor
                     inner
                     :direct? (push-postfix-dirabsdeclor-option
                                inner.direct? post))))
        :array (change-dirabsdeclor-array
                 dirabsdeclor
                 :declor? (push-postfix-dirabsdeclor-option
                            dirabsdeclor.declor? post))
        :array-static1 (change-dirabsdeclor-array-static1
                         dirabsdeclor
                         :declor? (push-postfix-dirabsdeclor-option
                                    dirabsdeclor.declor? post))
        :array-static2 (change-dirabsdeclor-array-static2
                         dirabsdeclor
                         :declor? (push-postfix-dirabsdeclor-option
                                    dirabsdeclor.declor? post))
        :array-star (change-dirabsdeclor-array-star
                      dirabsdeclor
                      :declor? (push-postfix-dirabsdeclor-option
                                 dirabsdeclor.declor? post))
        :function (change-dirabsdeclor-function
                    dirabsdeclor
                    :declor? (push-postfix-dirabsdeclor-option
                               dirabsdeclor.declor? post)))))
  :measure (dirabsdeclor-option-count dirabsdeclor?)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(define push-postfix ((declor? absdeclor-optionp) (post dirabsdeclorp))
  :returns (new-declor absdeclorp)
  :short "Push a postfix (array or function) layer
          onto an optional abstract declarator."
  (b* ((post (dirabsdeclor-fix post)))
    (if (absdeclor-option-case declor? :none)
        (make-absdeclor :pointers nil :direct? post)
      (b* (((absdeclor absdeclor) (absdeclor-option-some->val declor?)))
        (change-absdeclor absdeclor
                          :direct? (push-postfix-dirabsdeclor-option
                                     absdeclor.direct? post))))))

;;;;;;;;;;;;;;;;;;;;

(define push-array ((declor? absdeclor-optionp) (size? expr-optionp))
  :returns (new-declor absdeclorp)
  :short "Push an array layer onto an optional abstract declarator."
  (push-postfix declor?
                (make-dirabsdeclor-array
                  :declor? nil
                  :qualspecs nil
                  :size? size?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define spec/qual-list-to-decl-spec-list ((specquals spec/qual-listp))
  :returns (declspecs decl-spec-listp)
  :short "Turn a list of specifiers and qualifiers
          into a list of declaration specifiers."
  (b* (((when (endp specquals)) nil)
       (specqual (car specquals))
       (declspec (spec/qual-case
                   specqual
                   :typespec (decl-spec-typespec specqual.spec)
                   :typequal (decl-spec-typequal specqual.qual)
                   :align (decl-spec-align specqual.spec)
                   :attrib (decl-spec-attrib specqual.spec))))
    (cons declspec (spec/qual-list-to-decl-spec-list (cdr specquals)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define absdeclor-option-to-declor ((declor? absdeclor-optionp)
                                    (ident identp))
  :returns (declor declorp)
  :short "Turn an optional abstract declarator into a concrete declarator
          with a given identifier at its base."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to build the declarators of structure or union members,
     which must name the member.
     For the non-absent case we use @(tsee absdeclor-to-declor),
     which inserts the identifier at the base of the declarator."))
  (b* ((ident (ident-fix ident)))
    (if (absdeclor-option-case declor? :none)
        (make-declor :pointers nil :direct (dirdeclor-ident ident))
      (absdeclor-to-declor (absdeclor-option-some->val declor?) ident))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-scalar-to-spec/qual-list ((type typep))
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (specquals spec/qual-listp))
  :short "Turn a non-derived arithmetic, void, or boolean type
          into a list of specifiers and qualifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This handles all the @(tsee type) cases
     that correspond to a fixed sequence of type specifiers.
     The derived types (pointers, arrays, functions),
     the structure and union types,
     and the unrepresentable types (enumerations and the unknown types)
     are handled elsewhere; for them this returns an error."))
  (b* (((reterr) nil)
       (tyspecs
        (type-case
          type
          :void (list (type-spec-void))
          :char (list (type-spec-char))
          :schar (list (type-spec-signed (keyword-uscores-none))
                       (type-spec-char))
          :uchar (list (type-spec-unsigned) (type-spec-char))
          :sshort (list (type-spec-short) (type-spec-int))
          :ushort (list (type-spec-unsigned) (type-spec-short) (type-spec-int))
          :sint (list (type-spec-int))
          :uint (list (type-spec-unsigned) (type-spec-int))
          :slong (list (type-spec-long) (type-spec-int))
          :ulong (list (type-spec-unsigned) (type-spec-long) (type-spec-int))
          :sllong (list (type-spec-long) (type-spec-long) (type-spec-int))
          :ullong (list (type-spec-unsigned)
                        (type-spec-long) (type-spec-long) (type-spec-int))
          :float (list (type-spec-float))
          :double (list (type-spec-double))
          :ldouble (list (type-spec-long) (type-spec-double))
          :floatc (list (type-spec-float) (type-spec-complex))
          :doublec (list (type-spec-double) (type-spec-complex))
          :ldoublec (list (type-spec-long)
                          (type-spec-double) (type-spec-complex))
          :bool (list (type-spec-bool))
          :otherwise nil))
       ((unless tyspecs) (reterr t)))
    (retok (spec/qual-typespec-list tyspecs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type-to-tyname-loop
  :short "Mutually recursive functions to turn a @(tsee type)
          into the constituents of a type name."

  (define type-to-spec/qual+declor ((type typep) (ienv ienvp))
    :returns (mv (erp booleanp :rule-classes :type-prescription)
                 (specquals spec/qual-listp)
                 (declor? absdeclor-optionp))
    :short "Turn a type into a specifier/qualifier list
            and an optional abstract declarator."
    (b* (((reterr) nil nil))
      (type-case
        type
        :pointer (b* (((erp specquals declor?)
                       (type-to-spec/qual+declor type.to ienv)))
                   (retok specquals (push-pointer declor?)))
        :array (b* (((erp specquals declor?)
                     (type-to-spec/qual+declor type.of ienv))
                    ((erp size?)
                     (if type.size
                         (pos-to-size-expr type.size ienv)
                       (mv nil nil))))
                 (retok specquals (push-array declor? size?)))
        :function (b* (((erp specquals declor?)
                        (type-to-spec/qual+declor type.ret ienv))
                       ((erp params ellipsis)
                        (type-params-to-param-declons type.params ienv)))
                    (retok specquals
                           (push-postfix declor?
                                         (make-dirabsdeclor-function
                                           :declor? nil
                                           :params params
                                           :ellipsis ellipsis))))
        :struct (b* (((erp spec) (type-struni-to-struni-spec
                                   (type-struct->tag/members type) ienv)))
                  (retok (list (spec/qual-typespec
                                 (make-type-spec-struct :spec spec :info nil)))
                         nil))
        :union (b* (((erp spec) (type-struni-to-struni-spec
                                  (type-union->tag/members type) ienv)))
                 (retok (list (spec/qual-typespec (type-spec-union spec)))
                        nil))
        :otherwise (b* (((erp specquals)
                         (type-scalar-to-spec/qual-list type)))
                     (retok specquals nil))))
    :measure (type-count type))

  (define type-struni-to-struni-spec ((tag/members type-struni-tag/members-p)
                                      (ienv ienvp))
    :returns (mv (erp booleanp :rule-classes :type-prescription)
                 (spec struni-specp))
    :short "Turn the tag/members of a structure or union type
            into a structure or union specifier."
    (b* (((reterr) (irr-struni-spec)))
      (type-struni-tag/members-case
        tag/members
        :tagged (retok (make-struni-spec :attribs nil
                                         :name? tag/members.tag
                                         :members nil))
        :untagged (b* (((erp members)
                        (type-struni-member-list-to-struct-declons
                          tag/members.members ienv)))
                    (retok (make-struni-spec :attribs nil
                                             :name? nil
                                             :members members)))))
    :measure (type-struni-tag/members-count tag/members))

  (define type-struni-member-list-to-struct-declons
    ((members type-struni-member-listp)
     (ienv ienvp))
    :returns (mv (erp booleanp :rule-classes :type-prescription)
                 (declons struct-declon-listp))
    :short "Turn a list of structure or union members
            into a list of structure declarations."
    (b* (((reterr) nil)
         ((when (endp members)) (retok nil))
         ((erp declon)
          (type-struni-member-to-struct-declon (car members) ienv))
         ((erp declons)
          (type-struni-member-list-to-struct-declons (cdr members) ienv)))
      (retok (cons declon declons)))
    :measure (type-struni-member-list-count members))

  (define type-struni-member-to-struct-declon ((member type-struni-member-p)
                                               (ienv ienvp))
    :returns (mv (erp booleanp :rule-classes :type-prescription)
                 (declon struct-declonp))
    :short "Turn a structure or union member
            into a structure declaration."
    (b* (((reterr) (irr-struct-declon))
         ((type-struni-member member) member)
         ((erp specquals declor?)
          (type-to-spec/qual+declor member.type ienv))
         (struct-declor
          (ident-option-case
            member.name?
            :some (make-struct-declor
                    :declor? (absdeclor-option-to-declor declor?
                                                         member.name?.val)
                    :expr? nil
                    :info nil)
            :none (make-struct-declor :declor? nil :expr? nil :info nil))))
      (retok
       (make-struct-declon-member :extension nil
                                  :specquals specquals
                                  :declors (list struct-declor)
                                  :attribs nil)))
    :measure (type-struni-member-count member))

  (define type-params-to-param-declons ((params type-params-p) (ienv ienvp))
    :returns (mv (erp booleanp :rule-classes :type-prescription)
                 (declons param-declon-listp)
                 (ellipsis booleanp :rule-classes :type-prescription))
    :short "Turn the parameters of a function type
            into a list of parameter declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "An unspecified parameter list is rendered as
       an empty parameter list, which prints as @('()').
       A prototype with no parameters is the special @('(void)') case,
       which we render with a single @('void') parameter."))
    (b* (((reterr) nil nil))
      (type-params-case
        params
        :prototype (b* (((unless params.params)
                         (retok (list (make-param-declon
                                        :specs (list (decl-spec-typespec
                                                       (type-spec-void)))
                                        :declor (param-declor-none)
                                        :attribs nil
                                        :info nil))
                                nil))
                        ((erp declons)
                         (type-list-to-param-declons params.params ienv)))
                     (retok declons params.ellipsis))
        :old-style (b* (((erp declons)
                         (type-list-to-param-declons params.params ienv)))
                     (retok declons nil))
        :unspecified (retok nil nil)))
    :measure (type-params-count params))

  (define type-list-to-param-declons ((types type-listp) (ienv ienvp))
    :returns (mv (erp booleanp :rule-classes :type-prescription)
                 (declons param-declon-listp))
    :short "Turn a list of types into a list of parameter declarations."
    (b* (((reterr) nil)
         ((when (endp types)) (retok nil))
         ((erp specquals declor?)
          (type-to-spec/qual+declor (car types) ienv))
         (param-declor
          (if (absdeclor-option-case declor? :some)
              (param-declor-abstract (absdeclor-option-some->val declor?))
            (param-declor-none)))
         (declon (make-param-declon
                   :specs (spec/qual-list-to-decl-spec-list specquals)
                   :declor param-declor
                   :attribs nil
                   :info nil))
         ((erp declons) (type-list-to-param-declons (cdr types) ienv)))
      (retok (cons declon declons)))
    :measure (type-list-count types))

  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-to-tyname ((type typep) (ienv ienvp))
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (tyname tynamep))
  :short "Turn a type into a type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "We need an implementation environment to build the integer constants
     for array sizes; see @(tsee pos-to-size-expr).")
   (xdoc::p
    "If the type has no source-level representation as a type name
     (i.e. it is an enumeration type or one of the unknown types,
     possibly nested inside a derived or aggregate type),
     this returns an error.
     An error is also returned if an array size is too large
     to be represented by any integer type."))
  (b* (((reterr) (irr-tyname))
       (type (type-fix type))
       (ienv (ienv-fix ienv))
       ((erp specquals declor?) (type-to-spec/qual+declor type ienv)))
    (retok (make-tyname :specquals specquals
                        :declor? declor?
                        :info nil))))
