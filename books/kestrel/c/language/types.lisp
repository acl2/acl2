; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")
(include-book "integer-formats")

(include-book "../pack")

(include-book "kestrel/fty/pos-option" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "std/util/defval" :dir :system)

(local (include-book "std/lists/butlast" :dir :system))
(local (include-book "std/lists/last" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ types
  :parents (language)
  :short "A model of C types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the semantic notion of type,
     which is related to, but distinct from,
     the syntactic notion of type name [C17:6.7.7].
     Specifically, different type names may denote the same type,
     if they use syntactically different but equivalent type specifier sequences
     (e.g. @('int') and @('signed int'))."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum type
  :short "Fixtype of types [C17:6.2.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model a subset of the types denoted by
     the type names that we currently model;
     see @(tsee tyspecseq), @(tsee obj-adeclor), and @(tsee tyname).
     In essence, this fixtype combines
     a subset of the cases of @(tsee tyspecseq)
     (abstracting away the flags that model different syntactic variants),
     with the recursive structure of @(tsee obj-adeclor).")
   (xdoc::p
    "For array sizes, we use optional positive integers.
     The size is absent for an array type of unspecified size.
     If present, the size must not be 0 (this is why we use positive integers),
     because arrays are never empty in C [C17:6.2.5/20]."))
  (:void ())
  (:char ())
  (:schar ())
  (:uchar ())
  (:sshort ())
  (:ushort ())
  (:sint ())
  (:uint ())
  (:slong ())
  (:ulong ())
  (:sllong ())
  (:ullong ())
  (:struct ((tag ident)))
  (:pointer ((to type)))
  (:array ((of type)
           (size pos-option)))
  :pred typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist type-list
  :short "Fixtype of lists of types."
  :elt-type type
  :true-listp t
  :elementp-of-nil nil
  :pred type-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset type-set
  :short "Fixtype of sets of types."
  :elt-type type
  :elementp-of-nil nil
  :pred type-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption type-option
  type
  :short "Fixtype of optional types."
  :pred type-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist type-option-list
  :short "Fixtype of lists of optional types."
  :elt-type type-option
  :true-listp t
  :elementp-of-nil t
  :pred type-option-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset type-option-set
  :short "Fixtype of sets of optional types."
  :elt-type type-option
  :elementp-of-nil t
  :pred type-option-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist symbol-type-alist
  :short "Fixtype of alists from symbols to types."
  :key-type symbol
  :val-type type
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  :pred symbol-type-alistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-result
  :short "Fixtype of errors and types."
  :ok type
  :pred type-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-list-result
  :short "Fixtype of errors and lists of types."
  :ok type-list
  :pred type-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod member-type
  :short "Fixtype of member types."
  :long
  (xdoc::topstring
   (xdoc::p
    "These contain information about
     the members of structure and union types [C17:6.7.2.1].
     This information consists of a name and a type, for each member.
     We do not capture bit fields (including anonymous ones)
     and we do not capture static assertions.
     The information we capture mirrors @(tsee struct-declon).")
   (xdoc::p
    "We call these `member types' because they are
     the static counterpart of the member values
     captured by @(tsee member-value)."))
  ((name ident)
   (type type))
  :tag :member-type
  :pred member-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist member-type-list
  :short "Fixtype of lists of member types."
  :elt-type member-type
  :true-listp t
  :elementp-of-nil nil
  :pred member-type-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection member-type-list->name-list (x)
  :guard (member-type-listp x)
  :returns (names ident-listp)
  :short "Lift @(tsee member-type->name) to lists."
  (member-type->name x)
  ///
  (fty::deffixequiv member-type-list->name-list
    :args ((x member-type-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum member-type-list-option
  :short "Fixtype of optional lists of member types."
  (:some ((val member-type-list)))
  (:none ())
  :pred member-type-list-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult member-type-list-result
  :short "Fixtype of errors and lists of member types."
  :ok member-type-list
  :pred member-type-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define member-type-lookup ((name identp) (members member-type-listp))
  :returns (type type-optionp)
  :short "Look up a member by name in a list of member types."
  :long
  (xdoc::topstring
   (xdoc::p
    "We search from the beginning and stop at the first hit;
     since the names are unique in well-formed lists,
     the exact search strategy makes no difference
     We return the type of the member if the search is successful.
     We return @('nil') if the search is unsuccessful."))
  (b* (((when (endp members)) nil)
       ((when (equal (ident-fix name)
                     (member-type->name (car members))))
        (member-type->type (car members))))
    (member-type-lookup name (cdr members)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define member-type-add-first ((name identp)
                               (type typep)
                               (members member-type-listp))
  :returns (new-members member-type-list-optionp)
  :short "Add a member type at the beginning of a list of member types."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that a member with the same name is not already in the list,
     to maintain the well-formedness of the list."))
  (b* ((found (member-type-lookup name members))
       ((when found) (member-type-list-option-none)))
    (member-type-list-option-some
     (cons (make-member-type :name name :type type)
           members)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define member-type-add-last ((name identp)
                              (type typep)
                              (members member-type-listp))
  :returns (new-members member-type-list-optionp)
  :short "Add a member at the end of a list of member types."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that a member with the same name is not already in the list,
     to maintain the well-formedness of the list."))
  (b* ((found (member-type-lookup name members))
       ((when found) (member-type-list-option-none)))
    (member-type-list-option-some
     (rcons (make-member-type :name name :type type)
            members)))
  :guard-hints (("Goal" :in-theory (enable rcons)))
  ///
  (fty::deffixequiv member-type-add-last
    :hints (("Goal" :in-theory (enable rcons)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum init-type
  :short "Fixtype of initializer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a notion of types for "
    (xdoc::seetopic "initer" "initializers")
    ". An initializer type has the same structure as an initializer,
     but expressions are replaced with (their) types.")
   (xdoc::p
    "As our model of initializers is extended,
     our model of initializer types will be extended accordingly."))
  (:single ((get type)))
  (:list ((get type-list)))
  :pred init-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult init-type-result
  :short "Fixtype of errors and initializer types."
  :ok init-type
  :pred init-type-resultp
  :prepwork ((local (in-theory (enable init-type-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-signed-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a signed integer type [C17:6.2.5/4]."
  (and (member-eq (type-kind type)
                  '(:schar :sshort :sint :slong :sllong))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-unsigned-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an unsigned integer type [C17:6.2.5/6]."
  (and (member-eq (type-kind type)
                  '(:uchar :ushort :uint :ulong :ullong))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an integer type [C17:6.2.5/17]."
  (or (type-case type :char)
      (type-signed-integerp type)
      (type-unsigned-integerp type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(std::deflist type-integer-listp (x)
  :guard (type-listp x)
  :short "Check if a list of types consists of all integer types."
  (type-integerp x)
  ///
  (fty::deffixequiv type-integer-listp
    :args ((x type-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-realp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a real type [C17:6.2.5/18]."
  (type-integerp type)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-arithmeticp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an arithmetic type [C17:6.2.5/18]."
  (type-realp type)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(std::deflist type-arithmetic-listp (x)
  :guard (type-listp x)
  :short "Check if a list of types consists of all arithmetic types."
  (type-arithmeticp x)
  ///
  (fty::deffixequiv type-arithmetic-listp
    :args ((x type-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-scalarp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a scalar type [C17:6.2.5/21]."
  (or (type-arithmeticp type)
      (type-case type :pointer))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-promoted-arithmeticp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a promoted arithmetic type."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, an arithmetic type that is promoted,
     in the sense that applying integer promotions [C17:6.3.1.1/2] to it
     would leave the type unchanged.
     This means that the type is not
     a (signed, unsigned, or plain) @('char') type
     or a (signed or unsigned) @('short') type."))
  (and (type-arithmeticp type)
       (not (type-case type :char))
       (not (type-case type :schar))
       (not (type-case type :uchar))
       (not (type-case type :sshort))
       (not (type-case type :ushort)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-nonchar-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a (supported) type is an integer type
          except for the plain @('char') type."
  (or (type-case type :uchar)
      (type-case type :schar)
      (type-case type :ushort)
      (type-case type :sshort)
      (type-case type :uint)
      (type-case type :sint)
      (type-case type :ulong)
      (type-case type :slong)
      (type-case type :ullong)
      (type-case type :sllong))
  :hooks (:fix)
  ///

  (defrule type-integerp-when-type-nonchar-integerp
    (implies (type-nonchar-integerp x)
             (type-integerp x))
    :enable (type-integerp
             type-unsigned-integerp
             type-signed-integerp)))

;;;;;;;;;;;;;;;;;;;;

(std::deflist type-nonchar-integer-listp (x)
  :guard (type-listp x)
  :short "Check if a list of types consists of
          all integer types except the plain @('char') type."
  (type-nonchar-integerp x)
  ///
  (fty::deffixequiv type-nonchar-integer-listp
    :args ((x type-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-completep ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is complete [C17:6.2.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A type is complete when its size is determined,
     otherwise it is incomplete.
     While [C17:6.2.5] cautions that the same type
     may be complete or incomplete in different parts of a program,
     for now we capture the completeness of a type
     independently from where it occurs:
     this is adequate for our C subset and for our use of this predicate.")
   (xdoc::p
    "The @('void') type is never complete [C17:6.2.5/19].
     The basic types, which are the integer types in our subset of C,
     are always complete [C17:6.2.5/14].
     A structure type is complete as soon as its declaration ends [C17:6.7.2.1/8];
     it is incomplete inside the structure type,
     but we do not use this predicate for the member types.
     A pointer type is always complete [C17:6.2.5/20]
     (regardless of the pointed-to type).
     An array type needs its element type to be complete [C17:6.2.5/20],
     as formalized in @(tsee check-tyname);
     the array type itself is complete if the size is specified,
     otherwise it is incomplete [C17:6.2.5/22]."))
  (cond ((type-case type :void) nil)
        ((type-integerp type) t)
        ((type-case type :struct) t)
        ((type-case type :pointer) t)
        ((type-case type :array) (not (eq (type-array->size type) nil)))
        (t (impossible)))
  :guard-hints (("Goal" :in-theory (enable type-integerp
                                           type-unsigned-integerp
                                           type-signed-integerp
                                           member-equal)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tyspecseq-to-type ((tyspec tyspecseqp))
  :returns (type typep)
  :short "Turn a type specifier sequence into a type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a subroutine of @(tsee tyname-to-type), in a sense.
     A type specifier sequence already denotes a type (of certain kinds);
     but in general it is type names that denote types (of all kinds)."))
  (tyspecseq-case tyspec
                  :void (type-void)
                  :char (type-char)
                  :schar (type-schar)
                  :uchar (type-uchar)
                  :sshort (type-sshort)
                  :ushort (type-ushort)
                  :sint (type-sint)
                  :uint (type-uint)
                  :slong (type-slong)
                  :ulong (type-ulong)
                  :sllong (type-sllong)
                  :ullong (type-ullong)
                  :bool (prog2$
                         (raise "Internal error: ~
                                 _Bool not supported yet.")
                         (ec-call (type-fix :irrelevant)))
                  :float (prog2$
                          (raise "Internal error: ~
                                  float not supported yet.")
                          (ec-call (type-fix :irrelevant)))
                  :double (prog2$
                           (raise "Internal error: ~
                                   double not supported yet.")
                           (ec-call (type-fix :irrelevant)))
                  :ldouble (prog2$
                            (raise "Internal error: ~
                                    long double not supported yet.")
                            (ec-call (type-fix :irrelevant)))
                  :struct (type-struct tyspec.tag)
                  :union (prog2$
                          (raise "Internal error: ~
                                  union ~x0 not supported yet."
                                 tyspec.tag)
                          (ec-call (type-fix :irrelevant)))
                  :enum (prog2$
                         (raise "Internal error: ~
                                 enum ~x0 not supported yet."
                                tyspec.tag)
                         (ec-call (type-fix :irrelevant)))
                  :typedef (prog2$
                            (raise "Internal error: ~
                                    typedef ~x0 not supported yet."
                                   tyspec.name)
                            (ec-call (type-fix :irrelevant))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tyname-to-type ((tyname tynamep))
  :returns (type typep)
  :short "Turn a type name into a type."
  :long
  (xdoc::topstring
   (xdoc::p
    "A type name denotes a type [C17:6.7.7/2].
     This ACL2 function returns the denoted type.
     As mentioned in @(tsee type),
     a semantic type is an abstraction of a type name:
     this function reifies that abstraction.")
   (xdoc::p
    "If an array declarator in the type name has no size,
     we turn that into an array type with unspecified size.
     If the size is present (as an integer constant),
     we use its integer value as the array type size.
     If the size is present but 0,
     we cannot use that as the array type size, which must be positive;
     in this case, we return an array type of unspecified size,
     just to make this ACL2 function total,
     but when this function is used,
     other ACL2 code ensures that the integer constant is not 0.
     We may revise this treatment of an integer constant 0 as array size,
     at some point in the future."))
  (tyname-to-type-aux (tyname->tyspec tyname)
                      (tyname->declor tyname))
  :hooks (:fix)

  :prepwork
  ((define tyname-to-type-aux ((tyspec tyspecseqp) (declor obj-adeclorp))
     :returns (type typep)
     :parents nil
     (obj-adeclor-case
      declor
      :none (tyspecseq-to-type tyspec)
      :pointer (type-pointer (tyname-to-type-aux tyspec declor.decl))
      :array (if declor.size
                 (b* ((size (iconst->value declor.size)))
                   (if (= size 0)
                       (make-type-array :of (tyname-to-type-aux tyspec
                                                                declor.decl)
                                        :size nil)
                     (make-type-array :of (tyname-to-type-aux tyspec
                                                              declor.decl)
                                      :size size)))
               (make-type-array :of (tyname-to-type-aux tyspec
                                                        declor.decl)
                                :size nil)))
     :measure (obj-adeclor-count declor)
     :hints (("Goal" :in-theory (enable o< o-finp o-p)))
     :verify-guards :after-returns
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type-name-list-to-type-list ((x tyname-listp))
  :result-type type-listp
  :short "Lift @(tsee tyname-to-type) to lists."
  (tyname-to-type x)
  ///
  (fty::deffixequiv type-name-list-to-type-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *nonchar-integer-types*
  :short "List of the (supported) C integer types except plain @('char')."
  (list (type-schar)
        (type-uchar)
        (type-sshort)
        (type-ushort)
        (type-sint)
        (type-uint)
        (type-slong)
        (type-ulong)
        (type-sllong)
        (type-ullong))
  ///

  (defruled member-nonchar-integer-types-as-pred
    (implies (typep type)
             (iff (member-equal type *nonchar-integer-types*)
                  (type-nonchar-integerp type)))
    :enable (type-nonchar-integerp
             type-kind
             typep
             member-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-type-xdoc-string ((type typep))
  :guard (type-integerp type)
  :returns (string stringp)
  :short "Documentation (sub)string that describes a C integer type."
  (b* ((core (case (type-kind type)
               (:char "char")
               (:schar "signed char")
               (:uchar "unsigned char")
               (:sshort "signed short")
               (:ushort "unsigned short")
               (:sint "signed int")
               (:uint "unsigned int")
               (:slong "signed long")
               (:ulong "unsigned long")
               (:sllong "signed long long")
               (:ullong "unsigned long long")
               (t (prog2$ (impossible) "")))))
    (str::cat "type @('" core "')"))
  :guard-hints (("Goal" :in-theory (enable type-integerp
                                           type-unsigned-integerp
                                           type-signed-integerp
                                           member-equal)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Matt K. mod, summer 2023 when removing good-atom-listp: The following local
; include-book serves as a replacement.  But it is here instead of near the top
; of this book, because otherwise the include-book phase of certify-book was
; failing.
(local (include-book "std/typed-lists/atom-listp" :dir :system))

(define integer-type-bits-nulfun ((type typep))
  :guard (type-integerp type)
  :returns (bits symbolp)
  :short "Name of the nullary function that defines
          the size in bits of a C integer type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the name of one of the nullary functions
     introduced in @(see integer-formats).")
   (xdoc::p
    "We take the name of the kind,
     remove the initial @('s') or @('u'),
     and add @('-bits') at the end."))
  (b* ((char/short/int/long/llong
        (if (type-case type :char)
            "CHAR"
          (str::implode (cdr (str::explode (symbol-name (type-kind type))))))))
    (pack char/short/int/long/llong '-bits))
  :prepwork
  ((local (include-book "std/typed-lists/character-listp" :dir :system)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-type-bits ((type typep))
  :guard (type-integerp type)
  :returns (bits posp :rule-classes :type-prescription)
  :short "Number of bits that forms a value of a C integer type."
  (case (type-kind type)
    ((:char :schar :uchar) (char-bits))
    ((:sshort :ushort) (short-bits))
    ((:sint :uint) (int-bits))
    ((:slong :ulong) (long-bits))
    ((:sllong :ullong) (llong-bits))
    (t (prog2$ (impossible) 1)))
  :guard-hints (("Goal" :in-theory (enable type-integerp
                                           type-unsigned-integerp
                                           type-signed-integerp
                                           member-equal)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-type-minbits ((type typep))
  :guard (type-integerp type)
  :returns (minbits posp :rule-classes :type-prescription)
  :short "Minimum number of bits that forms a value of a C integer type."
  (case (type-kind type)
    ((:char :schar :uchar) 8)
    ((:sshort :ushort) 16)
    ((:sint :uint) 16)
    ((:slong :ulong) 32)
    ((:sllong :ullong) 64)
    (t (prog2$ (impossible) 1)))
  :guard-hints (("Goal" :in-theory (enable type-integerp
                                           type-unsigned-integerp
                                           type-signed-integerp
                                           member-equal)))
  :hooks (:fix))
