; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")

(include-book "kestrel/fty/pos-option" :dir :system)
(include-book "std/util/defprojection" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ types
  :parents (language)
  :short "A model of C types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the semantic notion of type,
     which is related to, but distinct from,
     the syntactic notion of type name [C:6.7.7].
     Specifically, different type names may denote the same type,
     if they use syntactically different but equivalent type specifier sequences
     (e.g. @('int') and @('signed int'))."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum type
  :short "Fixtype of types [C:6.2.5]."
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
     because arrays are never empty in C [C:6.2.5/20]."))
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
  :pred type-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset type-set
  :short "Fixtype of osets of types."
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
  :pred type-option-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset type-option-set
  :short "Fixtype of sets of optional types."
  :elt-type type-option
  :elementp-of-nil t
  :pred type-option-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-signed-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a signed integer type [C:6.2.5/4]."
  (and (member-eq (type-kind type)
                  '(:schar :sshort :sint :slong :sllong))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-unsigned-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an unsigned integer type [C:6.2.5/6]."
  (and (member-eq (type-kind type)
                  '(:uchar :ushort :uint :ulong :ullong))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an integer type [C:6.2.5/17]."
  (or (type-case type :char)
      (type-signed-integerp type)
      (type-unsigned-integerp type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(std::deflist type-integer-listp (x)
  :guard (type-listp x)
  (type-integerp x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-realp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a real type [C:6.2.5/18]."
  (type-integerp type)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-arithmeticp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an arithmetic type [C:6.2.5/18]."
  (type-realp type)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-scalarp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a scalar type [C:6.2.5/21]."
  (or (type-arithmeticp type)
      (type-case type :pointer))
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
     but in general it is type names that denote types (of all kidns)."))
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
    "A type name denotes a type [C:6.7.7/2].
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
      :pointer (type-pointer (tyname-to-type-aux tyspec declor.to))
      :array (if declor.size
                 (b* ((size (iconst->value declor.size)))
                   (if (= size 0)
                       (make-type-array :of (tyname-to-type-aux tyspec
                                                                declor.of)
                                        :size nil)
                     (make-type-array :of (tyname-to-type-aux tyspec
                                                              declor.of)
                                      :size size)))
               (make-type-array :of (tyname-to-type-aux tyspec
                                                        declor.of)
                                :size nil)))
     :measure (obj-adeclor-count declor)
     :verify-guards :after-returns
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type-name-list-to-type-list ((x tyname-listp))
  :result-type type-listp
  :short "Lift @(tsee tyname-to-type) to lists."
  (tyname-to-type x)
  ///
  (fty::deffixequiv type-name-list-to-type-list))
