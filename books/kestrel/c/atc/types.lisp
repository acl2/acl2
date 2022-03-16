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
(include-book "errors")

(include-book "std/util/defval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-types
  :parents (atc-implementation)
  :short "A model of C types for ATC."
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
    "For now we only model
     the @('void') type,
     the plain @('char') type, and
     the standard signed and unsigned integer types (except @('_Bool'),
     as well as pointer types.
     The referenced type of a pointer type may be any type (that we model),
     including a pointer type.
     The recursion bottoms out at the integer types.")
   (xdoc::p
    "This semantic model is more general
     than its syntactic counterpart @(tsee tyname):
     the latter only allows one level of pointers currently.
     In any case, initially we make a limited use of pointer types."))
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
  (:pointer ((referenced type)))
  (:array ((element type)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult type "types")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult type-list "lists of types")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-type ()
  :returns (ty typep)
  :short "An irrelevant type,
          usable as a dummy return value."
  (with-guard-checking :none (ec-call (type-fix :irrelevant)))
  ///
  (in-theory (disable (:e irr-type))))

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
    "This is a subroutine of @(tsee type-name-to-type).
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
                         (irr-type))
                  :float (prog2$
                          (raise "Internal error: ~
                                             float not supported yet.")
                          (irr-type))
                  :double (prog2$
                           (raise "Internal error: ~
                                              double not supported yet.")
                           (irr-type))
                  :ldouble (prog2$
                            (raise "Internal error: ~
                                               long double not supported yet.")
                            (irr-type))
                  :struct (prog2$
                           (raise "Internal error: ~
                                              struct ~x0 not supported yet."
                                  tyspec.tag)
                           (irr-type))
                  :union (prog2$
                          (raise "Internal error: ~
                                             union ~x0 not supported yet."
                                 tyspec.tag)
                          (irr-type))
                  :enum (prog2$
                         (raise "Internal error: ~
                                            enum ~x0 not supported yet."
                                tyspec.tag)
                         (irr-type))
                  :typedef (prog2$
                            (raise "Internal error: ~
                                               typedef ~x0 not supported yet."
                                   tyspec.name)
                            (irr-type)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-name-to-type ((tyname tynamep))
  :returns (type typep)
  :short "Turn a type name into a type."
  :long
  (xdoc::topstring
   (xdoc::p
    "A type name denotes a type [C:6.7.7/2].
     This ACL2 function returns the denoted type."))
  (type-name-to-type-aux (tyname->tyspec tyname)
                         (tyname->declor tyname))
  :hooks (:fix)

  :prepwork
  ((define type-name-to-type-aux ((tyspec tyspecseqp) (declor obj-adeclorp))
     :returns (type typep)
     :parents nil
     (obj-adeclor-case
      declor
      :none (tyspecseq-to-type tyspec)
      :pointer (type-pointer (type-name-to-type-aux tyspec declor.to))
      :array (type-array (type-name-to-type-aux tyspec declor.of)))
     :measure (obj-adeclor-count declor)
     :verify-guards :after-returns
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type-name-list-to-type-list ((x tyname-listp))
  :result-type type-listp
  :short "Lift @(tsee type-name-to-type) to lists."
  (type-name-to-type x)
  ///
  (fty::deffixequiv type-name-list-to-type-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-type-to-type-name ((type typep))
  :guard (type-integerp type)
  :returns (tyname tynamep)
  :short "Turn an integer type into a type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our model of type names does not cover all the types we model;
     specifically, our type names only have one level of pointers allowed,
     while our types allow multiple levels.
     So at the moment we cannot have a total function
     from all our types to our type names.
     For now we actually only need the mapping for integer types,
     so we define this function on integer types for now."))
  (case (type-kind type)
    (:char (make-tyname :tyspec (tyspecseq-char)
                        :declor (obj-adeclor-none)))
    (:schar (make-tyname :tyspec (tyspecseq-schar)
                         :declor (obj-adeclor-none)))
    (:uchar (make-tyname :tyspec (tyspecseq-uchar)
                         :declor (obj-adeclor-none)))
    (:sshort (make-tyname :tyspec (tyspecseq-sshort nil nil)
                          :declor (obj-adeclor-none)))
    (:ushort (make-tyname :tyspec (tyspecseq-ushort nil)
                          :declor (obj-adeclor-none)))
    (:sint (make-tyname :tyspec (tyspecseq-sint nil t)
                        :declor (obj-adeclor-none)))
    (:uint (make-tyname :tyspec (tyspecseq-uint t)
                        :declor (obj-adeclor-none)))
    (:slong (make-tyname :tyspec (tyspecseq-slong nil nil)
                         :declor (obj-adeclor-none)))
    (:ulong (make-tyname :tyspec (tyspecseq-ulong nil)
                         :declor (obj-adeclor-none)))
    (:sllong (make-tyname :tyspec (tyspecseq-sllong nil nil)
                          :declor (obj-adeclor-none)))
    (:ullong (make-tyname :tyspec (tyspecseq-ullong nil)
                          :declor (obj-adeclor-none)))
    (t (prog2$ (impossible) (irr-tyname))))
  :guard-hints (("Goal" :in-theory (enable type-integerp
                                           type-signed-integerp
                                           type-unsigned-integerp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-integer-types*
  :short "List of the supported C integer types except plain @('char')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This list is used in code that generates functions and theorems
     for different combinations of integer types."))
  (list (type-schar)
        (type-uchar)
        (type-sshort)
        (type-ushort)
        (type-sint)
        (type-uint)
        (type-slong)
        (type-ulong)
        (type-sllong)
        (type-ullong)))
