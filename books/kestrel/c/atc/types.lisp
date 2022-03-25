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

(include-book "abstract-syntax-operations")
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
    "We model a subset of the types denoted by
     the type names that we currently model;
     see @(tsee tyspecseq), @(tsee obj-adeclor), and @(tsee tyname).
     In essence, this fixtype combines
     a subset of the cases of @(tsee tyspecseq)
     (abstracting away the flags that model different syntactic variants),
     with the recursive structure of @(tsee obj-adeclor)."))
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
  (:array ((of type)))
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
    "This is a subroutine of @(tsee tyname-to-type).
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
                  :struct (type-struct tyspec.tag)
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
     this function reifies that abstraction."))
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
      :array (type-array (tyname-to-type-aux tyspec declor.of)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-to-tyname ((type typep))
  :returns (tyname tynamep)
  :short "Turn a type into a type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pick a particular choice of type specifier sequence,
     and thus of type name, for each integer type."))
  (b* (((mv tyspec declor) (type-to-tyname-aux type)))
    (make-tyname :tyspec tyspec :declor declor))
  :hooks (:fix)

  :prepwork
  ((define type-to-tyname-aux ((type typep))
     :returns (mv (tyspec tyspecseqp) (declor obj-adeclorp))
     :parents nil
     (type-case
      type
      :void (mv (tyspecseq-void) (obj-adeclor-none))
      :char (mv (tyspecseq-char) (obj-adeclor-none))
      :schar (mv (tyspecseq-schar) (obj-adeclor-none))
      :uchar (mv (tyspecseq-uchar) (obj-adeclor-none))
      :sshort (mv (tyspecseq-sshort nil nil) (obj-adeclor-none))
      :ushort (mv (tyspecseq-ushort nil) (obj-adeclor-none))
      :sint (mv (tyspecseq-sint nil t) (obj-adeclor-none))
      :uint (mv (tyspecseq-uint t) (obj-adeclor-none))
      :slong (mv (tyspecseq-slong nil nil) (obj-adeclor-none))
      :ulong (mv (tyspecseq-ulong nil) (obj-adeclor-none))
      :sllong (mv (tyspecseq-sllong nil nil) (obj-adeclor-none))
      :ullong (mv (tyspecseq-ullong nil) (obj-adeclor-none))
      :struct (mv (tyspecseq-struct type.tag) (obj-adeclor-none))
      :pointer (b* (((mv tyspec declor) (type-to-tyname-aux type.to)))
                 (mv tyspec (obj-adeclor-pointer declor)))
      :array (b* (((mv tyspec declor) (type-to-tyname-aux type.of)))
               (mv tyspec (obj-adeclor-array declor))))
     :measure (type-count type)
     :verify-guards :after-returns
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ident+type-to-tyspec+declor ((id identp) (type typep))
  :returns (mv (tyspec tyspecseqp) (declor obj-declorp))
  :short "Turn an identifier and a type into
          a type specifier sequence and an object declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function provides the consituents to construct
     a declaration of an identifier with a given type.
     The type specifier sequence and the object declarator
     can be used to construct various kinds of declarations
     (see our C abstract syntax).")
   (xdoc::p
    "Note that we pick a specific type specifier sequence for each type,
     out of possibly multiple ones possible,
     via the use of @(tsee type-to-tyname)."))
  (ident+tyname-to-tyspec+declor id (type-to-tyname type))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-type-predicate ((type typep))
  :returns (pred symbolp)
  :short "ACL2 predicate corresponding to a C type."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a supported integer type,
     the predicate is the recognizer of values of that type.
     For a pointer to integer type,
     the predicate is the recognizer of arrays with that element type.
     (So for a pointer type it is not a recognizer of pointer values.)
     We return @('nil') for other types."))
  (type-case
   type
   :void nil
   :char nil
   :schar 'scharp
   :uchar 'ucharp
   :sshort 'sshortp
   :ushort 'ushortp
   :sint 'sintp
   :uint 'uintp
   :slong 'slongp
   :ulong 'ulongp
   :sllong 'sllongp
   :ullong 'ullongp
   :struct nil
   :pointer (type-case
             type.to
             :void nil
             :char nil
             :schar 'schar-arrayp
             :uchar 'uchar-arrayp
             :sshort 'sshort-arrayp
             :ushort 'ushort-arrayp
             :sint 'sint-arrayp
             :uint 'uint-arrayp
             :slong 'slong-arrayp
             :ulong 'ulong-arrayp
             :sllong 'sllong-arrayp
             :ullong 'ullong-arrayp
             :struct nil
             :pointer nil
             :array nil)
   :array nil)
  :hooks (:fix))
