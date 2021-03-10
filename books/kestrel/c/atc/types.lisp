; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")
(include-book "errors")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ types
  :parents (atc-implementation)
  :short "C types."
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
    "For now we only model the plain @('char') type and
     the standard signed and unsigned integer types,
     as well as pointer types.
     The referenced type of a pointer type may be any type (that we model),
     including a pointer type.
     The recursion bottoms out at the @('char') and standard integer types.")
   (xdoc::p
    "This semantic model is more general
     than its syntactic counterpart @(tsee tyname):
     the latter only allows one level of pointers currently.
     In any case, initially we make a limited use of pointer types."))
  (:char ())
  (:schar ())
  (:sshort ())
  (:sint ())
  (:slong ())
  (:sllong ())
  (:uchar ())
  (:ushort ())
  (:uint ())
  (:ulong ())
  (:ullong ())
  (:pointer ((referenced type)))
  :pred typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist type-list
  :short "Fixtype of lists of types."
  :elt-type type
  :true-listp t
  :elementp-of-nil nil
  :pred type-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption type-option
  type
  :short "Fixtype of optional types."
  :pred type-optionp)

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

(define type-name-to-type ((tyname tynamep))
  :returns (type typep)
  :short "Turn a type name into a type."
  :long
  (xdoc::topstring
   (xdoc::p
    "A type name denotes a type [C:6.7.7/2].
     This ACL2 function returns the denoted type."))
  (b* ((tyspecseq (tyname->specs tyname))
       (type (tyspecseq-case tyspecseq
                             :char (type-char)
                             :schar (type-schar)
                             :sshort (type-sshort)
                             :sint (type-sint)
                             :slong (type-slong)
                             :sllong (type-sllong)
                             :uchar (type-uchar)
                             :ushort (type-ushort)
                             :uint (type-uint)
                             :ulong (type-ulong)
                             :ullong (type-ullong))))
    (if (tyname->pointerp tyname)
        (type-pointer type)
      type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type-name-list-to-type-list ((x tyname-listp))
  :result-type type-listp
  :short "Lift @(tsee type-name-to-type) to lists."
  (type-name-to-type x)
  ///
  (fty::deffixequiv type-name-list-to-type-list))
