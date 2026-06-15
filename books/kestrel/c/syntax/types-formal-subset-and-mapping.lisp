; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "types")

(include-book "abstract-syntax-formal-subset")
(include-book "abstract-syntax-formal-mapping-direct")

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ types-formal-subset-and-mapping
  :parents (validation)
  :short "Subset of the types that have a formal semantics,
          and mappings with the types in the language formalization."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-formalp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is supported in our formal semantics of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "By `supported' we mean that the type corresponds to
     one in the fixtype @(tsee c::type) of types in our formal semantics.
     This consists of @('void'),
     plain @('char'),
     the standard integer types except @('_Bool'),
     pointer types,
     and struct types with tags.")
   (xdoc::p
    "This predicate can be regarded as an extension of
     the collection of @('-formalp') predicates
     in @(see abstract-syntax-formal-subset)."))
  (or (and (member-eq (type-kind type)
                      '(:void
                        :char :uchar :schar
                        :ushort :sshort
                        :uint :sint
                        :ulong :slong
                        :ullong :sllong))
           t)
      (and (type-case type :pointer)
           (type-formalp (type-pointer->to type)))
      (and (type-case type :struct)
           (let ((tag/members (type-struct->tag/members type)))
             (type-struni-tag/members-case
               tag/members
               :tagged (ident-formalp tag/members.tag)
               :untagged nil)))
      (and (type-case type :array)
           (type-formalp (type-array->of type))))
  :measure (type-count type))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-option-formalp ((type? type-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional type is supported in our formal semantics of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case if the type is absent or supported."))
  (type-option-case type?
                    :some (type-formalp type?.val)
                    :none t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-set-formalp ((types type-setp))
  :returns (yes/no booleanp)
  :short "Check if all the types in a set
          are supported in our formal semantics of C."
  (or (set::emptyp (type-set-fix types))
      (and (type-formalp (set::head types))
           (type-set-formalp (set::tail types))))
  :prepwork ((local (in-theory (enable emptyp-of-type-set-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-option-set-formalp ((type?s type-option-setp))
  :returns (yes/no booleanp)
  :short "Check if all the optional types in a set
          are supported in our formal semantics of C."
  (or (set::emptyp (type-option-set-fix type?s))
      (and (type-option-formalp (set::head type?s))
           (type-option-set-formalp (set::tail type?s))))
  :prepwork ((local (in-theory (enable emptyp-of-type-option-set-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-type ((type typep))
  :returns (mv erp (type1 c::typep))
  :short "Map a type in @(tsee type) to a type in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function can be regarded as an extension of
     the collection of @('ldm-') functions
     in @(see abstract-syntax-formal-mapping-direct).
     The supported types are the same as discussed in @(tsee type-formalp)."))
  (b* (((reterr) (c::type-void)))
    (type-case
     type
     :void (retok (c::type-void))
     :char (retok (c::type-char))
     :schar (retok (c::type-schar))
     :uchar (retok (c::type-uchar))
     :sshort (retok (c::type-sshort))
     :ushort (retok (c::type-ushort))
     :sint (retok (c::type-sint))
     :uint (retok (c::type-uint))
     :slong (retok (c::type-slong))
     :ulong (retok (c::type-ulong))
     :sllong (retok (c::type-sllong))
     :ullong (retok (c::type-ullong))
     :float (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :double (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :ldouble (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :floatc (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :doublec (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :ldoublec (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :bool (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :struct (let ((tag/members (type-struct->tag/members type)))
               (type-struni-tag/members-case
                 tag/members
                 :tagged (b* (((erp tag) (ldm-ident tag/members.tag)))
                           (retok (c::type-struct tag)))
                 :untagged (reterr (msg "Type ~x0 not supported."
                                        (type-fix type)))))
     :union (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :enum (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :array (b* (((erp elty) (ldm-type type.of)))
              (retok (c::make-type-array :of elty :size type.size)))
     :pointer (b* (((erp refd-type) (ldm-type type.to)))
                (retok (c::make-type-pointer :to refd-type)))
     :function (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :unknown (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :unknown-scalar (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :unknown-arithmetic (reterr (msg "Type ~x0 not supported."
                                      (type-fix type)))))
  :measure (type-count type)
  :verify-guards :after-returns

  ///

  (defret ldm-type-when-type-formalp
    (not erp)
    :hyp (type-formalp type)
    :hints (("Goal" :induct t
                    :in-theory (enable type-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-type-option ((type? type-optionp))
  :returns (mv erp (type?1 c::type-optionp))
  :short "Map an optional type in @(tsee type-option)
          to an optional type in the language definition."
  (type-option-case type?
                    :some (ldm-type type?.val)
                    :none (mv nil nil))

  ///

  (defret ldm-type-option-when-type-option-formalp
    (not erp)
    :hyp (type-option-formalp type?)
    :hints (("Goal" :in-theory (enable type-option-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-type-set ((types type-setp))
  :returns (mv erp (types1 c::type-setp))
  :short "Map a set of types in @(tsee type-set)
          to a set of types in the language definition."
  (b* (((when (set::emptyp (type-set-fix types))) (mv nil nil))
       ((mv erp type) (ldm-type (set::head types)))
       ((when erp) (mv erp nil))
       ((mv erp types) (ldm-type-set (set::tail types)))
       ((when erp) (mv erp nil)))
    (mv nil (set::insert type types)))
  :prepwork ((local (in-theory (enable emptyp-of-type-set-fix))))
  :verify-guards :after-returns

  ///

  (defret ldm-type-set-when-type-set-formalp
    (not erp)
    :hyp (type-set-formalp types)
    :hints (("Goal" :induct t :in-theory (enable type-set-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-type-option-set ((type?s type-option-setp))
  :returns (mv erp (type?s1 c::type-option-setp))
  :short "Map a set of optional types in @(tsee type-option-set)
          to a set of optional types in the language definition."
  (b* (((when (set::emptyp (type-option-set-fix type?s))) (mv nil nil))
       ((mv erp type?) (ldm-type-option (set::head type?s)))
       ((when erp) (mv erp nil))
       ((mv erp type?s) (ldm-type-option-set (set::tail type?s)))
       ((when erp) (mv erp nil)))
    (mv nil (set::insert type? type?s)))
  :prepwork ((local (in-theory (enable emptyp-of-type-option-set-fix))))
  :verify-guards :after-returns

  ///

  (defret ldm-type-option-set-when-type-option-set-formalp
    (not erp)
    :hyp (type-option-set-formalp type?s)
    :hints (("Goal" :induct t :in-theory (enable type-option-set-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-to-value-kind ((type typep))
  :returns (kind keywordp
                 :hints (("Goal" :in-theory (enable type-kind))))
  :short "Map a type to the corresponding @(tsee c::value) kind."
  :long
  (xdoc::topstring
   (xdoc::p
    "We throw a hard error unless the type has
     a corresponding kind of values in the formal semantics.
     This function is always called when this condition is satisfied;
     the hard error signals an implementation error."))
  (if (type-formalp type)
      (type-kind type)
    (prog2$ (raise "Internal error: type ~x0 has no corresponding value kind."
                   (type-fix type))
            :irrelevant))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-type ((ctype c::typep))
  :returns (type typep)
  :short "Map a type in the language formalization to a type in @(tsee type)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse of @(tsee ldm-type),
     hence the @('i') for `inverse'.")
   (xdoc::p
    "Since our current type system is approximate (see @(tsee type)),
     this mapping abstracts away information in some cases."))
  (c::type-case
   ctype
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
   ;; TODO: we can't really create a struct, unless we wanted to invent a UID
   ;; and tunit. Then, we could perhaps create an incomplete struct type.
   :struct (irr-type)
   :pointer (make-type-pointer :to (ildm-type ctype.to))
   :array (make-type-array :of (ildm-type ctype.of) :size ctype.size))
  :measure (c::type-count ctype)
  :verify-guards :after-returns)
