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

(include-book "../language/types")
(include-book "../language/abstract-syntax-operations")
(include-book "../language/integer-ranges")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-types
  :parents (atc-implementation)
  :short "C types for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "ATC uses the "
    (xdoc::seetopic "types" "model of C types")
    " from the language formalization for various purposes."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-type ()
  :returns (ty typep)
  :short "An irrelevant type,
          usable as a dummy return value."
  (with-guard-checking :none (ec-call (type-fix :irrelevant)))
  ///
  (in-theory (disable (:e irr-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-to-maker ((type typep))
  :returns (term "A term.")
  :short "Turn a type into a term that makes (evaluates to) it."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is somewhat meta."))
  (type-case
   type
   :void '(type-void)
   :char '(type-char)
   :schar '(type-schar)
   :uchar '(type-uchar)
   :sshort '(type-sshort)
   :ushort '(type-ushort)
   :sint '(type-sint)
   :uint '(type-uint)
   :slong '(type-slong)
   :ulong '(type-ulong)
   :sllong '(type-sllong)
   :ullong '(type-ullong)
   :struct `(type-struct (ident ,(ident->name (type-struct->tag type))))
   :pointer `(make-type-pointer :to ,(type-to-maker (type-pointer->to type)))
   :array `(make-type-array :of ,(type-to-maker (type-array->of type))
                            :size ,(type-array->size type)))
  :measure (type-count type)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define positive-to-iconst ((pos posp))
  :returns (iconst iconstp)
  :short "Turn a positive integer into an integer constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "We always generate a decimal constant
     of the smallest type that can represent it.
     We cause an internal error if the integer is too large
     even for @('unsigned long long').
     This is never expected to happen,
     given expected invariants that hold when this function is called."))
  (cond ((<= pos (sint-max)) (make-iconst :value pos
                                          :base (iconst-base-dec)
                                          :unsignedp nil
                                          :length (iconst-length-none)))
        ((<= pos (uint-max)) (make-iconst :value pos
                                          :base (iconst-base-dec)
                                          :unsignedp t
                                          :length (iconst-length-none)))
        ((<= pos (slong-max)) (make-iconst :value pos
                                           :base (iconst-base-dec)
                                           :unsignedp nil
                                           :length (iconst-length-long)))
        ((<= pos (ulong-max)) (make-iconst :value pos
                                           :base (iconst-base-dec)
                                           :unsignedp t
                                           :length (iconst-length-long)))
        ((<= pos (sllong-max)) (make-iconst :value pos
                                            :base (iconst-base-dec)
                                            :unsignedp nil
                                            :length (iconst-length-llong)))
        ((<= pos (ullong-max)) (make-iconst :value pos
                                            :base (iconst-base-dec)
                                            :unsignedp t
                                            :length (iconst-length-llong)))
        (t (prog2$
            (raise "Internal error: ~x0 too large." pos)
            (ec-call (iconst-fix :irrelevant))))))

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
                 (mv tyspec (make-obj-adeclor-pointer :decl declor)))
      :array (b* (((mv tyspec declor) (type-to-tyname-aux type.of))
                  (size (if type.size
                            (positive-to-iconst type.size)
                          nil)))
               (mv tyspec (make-obj-adeclor-array :decl declor
                                                  :size size))))
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
