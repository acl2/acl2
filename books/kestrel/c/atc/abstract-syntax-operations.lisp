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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-abstract-syntax-operations
  :parents (atc-abstract-syntax)
  :short "Operations on the C abstract syntax for ATC."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binop-strictp ((op binopp))
  :returns (yes/no booleanp)
  :short "Check if a binary operator is strict."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the binary operators except logical conjunction and disjunction
     are strict."))
  (and (member-eq (binop-kind op)
                  (list :mul
                        :div
                        :rem
                        :add
                        :sub
                        :shl
                        :shr
                        :lt
                        :gt
                        :le
                        :ge
                        :eq
                        :ne
                        :bitand
                        :bitxor
                        :bitior
                        :asg
                        :asg-mul
                        :asg-div
                        :asg-rem
                        :asg-add
                        :asg-sub
                        :asg-shl
                        :asg-shr
                        :asg-and
                        :asg-xor
                        :asg-ior))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binop-purep ((op binopp))
  :returns (yes/no booleanp)
  :short "Check if a binary operator is pure."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the binary operators except (simple and compound) assignments
     are pure."))
  (and (member-eq (binop-kind op)
                  (list :mul
                        :div
                        :rem
                        :add
                        :sub
                        :shl
                        :shr
                        :lt
                        :gt
                        :le
                        :ge
                        :eq
                        :ne
                        :bitand
                        :bitxor
                        :bitior
                        :logand
                        :logor))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define obj-declor-to-ident+adeclor ((declor obj-declorp))
  :returns (mv (id identp) (adeclor obj-adeclorp))
  :short "Decompose an object declarator into
          an identifier and an abstract object declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This abstracts an object declarator to an abstract one,
     by removing the identifier and also returning it.
     See @(tsee obj-adeclor)."))
  (obj-declor-case
   declor
   :ident (mv declor.get (obj-adeclor-none))
   :pointer (b* (((mv id sub) (obj-declor-to-ident+adeclor declor.to)))
              (mv id (obj-adeclor-pointer sub)))
   :array (b* (((mv id sub) (obj-declor-to-ident+adeclor declor.of)))
            (mv id (obj-adeclor-array sub))))
  :measure (obj-declor-count declor)
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ident+adeclor-to-obj-declor ((id identp) (adeclor obj-adeclorp))
  :returns (declor obj-declorp)
  :short "Compose an identifier and an abstract object declarator
          into an object declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse of @(tsee obj-declor-to-ident+adeclor)."))
  (obj-adeclor-case
   adeclor
   :none (obj-declor-ident id)
   :pointer (obj-declor-pointer (ident+adeclor-to-obj-declor id adeclor.to))
   :array (obj-declor-array (ident+adeclor-to-obj-declor id adeclor.of)))
  :measure (obj-adeclor-count adeclor)
  :verify-guards :after-returns
  :hooks (:fix)
  ///

  (defrule ident+adeclor-to-obj-declor-of-obj-declor-to-ident+adeclor
    (b* (((mv id adeclor) (obj-declor-to-ident+adeclor declor)))
      (equal (ident+adeclor-to-obj-declor id adeclor)
             (obj-declor-fix declor)))
    :enable obj-declor-to-ident+adeclor)

  (defrule obj-declor-to-ident+adeclor-of-ident+adeclor-to-obj-declor
    (equal (obj-declor-to-ident+adeclor
            (ident+adeclor-to-obj-declor id adeclor))
           (mv (ident-fix id) (obj-adeclor-fix adeclor)))
    :enable obj-declor-to-ident+adeclor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tyspec+declor-to-ident+tyname ((tyspec tyspecseqp)
                                       (declor obj-declorp))
  :returns (mv (id identp) (tyname tynamep))
  :short "Turn a type specifier sequence and an object declarator
          into an identifier and a type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "We decompose the declarator into an identifier and an abstract declarator,
     and we for a type name with the latter and the type specifier sequence.")
   (xdoc::p
    "The name of this function does not mention @('obj') explicitly,
     but the fact that it deals with object declarators
     is implicit in the fact that it deals with type names.")
   (xdoc::p
    "In essence, we turn (the constituents of a) declaration
     into its name and type, which are somewhat mixed in the C syntax."))
  (b* (((mv id adeclor) (obj-declor-to-ident+adeclor declor)))
    (mv id (make-tyname :tyspec tyspec :declor adeclor)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ident+tyname-to-tyspec+declor ((id identp) (tyname tynamep))
  :returns (mv (tyspec tyspecseqp) (declor obj-declorp))
  :short "Turn an identifier and a type name
          into a type specifier sequence and an object declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "We decompose the type name into
     a type specifier sequence and an abstract object declarator,
     and we compose the latter with the identifier into an object declarator.")
   (xdoc::p
    "Given an identifier and a type (name),
     this function provides the constituents for declaring it.")
   (xdoc::p
    "This is the invers of @(tsee tyspec+declor-to-ident+tyname)."))
  (b* (((tyname tyname) tyname))
    (mv tyname.tyspec (ident+adeclor-to-obj-declor id tyname.declor)))
  :hooks (:fix)
  ///

  (defrule ident+tyname-to-tyspec+declor-of-tyspec+declor-to-ident+tyname
    (b* (((mv id tyname) (tyspec+declor-to-ident+tyname tyspec declor)))
      (equal (ident+tyname-to-tyspec+declor id tyname)
             (mv (tyspecseq-fix tyspec) (obj-declor-fix declor))))
    :enable tyspec+declor-to-ident+tyname)

  (defrule tyspec+declor-to-ident+tyname-of-ident+tyname-to-tyspec+declor
    (b* (((mv tyspec declor) (ident+tyname-to-tyspec+declor id tyname)))
      (equal (tyspec+declor-to-ident+tyname tyspec declor)
             (mv (ident-fix id) (tyname-fix tyname))))
    :enable tyspec+declor-to-ident+tyname))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-declon-to-ident+tyname ((declon struct-declonp))
  :returns (mv (id identp) (tyname tynamep))
  :short "Decompose a structure declaration into an identifier and a type name."
  (b* (((struct-declon declon) declon))
    (tyspec+declor-to-ident+tyname declon.tyspec declon.declor))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-declon-to-ident+tyname ((declon param-declonp))
  :returns (mv (id identp) (tyname tynamep))
  :short "Decompose a parameter declaration into an identifier and a type name."
  (b* (((param-declon declon) declon))
    (tyspec+declor-to-ident+tyname declon.tyspec declon.declor))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-declon-list-to-ident+tyname-lists
  ((declons param-declon-listp))
  :returns (mv (ids ident-listp) (tynames tyname-listp))
  :short "Lift @(tsee param-declon-to-ident+tyname) to lists."
  (b* (((when (endp declons)) (mv nil nil))
       ((mv id tyname) (param-declon-to-ident+tyname (car declons)))
       ((mv ids tynames) (param-declon-list-to-ident+tyname-lists
                          (cdr declons))))
    (mv (cons id ids) (cons tyname tynames)))
  :hooks (:fix)
  ///

  (defret len-of-param-declon-list-to-ident+tyname-lists.ids
    (equal (len ids)
           (len declons)))

  (defret len-of-param-declon-list-to-ident+tyname-lists.tynames
    (equal (len tynames)
           (len declons))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define obj-declon-to-ident+tyname+init ((declon obj-declonp))
  :returns (mv (id identp) (tyname tynamep) (init exprp))
  :short "Decompose an object declaration into
          an identifier, a type name, and an initializer."
  (b* (((obj-declon declon) declon)
       ((mv id tyname) (tyspec+declor-to-ident+tyname declon.tyspec
                                                      declon.declor)))
    (mv id tyname declon.init))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ext-declon-list->fundef-list ((exts ext-declon-listp))
  :returns (defs fundef-listp)
  :short "Extract from a list of external declarations
          the list of function definitions, in the same order."
  :long
  (xdoc::topstring
   (xdoc::p
    "Declarations are discarded. Only function definitions are projected."))
  (b* (((when (endp exts)) nil)
       (ext (car exts)))
    (ext-declon-case ext
                     :fundef (cons (ext-declon-fundef->get ext)
                                   (ext-declon-list->fundef-list (cdr exts)))
                     :obj-declon (ext-declon-list->fundef-list (cdr exts))
                     :tag-declon (ext-declon-list->fundef-list (cdr exts))))
  :hooks (:fix))
