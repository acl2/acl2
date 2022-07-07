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

(include-book "std/util/defprojection" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-operations
  :parents (abstract-syntax)
  :short "Operations on the C abstract syntax."
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
    "This abstracts an object declarator to an abstract object declarator,
     by removing the identifier and also returning it.
     See @(tsee obj-adeclor)."))
  (obj-declor-case
   declor
   :ident (mv declor.get (obj-adeclor-none))
   :pointer (b* (((mv id sub) (obj-declor-to-ident+adeclor declor.decl)))
              (mv id (make-obj-adeclor-pointer :decl sub)))
   :array (b* (((mv id sub) (obj-declor-to-ident+adeclor declor.decl)))
            (mv id (make-obj-adeclor-array :decl sub :size declor.size))))
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
   :pointer (make-obj-declor-pointer
             :decl (ident+adeclor-to-obj-declor id adeclor.decl))
   :array (make-obj-declor-array
           :decl (ident+adeclor-to-obj-declor id adeclor.decl)
           :size adeclor.size))
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

(define fun-declor-to-ident+adeclor ((declor fun-declorp))
  :returns (mv (id identp) (adeclor fun-adeclorp))
  :short "Decompose a function declarator into
          an identifier and an abstract function declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This abstracts a function declarator to an abstract function declarator,
     by removing the identifier and also returning it.
     See @(tsee fun-adeclor)."))
  (fun-declor-case
   declor
   :base (mv declor.name (fun-adeclor-base declor.params))
   :pointer (b* (((mv id sub) (fun-declor-to-ident+adeclor declor.decl)))
              (mv id (fun-adeclor-pointer sub))))
  :measure (fun-declor-count declor)
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ident+adeclor-to-fun-declor ((id identp) (adeclor fun-adeclorp))
  :returns (declor fun-declorp)
  :short "Compose an identifier and an abstract function declarator
          into a function declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse of @(tsee fun-declor-to-ident+adeclor)."))
  (fun-adeclor-case
   adeclor
   :base (make-fun-declor-base :name id :params adeclor.params)
   :pointer (make-fun-declor-pointer
             :decl (ident+adeclor-to-fun-declor id adeclor.decl)))
  :measure (fun-adeclor-count adeclor)
  :verify-guards :after-returns
  :hooks (:fix)
  ///

  (defrule ident+adeclor-to-fun-declor-of-fun-declor-to-ident+adeclor
    (b* (((mv id adeclor) (fun-declor-to-ident+adeclor declor)))
      (equal (ident+adeclor-to-fun-declor id adeclor)
             (fun-declor-fix declor)))
    :enable fun-declor-to-ident+adeclor)

  (defrule fun-declor-to-ident+adeclor-of-ident+adeclor-to-fun-declor
    (equal (fun-declor-to-ident+adeclor
            (ident+adeclor-to-fun-declor id adeclor))
           (mv (ident-fix id) (fun-adeclor-fix adeclor)))
    :enable fun-declor-to-ident+adeclor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-adeclor-to-params+declor ((declor fun-adeclorp))
  :returns (mv (params param-declon-listp)
               (declor obj-adeclorp))
  :short "Decompose an abstract function declarator into
          a list of parameter declarations and an abstract object declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The inverse of this is not well-defined for every object declarator,
     because the latter may include array declarators,
     which are not allowed in function declarators.
     We could define the inverse on object declarators
     that are restricted not to use array declarators;
     but we do not need the inverse for now."))
  (fun-adeclor-case
   declor
   :base (mv declor.params (obj-adeclor-none))
   :pointer (b* (((mv params sub) (fun-adeclor-to-params+declor declor.decl)))
              (mv params (make-obj-adeclor-pointer :decl sub))))
  :measure (fun-adeclor-count declor)
  :verify-guards :after-returns
  :hooks (:fix))

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
     and we form a type name with the latter and the type specifier sequence.")
   (xdoc::p
    "The name of this ACL2 function does not mention @('obj') explicitly,
     but the fact that it deals with object declarators
     is implicit in the fact that it returns an identifier and a type name.")
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
    "This is the inverse of @(tsee tyspec+declor-to-ident+tyname)."))
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

(define tyspec+declor-to-ident+params+tyname ((tyspec tyspecseqp)
                                              (declor fun-declorp))
  :returns (mv (id identp) (params param-declon-listp) (tyname tynamep))
  :short "Turn a type specifier sequence and a function declarator
          into an identifier,a list of parameter declarations, and a type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "We decompose the declarator into an identifier and an abstract declarator,
     and we form a type name with the latter and the type specifier sequence.")
   (xdoc::p
    "The name of this ACL2 function does not mention @('fun') explicitly,
     but the fact that it deals with object declarators
     is implicit in the fact that it returns
     an identifier, a list of parameter declarations, and a type name.")
   (xdoc::p
    "In essence, we turn (the constituents of a) declaration
     into its name and parameters and type,
     which are somewhat mixed in the C syntax.")
   (xdoc::p
    "The inverse of this is not well-defined for every type name,
     because the latter may include array declarators,
     which are not allowed in function declarators.
     We could define the inverse on type names
     that are restricted not to use array declarators;
     but we do not need the inverse for now."))
  (b* (((mv id fun-adeclor) (fun-declor-to-ident+adeclor declor))
       ((mv params obj-adeclor) (fun-adeclor-to-params+declor fun-adeclor)))
    (mv id params (make-tyname :tyspec tyspec :declor obj-adeclor)))
  :hooks (:fix))

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
  :returns (mv (id identp) (tyname tynamep) (init initerp))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef->name ((fundef fundefp))
  :returns (name identp)
  :short "Name of a function in a definition."
  (b* (((mv name &) (fun-declor-to-ident+adeclor (fundef->declor fundef))))
    name)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection fundef-list->name-list (x)
  :guard (fundef-listp x)
  :returns (names ident-listp)
  :short "Lift @(tsee fundef->name) to lists."
  (fundef->name x)
  ///
  (fty::deffixequiv fundef-list->name-list
    :args ((x fundef-listp))))
