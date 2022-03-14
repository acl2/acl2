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
  (obj-declor-case declor
                   :ident (mv declor.get (obj-adeclor-none))
                   :pointer (mv declor.get (obj-adeclor-pointer)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-declon-to-ident+tyname ((declon param-declonp))
  :returns (mv (id identp) (tyname tynamep))
  :short "Decompose a parameter declaration into an identifier and a type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "We remove the identifier from the declarator,
     obtaining an abstract declarator,
     which we combine with the type specifier sequence
     to obtain a type name,
     which we return along with the identifier.
     In essence, we turn a parameter declaration into its name and type,
     which are somewhat mixed in the C syntax."))
  (b* (((param-declon declon) declon)
       ((mv id adeclor) (obj-declor-to-ident+adeclor declon.declor)))
    (mv id (make-tyname :tyspec declon.tyspec :declor adeclor)))
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
