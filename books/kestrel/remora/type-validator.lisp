; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-validator")
(include-book "type-static-environments")

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-validator
  :parents (validator)
  :short "Validator of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This implements the specification in @(see type-validity)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-types
  :short "Check types and lists of types."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-type ((type typep) (ienv ispace-senvp) (tenv type-senvp))
    :returns (yes/no booleanp)
    :parents (type-validator check-types)
    :short "Check a type."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return @('t') if the check is successful, otherwise @('nil').")
     (xdoc::p
      "A variable must be in the environment.")
     (xdoc::p
      "A base type is always valid.")
     (xdoc::p
      "An array type is valid iff
       its element type is valid and atom-kinded (i.e. not an array type),
       and its ispace is valid.")
     (xdoc::p
      "A bracket type is valid iff
       its element type is valid and atom-kinded (i.e. not an array type),
       and its ispaces are valid.")
     (xdoc::p
      "The atom-kind requirement on the element type of
       an array or bracket type is the only kind constraint:
       as explained in @(tsee type),
       an atom-kinded type may otherwise be used
       wherever an array-kinded type is expected,
       being auto-lifted to a zero-rank array type.")
     (xdoc::p
      "A function type is valid iff
       its input types and its output type are all valid.")
     (xdoc::p
      "A universal type is valid iff its body is valid
       in the environment extended with the bound type variables.")
     (xdoc::p
      "A product type is valid iff its body is valid
       in the environment extended with the bound ispace variables.")
     (xdoc::p
      "A sum type is valid iff its body is valid
       in the environment extended with the bound ispace variables."))
    (type-case
     type
     :var (consp (omap::assoc type.var (type-senv->types tenv)))
     :base t
     :array (and (check-type type.elem ienv tenv)
                 (type-atom-kindp type.elem)
                 (check-ispace type.ispace ienv))
     :bracket (and (check-type type.elem ienv tenv)
                   (type-atom-kindp type.elem)
                   (check-ispace-list type.ispaces ienv))
     :fun (and (check-type type.in ienv tenv)
               (check-type type.out ienv tenv))
     :funn (and (check-type-list type.in ienv tenv)
                (check-type type.out ienv tenv))
     :forall (check-type type.body ienv (type-senv-add-var type.param tenv))
     :foralln (check-type type.body ienv (type-senv-add-vars type.params tenv))
     :pi (check-type type.body (ispace-senv-add-var type.param ienv) tenv)
     :pin (check-type type.body (ispace-senv-add-vars type.params ienv) tenv)
     :sigma (check-type type.body (ispace-senv-add-var type.param ienv) tenv)
     :sigman (check-type type.body
                         (ispace-senv-add-vars type.params ienv)
                         tenv))
    :measure (type-count type))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-type-list ((types type-listp)
                           (ienv ispace-senvp)
                           (tenv type-senvp))
    :returns (yes/no booleanp)
    :parents (type-validator check-types)
    :short "Check a list of types."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check each type in turn,
       returning @('t') iff they are all valid."))
    (or (endp types)
        (and (check-type (car types) ienv tenv)
             (check-type-list (cdr types) ienv tenv)))
    :measure (type-list-count types))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  (fty::deffixequiv-mutual check-types))
