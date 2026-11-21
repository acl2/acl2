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

(local (in-theory (enable typep-when-result-not-error
                          type-listp-when-result-not-error)))

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
    :returns (new-type type-resultp)
    :parents (type-validator check-types)
    :short "Check a type."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the check is successful, we return a type; otherwise, an error.
       For now, the returned type is always the same as the input type;
       but we plan to extend this function
       to lift atom-kinded types to scalar types (see @(tsee type))
       where array-kinded types are needed,
       so that the returned type makes that lifting explicit.")
     (xdoc::p
      "A variable must be in the environment.")
     (xdoc::p
      "A base type is always valid.")
     (xdoc::p
      "A scalar type is valid iff
       its element type is valid and atom-kinded (i.e. not an array type).")
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
       a scalar, array, or bracket type is the only kind constraint:
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
     :var (b* (((unless (consp (omap::assoc type.var (type-senv->types tenv))))
                (reserr nil)))
            (type-fix type))
     :base (type-fix type)
     :scalar (b* (((ok elem) (check-type type.elem ienv tenv))
                  ((unless (type-atom-kindp type.elem)) (reserr nil)))
               (type-scalar elem))
     :array (b* (((ok elem) (check-type type.elem ienv tenv))
                 ((unless (type-atom-kindp type.elem)) (reserr nil))
                 ((unless (check-ispace type.ispace ienv)) (reserr nil)))
              (make-type-array :elem elem :ispace type.ispace))
     :bracket (b* (((ok elem) (check-type type.elem ienv tenv))
                   ((unless (type-atom-kindp type.elem)) (reserr nil))
                   ((unless (check-ispace-list type.ispaces ienv))
                    (reserr nil)))
                (make-type-bracket :elem elem :ispaces type.ispaces))
     :fun (b* (((ok in) (check-type type.in ienv tenv))
               ((ok out) (check-type type.out ienv tenv)))
            (make-type-fun :in in :out out))
     :funn (b* (((ok in) (check-type-list type.in ienv tenv))
                ((ok out) (check-type type.out ienv tenv)))
             (make-type-funn :in in :out out))
     :forall (b* ((tenv (type-senv-add-var type.param tenv))
                  ((ok body) (check-type type.body ienv tenv)))
               (make-type-forall :param type.param :body body))
     :foralln (b* ((tenv (type-senv-add-vars type.params tenv))
                   ((ok body) (check-type type.body ienv tenv)))
                (make-type-foralln :params type.params :body body))
     :pi (b* ((ienv (ispace-senv-add-var type.param ienv))
              ((ok body) (check-type type.body ienv tenv)))
           (make-type-pi :param type.param :body body))
     :pin (b* ((ienv (ispace-senv-add-vars type.params ienv))
               ((ok body) (check-type type.body ienv tenv)))
            (make-type-pin :params type.params :body body))
     :sigma (b* ((ienv (ispace-senv-add-var type.param ienv))
                 ((ok body) (check-type type.body ienv tenv)))
              (make-type-sigma :param type.param :body body))
     :sigman (b* ((ienv (ispace-senv-add-vars type.params ienv))
                  ((ok body) (check-type type.body ienv tenv)))
               (make-type-sigman :params type.params :body body)))
    :measure (type-count type))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-type-list ((types type-listp)
                           (ienv ispace-senvp)
                           (tenv type-senvp))
    :returns (new-types type-list-resultp)
    :parents (type-validator check-types)
    :short "Check a list of types."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check each type in turn.
       If all the checks are successful,
       we return the resulting types, in the same order;
       otherwise, we return an error."))
    (b* (((when (endp types)) nil)
         ((ok type) (check-type (car types) ienv tenv))
         ((ok types) (check-type-list (cdr types) ienv tenv)))
      (cons type types))
    :measure (type-list-count types))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual check-types))
