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

(define type-lift-if-atom ((type typep))
  :returns (new-type typep)
  :short "Lift an atom-kinded type to a scalar type,
          leaving an array-kinded type unchanged."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used where an array-kinded type is expected,
     to make explicit the lifting of
     an atom-kinded type that stands for a scalar type
     (see @(tsee type)).
     The resulting type is always array-kinded."))
  (if (type-atom-kindp type)
      (type-scalar type)
    (type-fix type)))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection type-list-lift-if-atom ((x type-listp))
  :returns (new-types type-listp)
  :short "Lift @(tsee type-lift-if-atom) to lists."
  (type-lift-if-atom x))

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
      "If the check is successful, we return the type
       with the lifting of atom-kinded types to scalar types made explicit
       (see @(tsee type-lift-if-atom)),
       wherever the type validity rules require array-kinded types
       (see @(tsee type-validity-definition));
       otherwise, we return an error.")
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
       a scalar, array, or bracket type is the only kind constraint
       that makes the check fail:
       as explained in @(tsee type),
       an atom-kinded type may otherwise be used
       wherever an array-kinded type is expected,
       in which case we lift it to a scalar type.")
     (xdoc::p
      "A function type is valid iff
       its input types and its output type are all valid.
       The input types and the output type are expected to be array-kinded:
       we lift the ones that are atom-kinded.
       The exception is the output type of a nullary function type,
       which we do not lift:
       a nullary function type stands for its output type
       (see @(tsee type)),
       which may have either kind.")
     (xdoc::p
      "A universal type is valid iff its body is valid
       in the environment extended with the bound type variables.
       The body is expected to be array-kinded:
       we lift it if it is atom-kinded.")
     (xdoc::p
      "A product type is valid iff its body is valid
       in the environment extended with the bound ispace variables.
       The body is expected to be array-kinded:
       we lift it if it is atom-kinded.")
     (xdoc::p
      "A sum type is valid iff its body is valid
       in the environment extended with the bound ispace variables.
       The body is expected to be array-kinded:
       we lift it if it is atom-kinded."))
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
            (make-type-fun :in (type-lift-if-atom in)
                           :out (type-lift-if-atom out)))
     :funn (b* (((ok in) (check-type-list type.in ienv tenv))
                ((ok out) (check-type type.out ienv tenv)))
             (make-type-funn :in (type-list-lift-if-atom in)
                             :out (if (consp type.in)
                                      (type-lift-if-atom out)
                                    out)))
     :forall (b* ((tenv (type-senv-add-var type.param tenv))
                  ((ok body) (check-type type.body ienv tenv)))
               (make-type-forall :param type.param
                                 :body (type-lift-if-atom body)))
     :foralln (b* ((tenv (type-senv-add-vars type.params tenv))
                   ((ok body) (check-type type.body ienv tenv)))
                (make-type-foralln :params type.params
                                   :body (type-lift-if-atom body)))
     :pi (b* ((ienv (ispace-senv-add-var type.param ienv))
              ((ok body) (check-type type.body ienv tenv)))
           (make-type-pi :param type.param
                         :body (type-lift-if-atom body)))
     :pin (b* ((ienv (ispace-senv-add-vars type.params ienv))
               ((ok body) (check-type type.body ienv tenv)))
            (make-type-pin :params type.params
                           :body (type-lift-if-atom body)))
     :sigma (b* ((ienv (ispace-senv-add-var type.param ienv))
                 ((ok body) (check-type type.body ienv tenv)))
              (make-type-sigma :param type.param
                               :body (type-lift-if-atom body)))
     :sigman (b* ((ienv (ispace-senv-add-vars type.params ienv))
                  ((ok body) (check-type type.body ienv tenv)))
               (make-type-sigman :params type.params
                                 :body (type-lift-if-atom body))))
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
