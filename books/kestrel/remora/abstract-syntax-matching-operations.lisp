; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-derived-fixtypes")
(include-book "abstract-syntax-structurals")

(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable type+ispace-p-when-result-not-error
                          type+ispace-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-matching-operations
  :parents (abstract-syntax)
  :short "Operations to match ASTs to patterns."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce operations to check whether
     certain ASTs match certain patterns,
     in which case the components of the pattern are returned.")
   (xdoc::p
    "We start by adding a few of them that are needed elsewhere,
     but we plan to add more."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-array ((type typep))
  :no-function nil
  :returns (type+ispace type+ispace-resultp)
  :short "Check if an array type is an @(':array') or @(':bracket') summand,
          returning its elements' atom type and its ispace if successful."
  :long
  (xdoc::topstring
   (xdoc::p
    "A bracket type is an array type whose shape is
     the concatenation of its ispaces
     (see @(tsee type) and @(tsee eval-type)),
     so we return that concatenation as its ispace,
     consistently with @(tsee type-equivp)."))
  (type-case
   type
   :array (make-type+ispace :type type.elem
                            :ispace type.ispace)
   :bracket (make-type+ispace
             :type type.elem
             :ispace (ispace-shape
                      (shape-append
                       (shape-list-from-ispace-list type.ispaces))))
   :otherwise (reserrf (list :not-array-type (type-fix type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-match-array ((types type-listp))
  :returns (types+ispaces type+ispace-list-resultp)
  :short "Check if all the array types in a list are @(':array') summands,
          returning the list of their elements' atom types and its ispaces
          if successful."
  (b* (((when (endp types)) nil)
       ((ok type+ispace) (type-match-array (car types)))
       ((ok types+ispaces) (type-list-match-array (cdr types))))
    (cons type+ispace types+ispaces))

  ///

  (defret len-of-type-list-match-array
    (implies (not (reserrp types+ispaces))
             (equal (len types+ispaces)
                    (len types)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-fun ((type typep))
  :returns (in+out typelist+type-resultp)
  :short "Check if an atom type is a function type,
          returning its input and output array types if successful."
  (if (type-case type :fun)
      (make-typelist+type :types (type-fun->in type)
                          :type (type-fun->out type))
    (reserr nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-forall ((type typep))
  :returns (vars+type typevarlist+type-resultp)
  :short "Check if an atom type is a universal type,
          returning its type parameter variables and body array type
          if successful."
  (if (type-case type :forall)
      (make-typevarlist+type :vars (type-forall->params type)
                             :type (type-forall->body type))
    (reserr nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-product ((type typep))
  :returns (vars+type ispacevarlist+type-resultp)
  :short "Check if an atom type is a product type,
          returning its ispace parameter variables and body array type
          if successful."
  (if (type-case type :pi)
      (make-ispacevarlist+type :vars (type-pi->params type)
                               :type (type-pi->body type))
    (reserr nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-sum ((type typep))
  :returns (vars+type ispacevarlist+type-resultp)
  :short "Check if a type is a sum type,
          returning its ispace parameter variables and body array type
          if successful."
  (if (type-case type :sigma)
      (make-ispacevarlist+type :vars (type-sigma->params type)
                               :type (type-sigma->body type))
    (reserr nil)))
