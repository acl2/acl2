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

(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable atomtype+shape-p-when-result-not-error
                          atomtype+shape-listp-when-result-not-error)))

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

(define array-type-match-array ((type array-typep))
  :returns (type+shape atomtype+shape-resultp)
  :short "Check if an array type is an @(':array') summans,
          returning its elements' atom type and its shape if successful."
  (if (array-type-case type :array)
      (make-atomtype+shape :type (array-type-array->type type)
                           :shape (array-type-array->shape type))
    (reserr nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define array-type-list-match-array ((types array-type-listp))
  :returns (types+shapes atomtype+shape-list-resultp)
  :short "Check if all the array types in a list are @(':array') summands,
          returning the list of their elements' atom types and its shapes
          if successful."
  (b* (((when (endp types)) nil)
       ((ok type+shape) (array-type-match-array (car types)))
       ((ok types+shapes) (array-type-list-match-array (cdr types))))
    (cons type+shape types+shapes))

  ///

  (defret len-of-array-type-list-match-array
    (implies (not (reserrp types+shapes))
             (equal (len types+shapes)
                    (len types)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-type-match-fun ((type atom-typep))
  :returns (in+out arraytypelist+arraytype-resultp)
  :short "Check if an atom type is a function type,
          returning its input and output array types if successful."
  (if (atom-type-case type :fun)
      (make-arraytypelist+arraytype :types (atom-type-fun->in type)
                                    :type (atom-type-fun->out type))
    (reserr nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-type-match-forall ((type atom-typep))
  :returns (vars+type typevarlist+arraytype-resultp)
  :short "Check if an atom type is a universal type,
          returning its type parameter variables and body array type
          if successful."
  (if (atom-type-case type :forall)
      (make-typevarlist+arraytype :vars (atom-type-forall->params type)
                                  :type (atom-type-forall->type type))
    (reserr nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-type-match-product ((type atom-typep))
  :returns (vars+type ispacevarlist+arraytype-resultp)
  :short "Check if an atom type is a product type,
          returning its ispace parameter variables and body array type
          if successful."
  (if (atom-type-case type :pi)
      (make-ispacevarlist+arraytype :vars (atom-type-pi->params type)
                                    :type (atom-type-pi->type type))
    (reserr nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-type-match-sum ((type atom-typep))
  :returns (vars+type ispacevarlist+arraytype-resultp)
  :short "Check if a type is a sum type,
          returning its ispace parameter variables and body array type
          if successful."
  (if (atom-type-case type :sigma)
      (make-ispacevarlist+arraytype :vars (atom-type-sigma->params type)
                                    :type (atom-type-sigma->type type))
    (reserr nil)))
