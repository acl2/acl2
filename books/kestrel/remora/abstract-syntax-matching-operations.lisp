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

(local (in-theory (enable type+shape-p-when-result-not-error
                          type+shape-listp-when-result-not-error)))

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
  :returns (type+shape type+shape-resultp)
  :short "Check if a type is an array type,
          returning its inner type and shape if successful."
  (if (type-case type :array)
      (make-type+shape :type (type-array->type type)
                       :shape (type-array->shape type))
    (reserr nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-match-array ((types type-listp))
  :returns (types+shapes type+shape-list-resultp)
  :short "Check if all the types in a list are array types,
          returning the list of their inner types and shapes if successful."
  (b* (((when (endp types)) nil)
       ((ok type+shape) (type-match-array (car types)))
       ((ok types+shapes) (type-list-match-array (cdr types))))
    (cons type+shape types+shapes))

  ///

  (defret len-of-type-list-match-array
    (implies (not (reserrp types+shapes))
             (equal (len types+shapes)
                    (len types)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-fun ((type typep))
  :returns (in+out typelist+type-resultp)
  :short "Check if a type is a function type,
          returning its input and output types if successful."
  (if (type-case type :fun)
      (make-typelist+type :types (type-fun->in type)
                          :type (type-fun->out type))
    (reserr nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-forall ((type typep))
  :returns (vars+type kindedvarlist+type-resultp)
  :short "Check if a type is a universal type,
          returning its kinded variable list and body type if successful."
  (if (type-case type :forall)
      (make-kindedvarlist+type :vars (type-forall->vars type)
                               :type (type-forall->type type))
    (reserr nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-product ((type typep))
  :returns (params+type ispacevarlist+type-resultp)
  :short "Check if a type is a product type,
          returning its ispace parameter variables and body type if successful."
  (if (type-case type :pi)
      (make-ispacevarlist+type :params (type-pi->params type)
                               :type (type-pi->type type))
    (reserr nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-sum ((type typep))
  :returns (params+type ispacevarlist+type-resultp)
  :short "Check if a type is a sum type,
          returning its ispace parameter variables and body type if successful."
  (if (type-case type :sigma)
      (make-ispacevarlist+type :params (type-sigma->params type)
                               :type (type-sigma->type type))
    (reserr nil)))
