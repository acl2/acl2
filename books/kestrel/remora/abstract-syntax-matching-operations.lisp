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
  :returns (type+ispace type+ispace-resultp)
  :short "Check if an array type is an @(':array') summand,
          returning its elements' atom type and its ispace if successful."
  (if (type-case type :array)
      (make-type+ispace :type (type-array->elem type)
                        :ispace (type-array->ispace type))
    (reserr nil)))

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
