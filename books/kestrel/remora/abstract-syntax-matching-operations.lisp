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

(local
 (in-theory
  (enable type+index-p-when-type+index-resultp-and-not-reserrp
          type+index-listp-when-type+index-list-resultp-and-not-reserrp)))

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
  :returns (type+index type+index-resultp)
  :short "Check if a type is an array type,
          returning its inner type and index if successful."
  (if (type-case type :array)
      (make-type+index :type (type-array->type type)
                       :index (type-array->index type))
    (reserr nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-match-array ((types type-listp))
  :returns (types+indices type+index-list-resultp)
  :short "Check if all the types in a list are array types,
          returning the list of their inner types and indices if successful."
  (b* (((when (endp types)) nil)
       ((ok type+index) (type-match-array (car types)))
       ((ok types+indices) (type-list-match-array (cdr types))))
    (cons type+index types+indices))

  ///

  (defret len-of-type-list-match-array
    (implies (not (reserrp types+indices))
             (equal (len types+indices)
                    (len types)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-fun ((type typep))
  :returns (in+out typelist+type-resultp)
  :short "Check if a type if a function type,
          returning its input and output types if successful."
  (if (type-case type :fun)
      (make-typelist+type :types (type-fun->in type)
                          :type (type-fun->out type))
    (reserr nil)))
