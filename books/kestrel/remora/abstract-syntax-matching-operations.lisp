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

(acl2::controlled-configuration)

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

; TODO: add more matching operations
