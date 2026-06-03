; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "kestrel/json/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "JSONRPC"
  (append (set-difference-eq *std-pkg-symbols*
                             '(error
                               id
                               request))
          '(defirrelevant
            defxdoc+
            json::valuep
            json::value-fix
            json::value-case
            json::value-null
            json::value-true
            json::value-false
            json::value-number
            json::value-string
            json::value-array
            json::value-object
            json::value-number->get
            json::value-string->get
            json::value-array->elements
            json::value-object->members
            json::make-member
            json::member->name
            json::member->value
            json::member-listp)))
