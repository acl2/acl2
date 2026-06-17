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

(defpkg "JSONRPC" (append (set-difference-eq *std-pkg-symbols*
                                             '(error
                                               id))
                          '(defirrelevant
                            defxdoc+
                            json::valuep
                            json::value-fix
                            json::value-case
                            json::value-kind
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
                            json::value-listp
                            json::value-list
                            json::value-count
                            json::value-list-count
                            json::value-option
                            json::member-listp
                            json::member-list
                            json::member-list-count
                            json::member->name
                            json::member->value
                            json::make-member
                            json::make-value-number
                            json::object-member-values
                            json::object-has-member-p
                            json::parsed-to-value
                            int
                            bool
                            nat-to-string
                            parse-string-as-json
                            string-upcase
                            trans-eval-error-triple
                            read-file-into-character-list-safe
                            write-strings-to-file
                            defttag
                            include-raw)))

