; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSONRPC")

(include-book "kestrel/json/top" :dir :system)

(include-book "types")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ response
  :parents (jsonrpc)
  :short "Building JSON-RPC 2.0 response objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "These functions construct JSON-RPC 2.0 Response objects
     as @(see valuep) values ready for serialization.
     Per the specification, every Response object contains
     @('\"jsonrpc\": \"2.0\"') and the @('id') from the corresponding request.
     A successful response contains a @('\"result\"') member;
     an error response contains an @('\"error\"') member.
     Both members MUST NOT appear together."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define id-to-json-value ((id idp))
  :returns (val valuep)
  :short "Convert a JSON-RPC @(see id) to a JSON @(see valuep)."
  (id-case id
    :string (value-string id.get)
    :number (value-number id.get)
    :null (value-null)))

(define make-success-response ((id idp) (result valuep))
  :returns (val valuep)
  :short "Build a JSON-RPC 2.0 success Response object."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns a JSON Object of the form
     @('{\"jsonrpc\":\"2.0\",\"result\":<result>,\"id\":<id>}')."))
  (value-object
   (list (make-member :name "jsonrpc" :value (value-string "2.0"))
         (make-member :name "result" :value result)
         (make-member :name "id" :value (id-to-json-value id)))))

(define make-error-response ((id idp) (err errorp))
  :returns (val valuep)
  :short "Build a JSON-RPC 2.0 error Response object."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns a JSON Object of the form
     @('{\"jsonrpc\":\"2.0\",\"error\":{\"code\":<code>,\"message\":<msg>},\"id\":<id>}').
     If the @(see error) has a @('data') field,
     it is included in the error object.
     The @('id') should be @('null') (i.e. @('(id-null)'))
     when the request @('id') could not be determined."))
  (b* ((error-obj-members
        (append (list (make-member :name "code"
                                   :value (value-number
                                           (error->code err)))
                      (make-member :name "message"
                                   :value (value-string
                                           (error->message err))))
                (if (error->data err)
                    (list (make-member :name "data"
                                       :value (error->data err)))
                  nil))))
    (value-object
     (list (make-member :name "jsonrpc"
                        :value (value-string "2.0"))
           (make-member :name "error"
                        :value (value-object error-obj-members))
           (make-member :name "id"
                        :value (id-to-json-value id))))))
