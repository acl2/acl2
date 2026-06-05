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
(include-book "kestrel/json-parser/parse-json" :dir :system)

(include-book "types")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parse-rpc
  :parents (jsonrpc)
  :short "Parsing JSON-RPC 2.0 messages."
  :long "<p>These functions parse a JSON string into an @(see
  id-request+error-alist). The top-level entry point is @(see parse-json-rpc),
  which accepts both single requests and batch requests (arrays of requests).
  Each element is validated against the JSON-RPC 2.0 specification and yields
  either a parsed @(see request) or an @(see error) with the appropriate
  error code.</p>"
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; takes in a JSON object and extracts its "id" field
; returns:
;  - has-id: true if the "id" field is present
;  - is-valid: true if either the "id" field is not present or it is present and
; of the correct type
;  - id: the id
(define parse-rpc-id ((obj valuep))
  :short "Extract the @('id') field from a JSON-RPC request object."
  :guard (equal (value-kind obj) :object)
  :returns (mv (has-id booleanp) (is-valid booleanp) (id idp))
  (b* ((id-val? (object-member-value? "id" obj))
       ((unless id-val?)
        (mv nil t (id-null)))
       (id-val id-val?)
       ((when (equal (value-kind id-val) :string))
        (mv t t (id-string (value-string->get id-val))))
       ((when (and (equal (value-kind id-val) :number)
                   (rationalp (value-number->get id-val))))
        (mv t t (id-number (value-number->get id-val))))
       ((when (equal (value-kind id-val) :null))
        (mv t t (id-null))))
    (mv t nil (id-null))))

; takes in a JSON value and tries to parse it into a request+error
(define parse-rpc-request ((val valuep))
  :short "Parse a single JSON value as a JSON-RPC 2.0 request."
  :returns (mv (id idp) (req+err request+errorp))
  (b* (((unless (equal (value-kind val) :object))
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error "Request must be a JSON object"))))
       (jsonrpc-val? (object-member-value? "jsonrpc" val))
       ((unless (and jsonrpc-val?
                     (value-case jsonrpc-val? :string)
                     (equal (value-string->get jsonrpc-val?) "2.0")))
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error 
              "Missing or invalid \"jsonrpc\" field; must be \"2.0\""))))
       (method-val? (object-member-value? "method" val))
       ((unless (and method-val?
                     (equal (value-kind method-val?) :string)))
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error 
              "Missing or invalid \"method\" field; must be a string"))))
       (method (value-string->get method-val?))
       (params-presentp (object-has-member-p "params" val))
       (params-val? (and params-presentp 
                         (object-member-value? "params" val)))
       ((when (and params-val?
                   (not (value-case params-val? :array))
                   (not (value-case params-val? :object))))
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error 
              "\"params\" must be an array or object"))))
       (params (if params-val?
                   (if (equal (value-kind params-val?) :array)
                       (structured-array (value-array->elements params-val?))
                     (structured-object (value-object->members params-val?)))
                 (irr-structured)))
       ((mv has-id is-valid id-val) (parse-rpc-id val))
       ((unless is-valid)
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error 
              "\"id\" must either be a number, string, or null"))))
       (notificationp (not has-id)))
    (mv id-val
        (request+error-request
         (make-request :method method
                       :params-presentp params-presentp
                       :params params
                       :notificationp notificationp
                       :id id-val)))))

; takes in a JSON array and tries to parse it into an id-request+error-alist
(define parse-rpc-requests ((vals value-listp))
  :short "Parse a list of JSON values as a JSON-RPC 2.0 batch request."
  :returns (alist id-request+error-alistp)
  (b* (((when (endp vals)) nil)
       ((mv id req+err) (parse-rpc-request (car vals))))
    (cons (cons id req+err)
          (parse-rpc-requests (cdr vals)))))

; takes in a string and tries to parse it into an id-request+error-alist
(define parse-json-rpc ((msg stringp))
  :short "Parse a JSON string as a JSON-RPC 2.0 message."
  :long "<p>Accepts both single requests (JSON Object) and batch requests
  (JSON Array). Returns an @(see id-request+error-alist) with one entry per
  request. If the top-level JSON is not an Object or Array, or if the Array
  is empty, a single error entry with code @('-32600') is returned. If the
  string is not valid JSON, a single error entry with code @('-32700') is
  returned.</p>"
  :returns (alist id-request+error-alistp)
  (b* (((mv erp parsed) (parse-string-as-json msg))
       ((when erp)
        (list (cons (id-null)
                    (request+error-error
                     (make-parse-error "Failed to parse JSON")))))
       ((mv erp value) (parsed-to-value parsed))
       ((when erp)
        (list (cons (id-null)
                    (request+error-error
                     (make-parse-error "Failed to convert parsed JSON")))))
       ((when (equal (value-kind value) :array))
        (b* ((elems (value-array->elements value))
             ((when (endp elems))
              (list (cons (id-null)
                          (request+error-error
                           (make-invalid-request-error 
                            "Batch request array must not be empty"))))))
          (parse-rpc-requests elems)))
       ((when (equal (value-kind value) :object))
        (b* (((mv id req+err) (parse-rpc-request value)))
          (list (cons id req+err)))))
    (list (cons (id-null)
                (request+error-error
                 (make-invalid-request-error 
                  "Top-level JSON value must be an object or array"))))))
