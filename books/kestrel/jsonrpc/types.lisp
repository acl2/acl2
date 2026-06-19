; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSONRPC")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)
(include-book "kestrel/json/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ types
  :parents (jsonrpc)
  :short "Types for the JSON-RPC 2.0 interface."
  :long "<p>This section defines the ACL2 types used to represent JSON-RPC 2.0
  data structures, including request identifiers, parameter structures, requests,
  errors, and the alist mapping ids to parsed results.</p>"
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; id: MUST contain either a string, a number, or a null value
(fty::deftagsum id
  :short "A JSON-RPC request/response identifier."
  :long "<p>Per the JSON-RPC 2.0 specification, an @('id') MUST contain a
  String, Number, or Null value if included in a request. The @(':null') case
  is also used in error responses when the request @('id') could not be
  determined (e.g. due to a parse error or invalid request).</p>"
  (:string ((get string)))
  (:number ((get rational)))
  (:null ())
  :pred idp)

(defirrelevant irr-id
  :short "An irrelevant id."
  :type idp
  :body (id-null))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum structured
  :short "A structured JSON value (Array or Object)."
  :long "<p>Per the JSON-RPC 2.0 specification, the @('params') field of a
  request, if present, MUST be a Structured value &mdash; either a JSON Array
  (for by-position parameter passing) or a JSON Object (for by-name parameter
  passing).</p>"
  (:array ((elements value-list)))
  (:object ((members member-list)))
  :pred structuredp)

(defirrelevant irr-structured
  :short "An irrelevant structured value."
  :type structuredp
  :body (make-structured-array :elements nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; request:
;  - method: the name of the method to be invoked
;  - params-presentp: whether the params are present
;  - params: a structured JSON value (array or object)
;  - notificationp: true if no id provided
;  - id: the request id
(fty::defprod request
  :short "A parsed JSON-RPC 2.0 request object."
  :long "<p>Represents a successfully parsed JSON-RPC 2.0 Request object with
  the following fields:</p>
  <ul>
    <li>@('method'): the name of the method to be invoked.</li>
    <li>@('params-presentp'): whether the @('params') field was present in the
    request.</li>
    <li>@('params'): the parameter values, either a JSON Array (by-position)
    or JSON Object (by-name). Only meaningful when @('params-presentp') is
    true.</li>
    <li>@('notificationp'): true when no @('id') field was present, meaning
    this is a notification and no response should be sent.</li>
    <li>@('id'): the request identifier. Only meaningful when
    @('notificationp') is false.</li>
  </ul>"
  ((method string)
   (params-presentp bool)
   (params structured)
   (notificationp bool)
   (id id))
  :pred requestp)

(defirrelevant irr-request
  :short "An irrelevant request"
  :type requestp
  :body (make-request :method ""
                      :params-presentp nil
                      :params (irr-structured)
                      :notificationp nil
                      :id (irr-id)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; error
;  - code: error code
;    + -32700: Parse error
;    + -32600: Invalid request
;    + -32601: Method not found
;    + -32602: Invalid params
;    + -32603: Internal error
;    + -32000 to -32099: Server error
;  - message: the message string
;  - data: additional info, MAY be ommitted
(fty::defprod error
  :short "A JSON-RPC 2.0 error object."
  :long "<p>Represents a JSON-RPC 2.0 error with the following fields:</p>
  <ul>
    <li>@('code'): an integer error code. The following codes are predefined:
    @('-32700') (Parse error), @('-32600') (Invalid Request), @('-32601')
    (Method not found), @('-32602') (Invalid params), @('-32603') (Internal
    error). Codes from @('-32000') to @('-32099') are reserved for
    server-defined errors.</li>
    <li>@('message'): a short string description of the error.</li>
    <li>@('data'): an optional JSON value containing additional error
    information. May be @('nil') if absent.</li>
  </ul>
  <p>Use the constructors @(see make-parse-error), @(see make-invalid-request-error),
  @(see make-method-not-found-error), @(see make-invalid-params-error), and
  @(see make-internal-error) to build errors with the correct standard
  codes.</p>"
  ((code int)
   (message string)
   (data value-option))
  :pred errorp)

(define make-parse-error ((msg stringp))
  :returns (err errorp)
  (make-error :code -32700 :message msg :data nil))

(define make-invalid-request-error ((msg stringp))
  :returns (err errorp)
  (make-error :code -32600 :message msg :data nil))

(define make-method-not-found-error ((msg stringp))
  :returns (err errorp)
  (make-error :code -32601 :message msg :data nil))

(define make-invalid-params-error ((msg stringp))
  :returns (err errorp)
  (make-error :code -32602 :message msg :data nil))

(define make-internal-error ((msg stringp))
  :returns (err errorp)
  (make-error :code -32603 :message msg :data nil))

(defirrelevant irr-error
  :short "An irrelevant error"
  :type errorp
  :body (make-error :code 0 :message "" :data nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; request+error: contains a request and an error
(fty::deftagsum request+error
  :short "The result of parsing a single JSON-RPC request element."
  :long "<p>Represents either a successfully parsed @(see request) or a
  parse-time @(see error). This is the per-element result of @(see
  parse-rpc-request): if the element is a valid request it yields a
  @(':request'), otherwise it yields an @(':error') with the appropriate
  error code and message.</p>"
  (:request ((get request)))
  (:error ((get error)))
  :pred request+errorp)

; id-request+error-alist: mapping ids to request-errors
(fty::defalist id-request+error-alist
  :short "An alist mapping request ids to their parsed results."
  :long "<p>Maps each request @(see id) to the corresponding @(see
  request+error) &mdash; either a successfully parsed @(see request) or a
  parse-time @(see error). This is the output of @(see parse-json-rpc) and
  the input to @(see process-all). For batch requests, there is one entry per
  element of the input array. For single requests, there is exactly one
  entry.</p>"
  :key-type id
  :val-type request+error
  :true-listp t
  :pred id-request+error-alistp)
