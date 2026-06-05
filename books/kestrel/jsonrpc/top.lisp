; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSONRPC")

(include-book "types")
(include-book "parse-rpc")
(include-book "json-to-string")
(include-book "response")
(include-book "process-rpc")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ jsonrpc
  :parents (acl2::kestrel-books acl2::projects)
  :short "A JSON-RPC 2.0 interface for ACL2."
  :long "<h3>Overview</h3>

  <p>This library implements a
  <a href=\"https://www.jsonrpc.org/specification\">JSON-RPC 2.0</a>
  interface for ACL2. JSON-RPC is a stateless, light-weight remote procedure
  call protocol that uses JSON as its data format. It is transport agnostic;
  this library implements a file-based transport where requests are read from
  an input file and responses are written to an output file.</p>

  <h3>Basic Usage</h3>

  <p>The main entry point is @(see process-json-rpc-file). Given an input file
  containing a JSON-RPC request (or batch of requests) and an output file path,
  it parses the request, dispatches to the appropriate method function, and
  writes the JSON-RPC response to the output file.</p>

  @({
    (process-json-rpc-file \"request.json\" \"response.json\" state)
  })

  <p>The input file must contain a valid JSON-RPC 2.0 request object, or an
  array of request objects for batch processing. For example:</p>

  @({
    {\"jsonrpc\": \"2.0\", \"method\": \"subtract\", \"params\": [10, 3], \"id\": 1}
  })

  <h3>Writing Method Functions</h3>

  <p>Method functions are ACL2 functions defined in the @('JSONRPC') package.
  When a request arrives with @('\"method\": \"foo\"'), the library dispatches
  to the function @('jsonrpc::foo').</p>

  <p>Every method function must have the following signature:</p>

  @({
    (defun jsonrpc::my-method (param1 param2 ... state)
      (declare (xargs :guard (and (valuep param1) (valuep param2) ...)
                      :mode :program
                      :stobjs state))
      ...)
  })

  <p>The rules are:</p>

  <ul>
    <li>The function must be in the @('JSONRPC') package. The method name in
    the JSON request is upcased and interned into this package to find the
    function.</li>

    <li>Each parameter corresponds to one element of the @('params') field in
    the request. If @('params') is a JSON Array, the elements are passed
    positionally. If @('params') is a JSON Object, the members are passed as
    keyword arguments (e.g. @(':name value')). If @('params') is absent, only
    @('state') is passed.</li>

    <li>All parameters (except @('state')) are of type @('valuep') — raw JSON
    values. The method function is responsible for validating and extracting the
    values it needs.</li>

    <li>@('state') is always passed as the last argument.</li>

    <li>The function must return @('(mv erp result state)') where:
    <ul>
      <li>@('erp') is @('nil') on success, or an @(see error) value on
      failure.</li>
      <li>@('result') is a @('valuep') — the JSON value to be returned in the
      response's @('\"result\"') field. It is only used when @('erp') is
      @('nil').</li>
      <li>@('state') is the (possibly updated) ACL2 state.</li>
    </ul></li>
  </ul>

  <p>For error reporting, use the provided error constructors such as
  @(see make-invalid-params-error), @(see make-method-not-found-error), and
  @(see make-internal-error). These produce @(see error) values with the
  appropriate JSON-RPC error codes.</p>

  <p>Here is an example method function that subtracts two numbers:</p>

  @({
    (defun jsonrpc::subtract (x y state)
      (declare (xargs :guard (and (valuep x) (valuep y))
                      :mode :program
                      :stobjs state))
      (b* (((unless (equal (value-kind x) :number))
            (mv (make-invalid-params-error \"First argument must be a number\")
                (value-null)
                state))
           ((unless (equal (value-kind y) :number))
            (mv (make-invalid-params-error \"Second argument must be a number\")
                (value-null)
                state))
           (result (make-value-number :get (- (value-number->get x)
                                              (value-number->get y)))))
        (mv nil result state)))
  })

  <h3>Batch Requests</h3>

  <p>The library supports JSON-RPC 2.0 batch requests. If the input file
  contains a JSON Array of request objects, each is processed independently and
  the responses are collected into a JSON Array written to the output file.
  Notifications (requests without an @('\"id\"') field) do not produce a
  response and are omitted from the batch response array. If all requests in a
  batch are notifications, nothing is written to the output file.</p>

  <h3>Notifications</h3>

  <p>A request without an @('\"id\"') field is a notification. The library
  dispatches notifications to the appropriate method function but does not
  write any response, per the JSON-RPC 2.0 specification.</p>"
  :order-subtopics t
  :default-parent t)

