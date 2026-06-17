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
(include-book "socket")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ jsonrpc
  :parents (acl2::kestrel-books acl2::projects)
  :short "A JSON-RPC 2.0 interface for ACL2."
  :long "<h3>Overview</h3>

  <p>This library implements a
  <a href=\"https://www.jsonrpc.org/specification\">JSON-RPC 2.0</a>
  interface for ACL2. JSON-RPC is a stateless, light-weight remote procedure
  call protocol that uses JSON as its data format. Two transports are
  provided:</p>

  <ul>
    <li><b>File-based</b>: requests are read from an input file and responses
    written to an output file.</li>
    <li><b>TCP socket</b>: a server listens on a port and exchanges JSON-RPC
    messages over persistent connections.</li>
  </ul>

  <h3>Basic Usage</h3>

  <p><b>File transport.</b> The entry point is @(see process-json-rpc-file).
  Given an input file containing a JSON-RPC request (or batch of requests) and
  an output file path, it parses the request, dispatches to the appropriate
  method function, and writes the JSON-RPC response to the output file.</p>

  @({
    (process-json-rpc-file \"request.json\" \"response.json\" '(subtract) state)
  })

  <p><b>Socket transport.</b> The entry point is @(see run-jsonrpc-server).
  It opens a TCP server socket on the given port and accepts a single
  connection.  It then loops reading JSON-RPC messages from that connection
  until the client disconnects.  Messages must be compact (single-line) JSON
  terminated by a newline character.  The second argument controls the bind
  interface: @('nil') (or @('\"127.0.0.1\"')) binds to localhost only;
  @('\"0.0.0.0\"') accepts connections from any host.  The third argument is
  the allowed-methods list (see below).</p>

  @({
    (run-jsonrpc-server 7070 nil '(subtract) state)
  })

  <p>The input file must contain a valid JSON-RPC 2.0 request object, or an
  array of request objects for batch processing. For example:</p>

  @({
    {\"jsonrpc\": \"2.0\", \"method\": \"subtract\", \"params\": [10, 3], \"id\": 1}
  })

  <h3>Writing Method Functions</h3>

  <p>Method functions are ACL2 functions defined in the @('JSONRPC') package.
  When a request arrives with @('\"method\": \"foo\"'), the library dispatches
  to the function @('jsonrpc::foo'), provided that @('foo') appears in the
  @('allowed-methods') list passed to the entry point (or @('allowed-methods')
  is @(':any')).</p>

  <p>Every method function must have the following signature:</p>

  @({
    (defun my-method (params state)
      (declare (xargs :guard (structuredp params)
                      :stobjs state))
      ...)
  })

  <p>The rules are:</p>

  <ul>
    <li>The function must be in the @('JSONRPC') package.</li>

    <li>The @('params') field in request is passed directly to the first
    argument of the method function. The method function is responsible for
    processing the params. If @('params') is absent, only @('state') is
    passed.</li>

    <li>@('state') is always passed as the last argument.</li>

    <li>The function must return a error-triple @('(mv erp result state)')
    where:
    <ul>
      <li>@('erp') is @('nil') on success, or an @(see error) value on
      failure.</li>
      <li>@('result') is a @('valuep') — the JSON value to be returned in the
      response's @('\"result\"') field. It is only used when @('erp') is
      @('nil').</li>
      <li>@('state') is the ACL2 state.</li>
    </ul></li>
  </ul>

  <p>For error reporting, use the provided error constructors such as
  @(see make-invalid-params-error), @(see make-method-not-found-error), and
  @(see make-internal-error). These produce @(see error) values with the
  appropriate JSON-RPC error codes.</p>

  <p>Here is an example method function that subtracts two numbers:</p>

  @({
    (define subtract ((params structuredp) state)
      :returns (mv erp (res valuep) state)
      :stobjs state
      (b* (((mv x y)
        (if (equal (structured-kind params) :array)
            (b* ((elems (structured-array->elements params)))
              (if (= (len elems) 2)
                  (mv (first elems) (second elems))
                (mv nil nil)))
          (b* ((members (structured-object->members params))
               (x (find-member-value \"minuend\" members))
               (y (find-member-value \"subtrahend\" members)))
            (mv x y))))
       ((unless (and x y))
        (mv (make-invalid-params-error
             \"Params must be [minuend, subtrahend] or
             {\"minuend\":...,\"subtrahend\":...}\")
            (value-null)
            state))
       ((unless (equal (value-kind x) :number))
        (mv (make-invalid-params-error \"minuend must be a number\")
            (value-null)
            state))
       ((unless (equal (value-kind y) :number))
        (mv (make-invalid-params-error \"subtrahend must be a number\")
            (value-null)
            state))
       (result (- (value-number->get x) (value-number->get y))))
    (mv nil (value-number result) state)))
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

