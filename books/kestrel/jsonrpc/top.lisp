; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)
; Author: Grant Jurgensen (grant@kestrel.edu)

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
  :long
  (xdoc::topstring
   (xdoc::section
    "Overview"
    (xdoc::p
     "This library implements a "
     (xdoc::ahref "https://www.jsonrpc.org/specification" "JSON-RPC 2.0")
     " interface for ACL2.
      JSON-RPC is a stateless, light-weight remote procedure call protocol
      that uses JSON as its data format.
      Two transports are provided:")
    (xdoc::ul
     (xdoc::li
      (xdoc::b "File-based")
      ": requests are read from an input file
       and responses written to an output file.")
     (xdoc::li
      (xdoc::b "TCP socket")
      ": a server listens on a port
       and exchanges JSON-RPC messages over persistent connections.")))
   (xdoc::section
    "Basic Usage"
    (xdoc::p
     (xdoc::b "File transport.")
     " The entry point is @(see process-json-rpc-file).
      Given an input file containing a JSON-RPC request
      (or batch of requests) and an output file path,
      it parses the request,
      dispatches to the appropriate method function,
      and writes the JSON-RPC response to the output file.")
    (xdoc::codeblock
     "(process-json-rpc-file \"request.json\" \"response.json\" '(subtract) state)")
    (xdoc::p
     (xdoc::b "Socket transport.")
     " The entry point is @(see run-jsonrpc-server).
      It opens a TCP server socket on the given port
      and accepts connections sequentially.
      For each connection it loops reading JSON-RPC messages
      until the client disconnects,
      then waits for the next connection.
      Messages must be compact (single-line) JSON
      terminated by a newline character.
      The second argument controls the bind interface:
      @('nil') (or @('\"127.0.0.1\"')) binds to localhost only;
      @('\"0.0.0.0\"') accepts connections from any host.
      The third argument is the allowed-methods list (see below).")
    (xdoc::codeblock
     "(run-jsonrpc-server 7070 nil '(subtract) state)")
    (xdoc::p
     "The input file must contain a valid JSON-RPC 2.0 request object,
      or an array of request objects for batch processing.
      For example:")
    (xdoc::codeblock
     "{\"jsonrpc\": \"2.0\", \"method\": \"subtract\", \"params\": [10, 3], \"id\": 1}"))
   (xdoc::section
    "Writing Method Functions"
    (xdoc::p
     "Method functions are ACL2 functions
      defined in the @('JSONRPC') package.
      When a request arrives with @('\"method\": \"foo\"'),
      the library dispatches to the function @('jsonrpc::foo'),
      provided that @('foo') appears in the @('allowed-methods') list
      passed to the entry point
      (or @('allowed-methods') is @(':any')).")
    (xdoc::p
     "A typical method function has the following signature:")
    (xdoc::codeblock
     "(defun my-method (params state)"
     "  (declare (xargs :guard (structuredp params)"
     "                  :stobjs state))"
     "  ...)")
    (xdoc::p
     "The rules are:")
    (xdoc::ul
     (xdoc::li
      "The function must be in the @('JSONRPC') package.")
     (xdoc::li
      "The function may have at most one ordinary
       (non-@(see acl2::stobj)) input.
       The @('params') field in the request is passed directly to it.
       The method function is responsible for processing the params.
       The ordinary input must be present
       exactly when the request has @('params');
       otherwise, the request fails with an invalid-params error.")
     (xdoc::li
      "All other inputs must be stobjs, in any order.
       Each is passed the global stobj of that name,
       so a method function may take @('state'), user stobjs,
       both, or neither.
       Since user stobjs persist across requests,
       they can hold state shared by successive requests.")
     (xdoc::li
      "The function must return @('(mv erp result stobj1 ... stobjn)'),
       where:"
      (xdoc::ul
       (xdoc::li
        "@('erp') is @('nil') on success,
         or an @(see error) value on failure.")
       (xdoc::li
        "@('result') is a @('valuep') &mdash;
         the JSON value to be returned
         in the response's @('\"result\"') field.
         It is only used when @('erp') is @('nil').")
       (xdoc::li
        "@('stobj1'), ..., @('stobjn') are the stobjs the function updates,
         if any (e.g. @('state'))."))))
    (xdoc::p
     "For error reporting, use the provided error constructors such as
      @(see make-invalid-params-error),
      @(see make-method-not-found-error), and
      @(see make-internal-error).
      These produce @(see error) values
      with the appropriate JSON-RPC error codes.")
    (xdoc::p
     "For a worked example, see
      @('books/kestrel/jsonrpc/subtract-example.lisp')."))
   (xdoc::section
    "Batch Requests"
    (xdoc::p
     "The library supports JSON-RPC 2.0 batch requests.
      If the input file contains a JSON Array of request objects,
      each is processed independently
      and the responses are collected into a JSON Array
      written to the output file.
      Notifications (requests without an @('\"id\"') field)
      do not produce a response
      and are omitted from the batch response array.
      If all requests in a batch are notifications,
      nothing is written to the output file."))
   (xdoc::section
    "Notifications"
    (xdoc::p
     "A request without an @('\"id\"') field is a notification.
      The library dispatches notifications
      to the appropriate method function
      but does not write any response,
      per the JSON-RPC 2.0 specification.")))
  :order-subtopics t
  :default-parent t)
