; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSONRPC")

(include-book "kestrel/utilities/trans-eval-error-triple" :dir :system)
(include-book "kestrel/file-io-light/read-file-into-character-list" :dir :system)
(include-book "kestrel/file-io-light/write-strings-to-file" :dir :system)

(include-book "types")
(include-book "parse-rpc")
(include-book "json-to-string")
(include-book "response")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ process-rpc
  :parents (jsonrpc)
  :short "Dispatching and processing JSON-RPC 2.0 requests."
  :long "<p>These functions take a parsed @(see id-request+error-alist),
  dispatch each request to the appropriate @('JSONRPC') package function,
  collect the responses, and write them to an output file. The main entry
  point is @(see process-json-rpc-file).</p>"
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define method-name-allowedp ((name stringp) allowed-methods)
  :short "Check whether @('name') is permitted by @('allowed-methods')."
  :long "<p>Returns true if @('allowed-methods') is @(':any'), or if any symbol
  in @('allowed-methods') has a @('symbol-name') equal to @('name') (case-sensitive;
  callers should upcase @('name') before calling).</p>"
  :mode :program
  (or (eq allowed-methods :any)
      (and (consp allowed-methods)
           (or (equal name (symbol-name (car allowed-methods)))
               (method-name-allowedp name (cdr allowed-methods))))))

(define dispatch-request ((req requestp) allowed-methods ctx state)
  :short "Dispatch a parsed request to the appropriate @('JSONRPC') method function."
  :long "<p>Checks the method name against @('allowed-methods') first, then
  interns it into the @('JSONRPC') package to obtain the function symbol,
  constructs the call form with the params spliced in, and evaluates it via
  @('trans-eval-error-triple'). Returns @('(mv erp result state)') where
  @('erp') is @('nil') on success or an @(see error) on failure, and
  @('result') is the @(see valuep) returned by the method function.</p>

  <p>@('allowed-methods') must be either the keyword @(':any') (no restriction)
  or a list of symbols naming the permitted methods.  The check compares by
  symbol name, so the symbols may be in any package &mdash; e.g. passing
  @('(subtract)') works regardless of the current package.</p>"
  :mode :program
  :stobjs state
  (b* ((method-name (string-upcase (request->method req)))
       ((unless (method-name-allowedp method-name allowed-methods))
        (mv (make-method-not-found-error
             (concatenate 'string "Method not allowed: " (request->method req)))
            (value-null)
            state))
       (method-sym
        (intern-in-package-of-symbol method-name (pkg-witness "JSONRPC")))
       ((unless (function-symbolp method-sym (w state)))
        (mv (make-method-not-found-error
             (concatenate 'string "Method not found: " (request->method req)))
            (value-null)
            state))
       (params (request->params req))
       (form (if (not (request->params-presentp req))
                 `(,method-sym state)
               `(,method-sym ',params state)))
       ((mv erp result state)
        (trans-eval-error-triple form ctx state)))
    (mv erp result state)))


(define process-one ((id idp) (val request+errorp) allowed-methods ctx state)
  :short "Process a single @(see request+error) entry and produce a response."
  :long "<p>If @('val') is an @(see error) (from parse time), produces an
  error response immediately. If @('val') is a @(see request) and is a
  notification, returns @('nil') (no response per spec). Otherwise dispatches
  to the method function and returns either a success or error response.</p>"
  :mode :program
  :stobjs state
  (request+error-case val
    :error (mv (make-error-response id val.get) state)
    :request
    (b* ((req val.get)
         ((when (request->notificationp req))
          (mv nil state))
         ((mv erp output state)
          (dispatch-request req allowed-methods ctx state))
         (error-val (and erp
                         (if (errorp erp)
                             erp
                           (make-internal-error "Internal error"))))
         ((when erp)
          (mv (make-error-response id error-val) state)))
      (mv (make-success-response id output) state))))

(define process-all ((pairs id-request+error-alistp) allowed-methods ctx state)
  :short "Process all entries in an @(see id-request+error-alist) and collect responses."
  :long "<p>Calls @(see process-one) on each entry. Notifications produce no
  response and are omitted from the result list. Returns @('(mv erp responses
  state)') where @('erp') is @('nil') on success and @('responses') is the
  list of response @(see valuep) objects.</p>"
  :mode :program
  :stobjs state
  (if (endp pairs)
      (mv nil nil state)
    (b* (((mv resp state) (process-one (caar pairs) (cdar pairs) allowed-methods ctx state))
         ((mv erp rest state) (process-all (cdr pairs) allowed-methods ctx state)))
      (if resp
          (mv erp (cons resp rest) state)
        (mv erp rest state)))))

(define process-json-rpc-file ((input-file stringp) (output-file stringp) allowed-methods state)
  :short "Process a JSON-RPC 2.0 request file and write the response to a file."
  :long "<p>This is the main entry point for the JSON-RPC interface. It reads
  @('input-file'), parses it as a JSON-RPC 2.0 message (single request or
  batch), dispatches each request to the appropriate @('JSONRPC') package
  function, and writes the response JSON to @('output-file').</p>

  <p>@('allowed-methods') must be either the keyword @(':any') (no restriction)
  or a list of symbols naming the permitted methods, e.g. @('(subtract add)').
  Requests for methods not in the list are rejected with a method-not-found
  error.</p>

  <p>For a single request, the response is a single JSON Object. For a batch
  request, the response is a JSON Array of response objects. If all requests
  are notifications, nothing is written to @('output-file').</p>

  <p>Returns @('(mv erp val state)') where @('erp') is @('nil') on success and
  @('val') is the response @(see valuep).</p>"
  :mode :program
  :stobjs state
  (b* (((mv chars state) (read-file-into-character-list-safe input-file state))
       (msg (coerce chars 'string))
       ((mv batchp alist) (parse-json-rpc msg))
       ((mv erp responses state) (process-all alist allowed-methods 'process-json-rpc-file state))
       ((when erp) (mv erp nil state))
       (response-val
        (cond ((endp responses) nil)
              (batchp (value-array responses))
              (t (car responses))))
       ((when response-val)
        (b* ((response (list (value-to-json-string response-val)))
             ((mv erp state)
              (write-strings-to-file response
                                     output-file
                                     'process-json-rpc-file
                                     state))
             ((when erp)
              (mv t nil state)))
          (mv nil response-val state)))
       ((mv erp1 state)
        (write-strings-to-file nil
                               output-file
                               'process-json-rpc-file
                               state)))
    (mv erp1 nil state)))
