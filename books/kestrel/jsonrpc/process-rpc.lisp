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

; converts a member list into a keyword-argument list
(define json-member-list-to-lisp-params ((members member-listp))
  :short "Convert a JSON Object's member list to a keyword-argument list."
  :long "<p>Each member @('\"name\": value') becomes @(':NAME value') in the
  output list, suitable for splicing into a function call form for by-name
  parameter passing.</p>"
  :returns (params true-listp)
  (if (endp members)
      nil
    (b* ((m (car members))
         (key (intern (string-upcase (member->name m)) "KEYWORD"))
         (val (member->value m))
         (rest (json-member-list-to-lisp-params (cdr members))))
      (cons key (cons val rest)))))

; converts the json params to an appropriate params list
(define json-params-to-lisp-params ((params structuredp))
  :short "Convert JSON-RPC params to a list suitable for splicing into a call form."
  :long "<p>For Array params, returns the list of @(see valuep) elements
  directly (by-position). For Object params, delegates to @(see
  json-member-list-to-lisp-params) to produce a keyword-argument list
  (by-name).</p>"
  :returns (lisp-params true-listp)
  (if (equal (structured-kind params) :array)
      (structured-array->elements params)
    (json-member-list-to-lisp-params (structured-object->members params))))

(define dispatch-request ((req requestp) ctx state)
  :short "Dispatch a parsed request to the appropriate @('JSONRPC') method function."
  :long "<p>Interns the method name (upcased) into the @('JSONRPC') package to
  obtain the function symbol, constructs the call form with the params spliced
  in, and evaluates it via @('trans-eval-error-triple'). Returns @('(mv erp
  result state)') where @('erp') is @('nil') on success or an @(see error) on
  failure, and @('result') is the @(see valuep) returned by the method
  function.</p>"
  :mode :program
  :stobjs state
  (b* ((method-sym
        (intern-in-package-of-symbol (string-upcase (request->method req))
                                     (pkg-witness "JSONRPC")))
       (form (if (not (request->params-presentp req))
                 `(,method-sym state)
               `(,method-sym ,@(kwote-lst (json-params-to-lisp-params
                                           (request->params req)))
                             state)))
       ((mv erp result state)
        (trans-eval-error-triple form ctx state)))
    (mv erp result state)))


;; NOTE: should process-one and process-all attach the state to its outputs?
(define process-one ((id idp) (val request+errorp) ctx state)
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
          (dispatch-request req ctx state))
         (error-val (and erp
                         (if (errorp erp)
                             erp
                           (make-internal-error "Internal error"))))
         ((when erp)
          (mv (make-error-response id error-val) state)))
      (mv (make-success-response id output) state))))

(define process-all ((pairs id-request+error-alistp) ctx state)
  :short "Process all entries in an @(see id-request+error-alist) and collect responses."
  :long "<p>Calls @(see process-one) on each entry. Notifications produce no
  response and are omitted from the result list. Returns the list of response
  @(see valuep) objects.</p>"
  :mode :program
  :stobjs state
  (if (endp pairs)
      (mv nil state)
    (b* (((mv resp state) (process-one (caar pairs) (cdar pairs) ctx state))
         ((mv rest state) (process-all (cdr pairs) ctx state)))
      (if resp 
          (mv (cons resp rest) state) 
        (mv rest state)))))

(define process-json-rpc-file ((input-file stringp) (output-file stringp) state)
  :short "Process a JSON-RPC 2.0 request file and write the response to a file."
  :long "<p>This is the main entry point for the JSON-RPC interface. It reads
  @('input-file'), parses it as a JSON-RPC 2.0 message (single request or
  batch), dispatches each request to the appropriate @('JSONRPC') package
  function, and writes the response JSON to @('output-file').</p>

  <p>For a single request, the response is a single JSON Object. For a batch
  request, the response is a JSON Array of response objects. If all requests
  are notifications, nothing is written to @('output-file').</p>

  <p>Returns @('(mv erp msg state)') where @('erp') is @('nil') on success and
  @('msg') is a status string.</p>"
  :mode :program
  :stobjs state
  (b* (((mv chars state) (read-file-into-character-list-safe input-file state))
       (msg (coerce chars 'string))
       (alist (parse-json-rpc msg))
       (batchp (> (len alist) 1))
       ((mv responses state) (process-all alist 'process-json-rpc-file state))
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
              (mv t "[ERROR] error when writing response to file" state)))
          (mv erp "[SUCCESS] response written to output file" state))))
    (mv nil "[NOTICE] no responses were generated" state)))
