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
  :long
  (xdoc::topstring
   (xdoc::p
    "These functions take a parsed @(see id-request+error-alist),
     dispatch each request to the appropriate @('JSONRPC') package function,
     collect the responses, and write them to an output file.
     The main entry point is @(see process-json-rpc-file)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define method-name-allowedp ((name stringp) allowed-methods)
  :mode :program
  :short "Check whether @('name') is permitted by @('allowed-methods')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns true if @('allowed-methods') is @(':any'),
     or if any symbol in @('allowed-methods')
     has a @('symbol-name') equal to @('name')
     (case-sensitive; callers should upcase @('name') before calling)."))
  (or (eq allowed-methods :any)
      (and (consp allowed-methods)
           (or (equal name (symbol-name (car allowed-methods)))
               (method-name-allowedp name (cdr allowed-methods))))))

(define method-signature-okp ((stobjs-in symbol-listp)
                              (stobjs-out symbol-listp))
  :returns (yes/no booleanp)
  :short "Check whether a method function's signature is supported."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every input must be a @(see acl2::stobj),
     except for at most one ordinary input, which receives the params.
     The outputs must be two ordinary values, @('erp') and @('result'),
     followed only by stobjs."))
  (and (not (member-eq :df stobjs-in))
       (<= (- (len stobjs-in) (len (remove-eq nil stobjs-in))) 1)
       (consp stobjs-out)
       (consp (cdr stobjs-out))
       (null (car stobjs-out))
       (null (cadr stobjs-out))
       (not (member-eq nil (cddr stobjs-out)))
       (not (member-eq :df (cddr stobjs-out)))))

(define method-call-args ((stobjs-in symbol-listp) params)
  :returns (args true-listp)
  :short "The arguments of a call of a method function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each stobj input, including @('state'),
     is passed the stobj of that name, i.e. the live, global stobj.
     The ordinary input, if any, is passed the quoted @('params')."))
  (if (endp stobjs-in)
      nil
    (cons (or (car stobjs-in) `',params)
          (method-call-args (cdr stobjs-in) params))))

(define dispatch-request ((req requestp) allowed-methods ctx state)
  :mode :program
  :stobjs state
  :short "Dispatch a parsed request
          to the appropriate @('JSONRPC') method function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Checks the method name against @('allowed-methods') first,
     then interns it into the @('JSONRPC') package
     to obtain the function symbol.
     After checking the function's signature
     (see @(see method-signature-okp)),
     it constructs the call form from that signature
     (see @(see method-call-args))
     and evaluates it via @('trans-eval-no-warning')
     (see @(see acl2::trans-eval)).
     Returns @('(mv erp result state)'),
     where @('erp') is @('nil') on success or an @(see error) on failure,
     and @('result') is the @(see valuep) returned by the method function.")
   (xdoc::p
    "@('allowed-methods') must be either the keyword @(':any')
     (no restriction) or a list of symbols naming the permitted methods.
     The check compares by symbol name,
     so the symbols may be in any package &mdash;
     e.g. passing @('(subtract)') works regardless of the current package."))
  (b* ((method-name (string-upcase (request->method req)))
       ((unless (method-name-allowedp method-name allowed-methods))
        (mv (make-method-not-found-error
             (concatenate 'string "Method not allowed: " (request->method req)))
            (value-null)
            state))
       (method-sym
        (intern-in-package-of-symbol method-name (pkg-witness "JSONRPC")))
       (wrld (w state))
       ((unless (function-symbolp method-sym wrld))
        (mv (make-method-not-found-error
             (concatenate 'string "Method not found: " (request->method req)))
            (value-null)
            state))
       (stobjs-in (acl2::stobjs-in method-sym wrld))
       ((unless (method-signature-okp stobjs-in
                                      (acl2::stobjs-out method-sym wrld)))
        (mv (make-internal-error
             (concatenate 'string
                          "Method has an unsupported signature: "
                          (request->method req)))
            (value-null)
            state))
       (params-inputp (member-eq nil stobjs-in))
       ((unless (iff params-inputp (request->params-presentp req)))
        (mv (make-invalid-params-error
             (concatenate 'string
                          (if params-inputp
                              "Method requires params: "
                            "Method takes no params: ")
                          (request->method req)))
            (value-null)
            state))
       (form (cons method-sym
                   (method-call-args stobjs-in (request->params req))))
       ;; Methods may update user stobjs by design, so we suppress the
       ;; warning trans-eval would otherwise print for each such update.
       ((mv erp stobjs-out/replaced-val state)
        (acl2::trans-eval-no-warning form ctx state t))
       ((when erp)
        (mv (make-internal-error
             (concatenate 'string
                          "Error evaluating method: "
                          (request->method req)))
            (value-null)
            state))
       ;; By the signature check, the first two values are not stobjs,
       ;; so they are not replaced.
       (vals (cdr stobjs-out/replaced-val)))
    (mv (car vals) (cadr vals) state)))


(define process-one ((id idp) (val request+errorp) allowed-methods ctx state)
  :mode :program
  :stobjs state
  :short "Process a single @(see request+error) entry
          and produce a response."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @('val') is an @(see error) (from parse time),
     produces an error response immediately.
     If @('val') is a @(see request) and is a notification,
     returns @('nil') (no response per spec).
     Otherwise dispatches to the method function
     and returns either a success or error response."))
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
  :mode :program
  :stobjs state
  :short "Process all entries in an @(see id-request+error-alist)
          and collect responses."
  :long
  (xdoc::topstring
   (xdoc::p
    "Calls @(see process-one) on each entry.
     Notifications produce no response
     and are omitted from the result list.
     Returns @('(mv erp responses state)'),
     where @('erp') is @('nil') on success
     and @('responses') is the list of response @(see valuep) objects."))
  (if (endp pairs)
      (mv nil nil state)
    (b* (((mv resp state) (process-one (caar pairs) (cdar pairs) allowed-methods ctx state))
         ((mv erp rest state) (process-all (cdr pairs) allowed-methods ctx state)))
      (if resp
          (mv erp (cons resp rest) state)
        (mv erp rest state)))))

(define process-json-rpc-file ((input-file stringp) (output-file stringp) allowed-methods state)
  :mode :program
  :stobjs state
  :short "Process a JSON-RPC 2.0 request file
          and write the response to a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the main entry point for the JSON-RPC interface.
     It reads @('input-file'),
     parses it as a JSON-RPC 2.0 message (single request or batch),
     dispatches each request
     to the appropriate @('JSONRPC') package function,
     and writes the response JSON to @('output-file').")
   (xdoc::p
    "@('allowed-methods') must be either the keyword @(':any')
     (no restriction) or a list of symbols naming the permitted methods,
     e.g. @('(subtract add)').
     Requests for methods not in the list
     are rejected with a method-not-found error.")
   (xdoc::p
    "For a single request, the response is a single JSON Object.
     For a batch request, the response is a JSON Array of response objects.
     If all requests are notifications,
     nothing is written to @('output-file').")
   (xdoc::p
    "Returns @('(mv erp val state)'),
     where @('erp') is @('nil') on success
     and @('val') is the response @(see valuep)."))
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
