; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "code-env")
(include-book "params")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ drop-ensemble-method
  :parents (c-transformation-json-rpc)
  :short "A JSON-RPC 2.0 method that removes a code ensemble
          from the environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This @('drop-ensemble') method unbinds a name in the @(see code-env),
     making its code ensemble available for garbage collection.
     It is an error if the name is not bound.
     To drop several code ensembles, send a batch of requests.")
   (xdoc::p
    "The request @('params') must be a JSON Object
     with the following member.")
   (xdoc::section
    "Request Parameters"
    (xdoc::desc
     "@('\"name\"') &mdash; required"
     (xdoc::p
      "A string naming the code ensemble to drop.")))
   (xdoc::p
    "On success the result is @('null')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The dispatched method must be in the JSONRPC package: the JSON-RPC interface
; interns the requested method name into that package to find the function.

(define jsonrpc::drop-ensemble ((params jsonrpc::structuredp) code-env)
  :returns (mv (erp maybe-errorp) (res json::valuep) code-env)
  :stobjs code-env
  :short "JSON-RPC method that removes a code ensemble from the environment."
  (b* (((reterr) (json::value-null) code-env)
       ((erp members) (params->members params '("name")))
       (obj (json::value-object members))
       ((erp & name) (param->string "name" obj t))
       ((unless (ensembles-boundp name code-env))
        (reterr (jsonrpc::make-invalid-params-error
                 (concatenate 'string "Unbound name: " name))))
       (code-env (ensembles-rem name code-env)))
    (retok (json::value-null) code-env)))
