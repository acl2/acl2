; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/c/transformation/simpadd0" :dir :system)

(include-book "code-env")
(include-book "params")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ simpadd0-method
  :parents (c-transformation-json-rpc)
  :short "A JSON-RPC 2.0 method that runs the @(tsee simpadd0)
          C-to-C transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This @('simpadd0') method simplifies expressions of the form
     @('E + 0') to @('E'), for certain expressions @('E') of type @('int').
     It is a simple proof-of-concept transformation.
     See @(see simpadd0) for the exact conditions.
     The event form of the transformation also generates proofs of equivalence;
     this method does not return them.")
   (xdoc::p
    "The only parameters are
     @('\"input-ensemble\"'), @('\"output-ensemble\"'), and @('\"overwrite\"'),
     as described in @(see c-transformation-json-rpc).")
   (xdoc::p
    "On success the result is @('null').")
   (xdoc::p
    "Example request:")
   (xdoc::codeblock
    "{\"jsonrpc\": \"2.0\","
    " \"method\": \"simpadd0\","
    " \"params\": {\"input-ensemble\": \"orig\","
    "             \"output-ensemble\": \"simplified\"},"
    " \"id\": 2}"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *simpadd0-parameter-names*
  '("input-ensemble"
    "output-ensemble"
    "overwrite"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The dispatched method must be in the JSONRPC package: the JSON-RPC interface
; interns the requested method name into that package to find the function.

(define jsonrpc::simpadd0 ((params jsonrpc::structuredp) code-env)
  :returns (mv (erp maybe-errorp) (res json::valuep) code-env)
  :stobjs code-env
  :short "JSON-RPC method implementing the @(tsee c2c::simpadd0)
          transformation."
  (b* (((reterr) (json::value-null) code-env)
       ((erp members) (params->members params *simpadd0-parameter-names*))
       (obj (json::value-object members))
       ((erp code) (param->input-ensemble obj code-env))
       ((erp output-name) (param->output-ensemble obj code-env))
       ;; The transformation requires unambiguous code, which validated code
       ;; is, but that is not statically known, so we check it here.
       ((unless (code-ensemble-unambp code))
        (reterr (jsonrpc::make-internal-error
                 "Internal error: the input ensemble is ambiguous.")))
       ;; The transformation generates theorems, whose names are based on
       ;; :const-new; since we do not return them, any name will do.
       (gin (make-gin :ienv (code-ensemble->ienv code)
                      :const-new '*simpadd0-json-rpc*
                      :vartys nil
                      :events nil
                      :thm-index 1))
       ((mv code$ &) (simpadd0-code-ensemble code gin))
       (code-env (ensembles-put output-name code$ code-env)))
    (retok (json::value-null) code-env)))
