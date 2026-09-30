; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/c/transformation/split-fn" :dir :system)

(include-book "code-env")
(include-book "params")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ split-fn-method
  :parents (c-transformation-json-rpc)
  :short "A JSON-RPC 2.0 method that runs the @(tsee split-fn)
          C-to-C transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This @('split-fn') method splits a function in two:
     the body of the function is truncated at a split point,
     where it calls a new function containing the rest of the body.
     Values needed by the new function are passed by pointer.
     See @(see split-fn) for the exact conditions and limitations.")
   (xdoc::p
    "The @('\"input-ensemble\"'), @('\"output-ensemble\"'),
     and @('\"overwrite\"') parameters
     are as described in @(see c-transformation-json-rpc).
     The other parameters are as follows.")
   (xdoc::section
    "Request Parameters"
    (xdoc::desc
     "@('\"target\"') &mdash; required"
     (xdoc::p
      "A string: the name of the function to split."))
    (xdoc::desc
     "@('\"new-fn\"') &mdash; required"
     (xdoc::p
      "A string: the name of the new function."))
    (xdoc::desc
     "@('\"split-point\"') &mdash; required"
     (xdoc::p
      "A natural number: the number of top-level statements and declarations
       of the function body that stay in the original function.")))
   (xdoc::p
    "On success the result is @('null').")
   (xdoc::p
    "Example request:")
   (xdoc::codeblock
    "{\"jsonrpc\": \"2.0\","
    " \"method\": \"split-fn\","
    " \"params\": {\"input-ensemble\": \"orig\","
    "             \"output-ensemble\": \"split\","
    "             \"target\": \"foo\","
    "             \"new-fn\": \"foo_new\","
    "             \"split-point\": 1},"
    " \"id\": 2}"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *split-fn-parameter-names*
  '("input-ensemble"
    "output-ensemble"
    "overwrite"
    "target"
    "new-fn"
    "split-point"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The dispatched method must be in the JSONRPC package: the JSON-RPC interface
; interns the requested method name into that package to find the function.

(define jsonrpc::split-fn ((params jsonrpc::structuredp) code-env)
  :returns (mv (erp maybe-errorp) (res json::valuep) code-env)
  :stobjs code-env
  :short "JSON-RPC method implementing the @(tsee c2c::split-fn)
          transformation."
  (b* (((reterr) (json::value-null) code-env)
       ((erp members) (params->members params *split-fn-parameter-names*))
       (obj (json::value-object members))
       ((erp code) (param->input-ensemble obj code-env))
       ((erp output-name) (param->output-ensemble obj code-env))
       ((erp & target) (param->string "target" obj t))
       ((erp & new-fn) (param->string "new-fn" obj t))
       ((erp split-point) (param->natural "split-point" obj))
       ((mv er? code$)
        (split-fn-code-ensemble (c$::ident target)
                                (c$::ident new-fn)
                                code
                                split-point))
       ((when er?)
        (reterr (jsonrpc::make-internal-error
                 (concatenate 'string
                              "split-fn error: "
                              (warning-to-string er?)))))
       ((mv er? code$) (revalidate-code-ensemble code$))
       ((when er?)
        (reterr (jsonrpc::make-internal-error (warning-to-string er?))))
       (code-env (ensembles-put output-name code$ code-env)))
    (retok (json::value-null) code-env)))
