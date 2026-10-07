; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/c/syntax/output-files" :dir :system)

(include-book "code-env")
(include-book "params")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ output-files-method
  :parents (c-transformation-json-rpc)
  :short "A JSON-RPC 2.0 method that writes a named code ensemble to files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This @('output-files') method writes the code ensemble
     bound to a name in the @(see code-env) to files,
     as @(tsee c$::output-files) does.
     The environment is unchanged.")
   (xdoc::p
    "The request @('params') must be a JSON Object
     with the following members.")
   (xdoc::section
    "Request Parameters"
    (xdoc::desc
     "@('\"input-ensemble\"') &mdash; required"
     (xdoc::p
      "A string naming the code ensemble to write."))
    (xdoc::desc
     "@('\"base-dir\"') &mdash; optional, default @('\".\"')"
     (xdoc::p
      "A string denoting the base directory for the files,
       as the @(':base-dir') input of @(tsee c$::output-files).")))
   (xdoc::p
    "On success the result is @('null').")
   (xdoc::p
    "Example request:")
   (xdoc::codeblock
    "{\"jsonrpc\": \"2.0\","
    " \"method\": \"output-files\","
    " \"params\": {\"input-ensemble\": \"split\","
    "             \"base-dir\": \"out\"},"
    " \"id\": 3}"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *output-files-parameter-names*
  '("input-ensemble"
    "base-dir"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The dispatched method must be in the JSONRPC package: the JSON-RPC interface
; interns the requested method name into that package to find the function.

(define jsonrpc::output-files ((params jsonrpc::structuredp) code-env state)
  :returns (mv (erp maybe-errorp) (res json::valuep) state)
  :stobjs (code-env state)
  :short "JSON-RPC method that writes a named code ensemble to files."
  (b* (((reterr) (json::value-null) state)
       ((erp members) (params->members params *output-files-parameter-names*))
       (obj (json::value-object members))
       ((erp code) (param->input-ensemble obj code-env))
       ((erp base-dir) (param->base-dir obj))
       ((mv erp state)
        (c$::output-files-prog-fn code (list :base-dir base-dir) state))
       ((when erp)
        (reterr
         (jsonrpc::make-internal-error
          (if (msgp erp)
              (concatenate 'string
                           "Error processing output files: "
                           (warning-to-string erp))
            "Error processing output files.")))))
    (retok (json::value-null) state)))
