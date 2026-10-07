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

(defxdoc+ list-ensembles-method
  :parents (c-transformation-json-rpc)
  :short "A JSON-RPC 2.0 method that lists the code ensembles
          in the environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This @('list-ensembles') method returns the names
     of the code ensembles in the @(see code-env),
     as a JSON Array of strings, sorted in @(tsee lexorder).
     The request has no @('params')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define names-to-values (names)
  :returns (vals json::value-listp)
  :short "Turn the string names in a list into JSON string values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The names in the environment are always strings,
     but the logic does not constrain the keys of a hash table,
     so we skip any non-string key."))
  (b* (((when (atom names)) nil)
       (name (car names)))
    (if (stringp name)
        (cons (json::value-string name)
              (names-to-values (cdr names)))
      (names-to-values (cdr names)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The dispatched method must be in the JSONRPC package: the JSON-RPC interface
; interns the requested method name into that package to find the function.

(define jsonrpc::list-ensembles (code-env)
  :returns (mv (erp maybe-errorp) (res json::valuep))
  :stobjs code-env
  :short "JSON-RPC method that lists the code ensembles in the environment."
  (mv nil (json::value-array (names-to-values (ensembles-keys code-env)))))
