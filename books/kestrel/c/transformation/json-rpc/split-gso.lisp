; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/c/transformation/split-gso" :dir :system)

(include-book "code-env")
(include-book "params")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ split-gso-method
  :parents (c-transformation-json-rpc)
  :short "A JSON-RPC 2.0 method that runs the @(tsee split-gso)
          C-to-C transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This @('split-gso') method splits a global struct object,
     i.e. a file-scope object of a struct type,
     into two objects of two new struct types,
     dividing the struct members between them.
     Accesses to the members of the original object
     are redirected to the corresponding new object.
     See @(see split-gso) for the exact conditions and limitations.")
   (xdoc::p
    "The @('\"input-ensemble\"'), @('\"output-ensemble\"'), and @('\"overwrite\"') parameters
     are as described in @(see c-transformation-json-rpc).
     The other parameters are as follows.")
   (xdoc::section
    "Request Parameters"
    (xdoc::desc
     "@('\"object-name\"') &mdash; required"
     (xdoc::p
      "A string: the name of the object to split."))
    (xdoc::desc
     "@('\"split-members\"') &mdash; required"
     (xdoc::p
      "An array of strings: the members to move into the second new object.
       The other members go into the first new object."))
    (xdoc::desc
     "@('\"object-filepath\"') &mdash; optional"
     (xdoc::p
      "A string: the file declaring the object,
       required if the object has internal linkage."))
    (xdoc::desc
     "@('\"new-object1\"'), @('\"new-object2\"') &mdash; optional"
     (xdoc::p
      "Strings: the names of the two new objects.
       By default, fresh names are generated."))
    (xdoc::desc
     "@('\"new-type1\"'), @('\"new-type2\"') &mdash; optional"
     (xdoc::p
      "Strings: the tags of the two new struct types.
       By default, fresh tags are generated.")))
   (xdoc::p
    "On success the result is @('null').")
   (xdoc::p
    "Example request:")
   (xdoc::codeblock
    "{\"jsonrpc\": \"2.0\","
    " \"method\": \"split-gso\","
    " \"params\": {\"input-ensemble\": \"orig\","
    "             \"output-ensemble\": \"split\","
    "             \"object-name\": \"foo_data\","
    "             \"split-members\": [\"a2\", \"a2_size\"]},"
    " \"id\": 2}"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *split-gso-parameter-names*
  '("input-ensemble"
    "output-ensemble"
    "overwrite"
    "object-name"
    "split-members"
    "object-filepath"
    "new-object1"
    "new-object2"
    "new-type1"
    "new-type2"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The dispatched method must be in the JSONRPC package: the JSON-RPC interface
; interns the requested method name into that package to find the function.

(define jsonrpc::split-gso ((params jsonrpc::structuredp) code-env)
  :returns (mv (erp maybe-errorp) (res json::valuep) code-env)
  :stobjs code-env
  :short "JSON-RPC method implementing the @(tsee c2c::split-gso)
          transformation."
  (b* (((reterr) (json::value-null) code-env)
       ((erp members) (params->members params *split-gso-parameter-names*))
       (obj (json::value-object members))
       ((erp code) (param->input-ensemble obj code-env))
       ((erp output-name) (param->output-ensemble obj code-env))
       ((erp & object-name) (param->string "object-name" obj t))
       ((erp split-members) (param->string-list "split-members" obj t))
       ((erp object-filepath?) (param->filepath-option "object-filepath" obj))
       ((erp new-object1?) (param->ident-option "new-object1" obj))
       ((erp new-object2?) (param->ident-option "new-object2" obj))
       ((erp new-type1?) (param->ident-option "new-type1" obj))
       ((erp new-type2?) (param->ident-option "new-type2" obj))
       ((mv er? code$)
        (split-gso-code-ensemble object-filepath?
                                 (c$::ident object-name)
                                 new-object1?
                                 new-object2?
                                 new-type1?
                                 new-type2?
                                 (c$::string-list-map-ident split-members)
                                 code))
       ((when er?)
        (reterr (jsonrpc::make-internal-error
                 (concatenate 'string
                              "split-gso error: "
                              (warning-to-string er?)))))
       ((mv er? code$) (revalidate-code-ensemble code$))
       ((when er?)
        (reterr (jsonrpc::make-internal-error (warning-to-string er?))))
       (code-env (ensembles-put output-name code$ code-env)))
    (retok (json::value-null) code-env)))
