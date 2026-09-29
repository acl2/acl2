; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/c/transformation/wrap-fn" :dir :system)

(include-book "code-env")
(include-book "params")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ wrap-fn-method
  :parents (c-transformation-json-rpc)
  :short "A JSON-RPC 2.0 method that runs the @(tsee wrap-fn)
          C-to-C transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This @('wrap-fn') method introduces function wrappers:
     for each target function, a new function (with internal linkage)
     that just calls the target,
     and replaces the direct calls of the target with calls of the wrapper.
     See @(see wrap-fn) for the exact conditions and limitations.")
   (xdoc::p
    "The @('\"input-ensemble\"'), @('\"output-ensemble\"'), and @('\"overwrite\"') parameters
     are as described in @(see c-transformation-json-rpc).
     The other parameter is as follows.")
   (xdoc::section
    "Request Parameters"
    (xdoc::desc
     "@('\"targets\"') &mdash; required"
     (xdoc::p
      "Either an array of strings, the names of the functions to wrap,
       or an object whose member names are the names of the functions to wrap
       and whose member values are the suggested names of their wrappers,
       as strings, or @('false') or @('null') for generated names.
       With an array, all the wrapper names are generated.")))
   (xdoc::p
    "On success the result is @('null').")
   (xdoc::p
    "Example request:")
   (xdoc::codeblock
    "{\"jsonrpc\": \"2.0\","
    " \"method\": \"wrap-fn\","
    " \"params\": {\"input-ensemble\": \"orig\","
    "             \"output-ensemble\": \"wrapped\","
    "             \"targets\": {\"foo\": \"foo_wrapper\", \"bar\": null}},"
    " \"id\": 2}"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *wrap-fn-parameter-names*
  '("input-ensemble"
    "output-ensemble"
    "overwrite"
    "targets"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define members->string-string-option-alist ((members json::member-listp))
  :returns (mv (erp maybe-errorp) (alist string-string-option-alistp))
  :short "Convert the members of the @('\"targets\"') object
          to an alist from function names to optional wrapper names."
  (b* (((reterr) nil)
       ((when (endp members)) (retok nil))
       (name (json::member->name (car members)))
       (value (json::member->value (car members)))
       ((erp wrapper?)
        (cond ((json::value-case value :string)
               (retok (json::value-string->get value)))
              ((or (json::value-case value :false)
                   (json::value-case value :null))
               (retok nil))
              (t (reterr
                  (jsonrpc::make-invalid-params-error
                   (warning-to-string
                    (msg "Entry ~x0 of parameter ~x1 must be a string, ~
                          false, or null."
                         name
                         "targets")))))))
       ((erp rest) (members->string-string-option-alist (cdr members))))
    (retok (cons (cons name wrapper?) rest))))

(define param->wrap-fn-targets ((obj json::valuep))
  :guard (json::value-case obj :object)
  :returns (mv (erp maybe-errorp) (targets ident-ident-option-mapp))
  :short "Read the @('\"targets\"') parameter."
  (b* (((reterr) nil)
       ((mv presentp v) (get-member "targets" obj))
       ((unless presentp)
        (reterr (jsonrpc::make-invalid-params-error
                 "Missing required parameter: targets")))
       ((when (json::value-case v :array))
        (b* (((mv bad-index names)
              (value-list->strings (json::value-array->elements v)))
             ((when bad-index)
              (reterr
               (jsonrpc::make-invalid-params-error
                (warning-to-string
                 (msg "Element at index ~x0 of parameter ~x1 must be a string."
                      bad-index
                      "targets"))))))
          (retok (string-list-to-ident-ident-option-map names))))
       ((when (json::value-case v :object))
        (b* ((members (json::value-object->members v))
             (dup (members-first-duplicate members))
             ((when dup)
              (reterr (jsonrpc::make-invalid-params-error
                       (concatenate 'string "Duplicate targets entry: " dup))))
             ((erp alist) (members->string-string-option-alist members)))
          (retok (string-string-option-alist-to-ident-ident-option-map
                  alist)))))
    (reterr (jsonrpc::make-invalid-params-error
             "Parameter targets must be an array of strings or an object."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The dispatched method must be in the JSONRPC package: the JSON-RPC interface
; interns the requested method name into that package to find the function.

(define jsonrpc::wrap-fn ((params jsonrpc::structuredp) code-env)
  :returns (mv (erp maybe-errorp) (res json::valuep) code-env)
  :stobjs code-env
  :short "JSON-RPC method implementing the @(tsee c2c::wrap-fn)
          transformation."
  (b* (((reterr) (json::value-null) code-env)
       ((erp members) (params->members params *wrap-fn-parameter-names*))
       (obj (json::value-object members))
       ((erp code) (param->input-ensemble obj code-env))
       ((erp output-name) (param->output-ensemble obj code-env))
       ((erp targets) (param->wrap-fn-targets obj))
       ;; The transformation re-validates its output,
       ;; which is therefore annotated.
       ((mv er? code$) (code-ensemble-wrap-fn-multiple code targets))
       ((when er?)
        (reterr (jsonrpc::make-internal-error
                 (concatenate 'string
                              "wrap-fn error: "
                              (warning-to-string er?)))))
       (code-env (ensembles-put output-name code$ code-env)))
    (retok (json::value-null) code-env)))
