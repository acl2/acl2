; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/c/transformation/add-section-attr" :dir :system)

(include-book "code-env")
(include-book "params")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ add-section-attr-method
  :parents (c-transformation-json-rpc)
  :short "A JSON-RPC 2.0 method that runs the @(tsee add-section-attr)
          C-to-C transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This @('add-section-attr') method adds GCC ``section'' attributes
     to the declarations of given file-scope functions and objects,
     so that they are placed in given sections.
     See @(see add-section-attr) for the exact conditions.")
   (xdoc::p
    "The @('\"input-ensemble\"'), @('\"output-ensemble\"'), and @('\"overwrite\"') parameters
     are as described in @(see c-transformation-json-rpc).
     The other parameter is as follows.")
   (xdoc::section
    "Request Parameters"
    (xdoc::desc
     "@('\"attrs\"') &mdash; required"
     (xdoc::p
      "An array of objects, each with two members:")
     (xdoc::ul
      (xdoc::li
       "@('\"target\"'): an object identifying a function or object,
        with a member @('\"ident\"'), a string, the name,
        and an optional member @('\"filepath\"'), a string or @('null'),
        the file declaring it,
        which is required if it has internal linkage.")
      (xdoc::li
       "@('\"section\"'): a string, the section name."))))
   (xdoc::p
    "On success the result is @('null').")
   (xdoc::p
    "Example request:")
   (xdoc::codeblock
    "{\"jsonrpc\": \"2.0\","
    " \"method\": \"add-section-attr\","
    " \"params\": {\"input-ensemble\": \"orig\","
    "             \"output-ensemble\": \"sectioned\","
    "             \"attrs\": [{\"target\": {\"filepath\": \"file9.c\","
    "                                     \"ident\": \"foo\"},"
    "                         \"section\": \"foosection\"},"
    "                        {\"target\": {\"ident\": \"bar\"},"
    "                         \"section\": \"barsection\"}]},"
    " \"id\": 2}"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *add-section-attr-parameter-names*
  '("input-ensemble"
    "output-ensemble"
    "overwrite"
    "attrs"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value->qualified-ident ((val json::valuep))
  :returns (mv (erp maybe-errorp) (qident? qualified-ident-optionp))
  :short "Read the @('\"target\"') of an element of @('\"attrs\"')."
  (b* (((reterr) nil)
       ((unless (json::value-case val :object))
        (reterr (jsonrpc::make-invalid-params-error
                 "Each target in attrs must be an object.")))
       (erp (check-member-names (json::value-object->members val)
                                '("filepath" "ident")
                                "attrs target member"))
       ((when erp) (reterr erp))
       ((erp & ident) (param->string "ident" val t))
       ((mv presentp filepath) (get-member "filepath" val))
       ((erp filepath?)
        (cond ((or (not presentp)
                   (json::value-case filepath :null))
               (retok nil))
              ((json::value-case filepath :string)
               (retok (c$::filepath (json::value-string->get filepath))))
              (t (reterr (jsonrpc::make-invalid-params-error
                          "Each filepath in attrs must be a string or null."))))))
    (retok (make-qualified-ident :filepath? filepath?
                                 :ident (c$::ident ident)))))

(define values->section-attrs ((vals json::value-listp))
  :returns (mv (erp maybe-errorp) (attrs qualified-ident-string-alistp))
  :short "Read the elements of @('\"attrs\"')."
  (b* (((reterr) nil)
       ((when (endp vals)) (retok nil))
       (val (car vals))
       ((unless (json::value-case val :object))
        (reterr (jsonrpc::make-invalid-params-error
                 "Each element of attrs must be an object.")))
       (erp (check-member-names (json::value-object->members val)
                                '("target" "section")
                                "attrs member"))
       ((when erp) (reterr erp))
       ((erp & section) (param->string "section" val t))
       ((mv presentp target) (get-member "target" val))
       ((unless presentp)
        (reterr (jsonrpc::make-invalid-params-error
                 "Missing target in an element of attrs.")))
       ((erp qident?) (value->qualified-ident target))
       ((unless qident?)
        (reterr (jsonrpc::make-internal-error
                 "Internal error: no qualified identifier.")))
       ((erp rest) (values->section-attrs (cdr vals))))
    (retok (cons (cons qident? section) rest))))

(define param->section-attrs ((obj json::valuep))
  :guard (json::value-case obj :object)
  :returns (mv (erp maybe-errorp) (attrs qualified-ident-string-alistp))
  :short "Read the @('\"attrs\"') parameter."
  (b* (((reterr) nil)
       ((mv presentp v) (get-member "attrs" obj))
       ((unless presentp)
        (reterr (jsonrpc::make-invalid-params-error
                 "Missing required parameter: attrs")))
       ((unless (json::value-case v :array))
        (reterr (jsonrpc::make-invalid-params-error
                 "Parameter attrs must be an array."))))
    (values->section-attrs (json::value-array->elements v))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The dispatched method must be in the JSONRPC package: the JSON-RPC interface
; interns the requested method name into that package to find the function.

(define jsonrpc::add-section-attr ((params jsonrpc::structuredp) code-env)
  :returns (mv (erp maybe-errorp) (res json::valuep) code-env)
  :stobjs code-env
  :short "JSON-RPC method implementing the @(tsee c2c::add-section-attr)
          transformation."
  (b* (((reterr) (json::value-null) code-env)
       ((erp members)
        (params->members params *add-section-attr-parameter-names*))
       (obj (json::value-object members))
       ((erp code) (param->input-ensemble obj code-env))
       ((erp output-name) (param->output-ensemble obj code-env))
       ((erp attrs) (param->section-attrs obj))
       ((mv er? code$) (code-ensemble-add-section-attr code attrs))
       ((when er?)
        (reterr (jsonrpc::make-internal-error
                 (concatenate 'string
                              "add-section-attr error: "
                              (warning-to-string er?)))))
       ((mv er? code$) (revalidate-code-ensemble code$))
       ((when er?)
        (reterr (jsonrpc::make-internal-error (warning-to-string er?))))
       (code-env (ensembles-put output-name code$ code-env)))
    (retok (json::value-null) code-env)))
