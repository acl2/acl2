; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/c/syntax/input-files" :dir :system)

(include-book "code-env")
(include-book "params")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ input-files-method
  :parents (c-transformation-json-rpc)
  :short "A JSON-RPC 2.0 method that reads C files
          into a named code ensemble."
  :long
  (xdoc::topstring
   (xdoc::p
    "This @('input-files') method reads, parses, disambiguates,
     and validates C files, as @(tsee c$::input-files) does,
     and binds the resulting code ensemble to a name
     in the @(see code-env).")
   (xdoc::p
    "The request @('params') must be a JSON Object
     with the following members.
     Except for @('\"output-ensemble\"') and @('\"overwrite\"'),
     the names match the keyword arguments of @(tsee c$::input-files),
     as strings without leading colons.")
   (xdoc::section
    "Request Parameters"
    (xdoc::desc
     "@('\"output-ensemble\"') &mdash; required"
     (xdoc::p
      "A string naming the code ensemble to create."))
    (xdoc::desc
     "@('\"overwrite\"') &mdash; optional, default @('false')"
     (xdoc::p
      "A boolean that must be @('true')
       if @('\"output-ensemble\"') is already bound."))
    (xdoc::desc
     "@('\"files\"') &mdash; required"
     (xdoc::p
      "An array of strings denoting the files to read,
       relative to @('\"base-dir\"')."))
    (xdoc::desc
     "@('\"base-dir\"') &mdash; optional, default @('\".\"')"
     (xdoc::p
      "A string denoting the base directory of the files."))
    (xdoc::desc
     "@('\"preprocess\"') &mdash; optional, default @('\"auto\"')"
     (xdoc::p
      "A boolean or string controlling preprocessing:
       @('false') disables it, @('true') preprocesses with auto-detection
       (like the default), and a string names the preprocessor."))
    (xdoc::desc
     "@('\"preprocess-args\"') &mdash; optional"
     (xdoc::p
      "Either an array of strings denoting extra arguments
       passed to the preprocessor for every file,
       or an object whose member names are file paths
       and whose member values are arrays of strings
       denoting the extra arguments for the corresponding files."))
    (xdoc::desc
     "@('\"extensions\"') &mdash; optional, default @('\"gcc\"')"
     (xdoc::p
      "A string or boolean:
       @('\"gcc\"'), @('\"clang\"'), or @('false') to disable extensions.")))
   (xdoc::p
    "On success the result is @('null').")
   (xdoc::p
    "Example request:")
   (xdoc::codeblock
    "{\"jsonrpc\": \"2.0\","
    " \"method\": \"input-files\","
    " \"params\": {\"output-ensemble\": \"orig\","
    "             \"base-dir\": \"input-files\","
    "             \"files\": [\"test1.c\"],"
    "             \"preprocess\": false},"
    " \"id\": 1}"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *input-files-parameter-names*
  '("output-ensemble"
    "overwrite"
    "files"
    "base-dir"
    "preprocess"
    "preprocess-args"
    "extensions"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The dispatched method must be in the JSONRPC package: the JSON-RPC interface
; interns the requested method name into that package to find the function.

(define jsonrpc::input-files ((params jsonrpc::structuredp) code-env state)
  :returns (mv (erp maybe-errorp) (res json::valuep) code-env state)
  :stobjs (code-env state)
  :short "JSON-RPC method that reads C files into a named code ensemble."
  (b* (((reterr) (json::value-null) code-env state)
       ((erp members) (params->members params *input-files-parameter-names*))
       (obj (json::value-object members))
       ((erp output-name) (param->output-ensemble obj code-env))
       ((erp files) (param->string-list "files" obj t))
       ((erp base-dir) (param->base-dir obj))
       ((erp preprocess) (param->preprocess obj))
       ((erp preprocess-args) (param->preprocess-args obj))
       ((erp ienv) (param->ienv obj))
       ((mv erp code state)
        (c$::input-files-prog-fn t files base-dir preprocess preprocess-args
                                 nil nil :validate nil nil nil ienv state))
       ((when erp)
        (reterr
         (jsonrpc::make-internal-error
          (if (msgp erp)
              (concatenate 'string
                           "Error processing input files: "
                           (warning-to-string erp))
            "Error processing input files."))))
       ;; input-files-prog-fn with :validate produces an annotated code
       ;; ensemble, but that is not statically guaranteed, so we check it here.
       ((unless (code-ensemble-annop code))
        (reterr (jsonrpc::make-internal-error
                 "Internal error: the input code ensemble is not annotated.")))
       (code-env (ensembles-put output-name code code-env)))
    (retok (json::value-null) code-env state)))
