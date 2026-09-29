; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/c/transformation/struct-type-split" :dir :system)

(include-book "code-env")
(include-book "params")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ struct-type-split-method
  :parents (c-transformation-json-rpc)
  :short "A JSON-RPC 2.0 method that runs the @(tsee struct-type-split)
          C-to-C transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This @('struct-type-split') method applies
     the @(see struct-type-split) transformation
     to a code ensemble in the @(see code-env),
     and binds the resulting code ensemble to a name.
     The files are read and written by separate methods;
     see @(see input-files-method) and @(see output-files-method).")
   (xdoc::p
    "The request @('params') must be a JSON Object
     with the following members.
     Except for @('\"source\"'), @('\"target\"'), and @('\"overwrite\"'),
     the names match the keyword arguments of @(tsee struct-type-split),
     as strings without leading colons.
     It is an error for a member name to appear more than once.")
   (xdoc::section
    "Request Parameters"
    (xdoc::desc
     "@('\"source\"') &mdash; required"
     (xdoc::p
      "A string naming the code ensemble to transform."))
    (xdoc::desc
     "@('\"target\"') &mdash; required"
     (xdoc::p
      "A string naming the transformed code ensemble.
       It may be the same as @('\"source\"'),
       in which case the transformed code ensemble replaces the original
       (this requires @('\"overwrite\"')).
       If the transformation fails, the environment is unchanged."))
    (xdoc::desc
     "@('\"overwrite\"') &mdash; optional, default @('false')"
     (xdoc::p
      "A boolean that must be @('true')
       if @('\"target\"') is already bound."))
    (xdoc::desc
     "@('\"struct-tag\"')"
     (xdoc::p
      "A string denoting the tag of the struct type to split.
       Exactly one of @('\"struct-tag\"') and @('\"typedef-name\"')
       must be provided."))
    (xdoc::desc
     "@('\"typedef-name\"')"
     (xdoc::p
      "A string denoting a file-scope typedef name
       for the struct type to split.
       Exactly one of @('\"struct-tag\"') and @('\"typedef-name\"')
       must be provided."))
    (xdoc::desc
     "@('\"right-members\"') &mdash; required"
     (xdoc::p
      "A non-empty array of strings denoting the members
       to split off into the new right struct type."))
    (xdoc::desc
     "@('\"filepath\"') &mdash; optional"
     (xdoc::p
      "A string that disambiguates @('\"struct-tag\"')
       when incompatible struct types in different translation units
       share the tag."))
    (xdoc::desc
     "@('\"new-tag\"') &mdash; optional"
     (xdoc::p
      "A string denoting the tag of the new right struct type."))
    (xdoc::desc
     "@('\"safety-checks\"') &mdash; optional, default @('true')"
     (xdoc::p
      "A boolean that, when @('false'),
       disables the transformation's safety checks.")))
   (xdoc::p
    "On success the result is a JSON Object with a single member
     @('\"warnings\"'), an array of warning strings produced by the
     transformation (empty when there are none).")
   (xdoc::p
    "Example request:")
   (xdoc::codeblock
    "{\"jsonrpc\": \"2.0\","
    " \"method\": \"struct-type-split\","
    " \"params\": {\"source\": \"orig\","
    "             \"target\": \"split\","
    "             \"struct-tag\": \"point\","
    "             \"right-members\": [\"z\"],"
    "             \"new-tag\": \"point_right\","
    "             \"safety-checks\": false},"
    " \"id\": 2}"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *struct-type-split-parameter-names*
  '("source"
    "target"
    "overwrite"
    "struct-tag"
    "typedef-name"
    "right-members"
    "filepath"
    "new-tag"
    "safety-checks"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The dispatched method must be in the JSONRPC package: the JSON-RPC interface
; interns the requested method name into that package to find the function.

(define jsonrpc::struct-type-split ((params jsonrpc::structuredp) code-env)
  :returns (mv (erp maybe-errorp) (res json::valuep) code-env)
  :stobjs code-env
  :short "JSON-RPC method implementing the @(tsee c2c::struct-type-split)
          transformation."
  (b* (((reterr) (json::value-null) code-env)
       ((erp members)
        (params->members params *struct-type-split-parameter-names*))
       (obj (json::value-object members))
       ((erp code) (param->source obj code-env))
       ((erp target) (param->target obj code-env))
       ((erp struct-tag-present struct-tag)
        (param->string "struct-tag" obj nil))
       ((erp typedef-name-present typedef-name)
        (param->string "typedef-name" obj nil))
       ((when (iff struct-tag-present typedef-name-present))
        (reterr (jsonrpc::make-invalid-params-error
                 "Exactly one of struct-tag and typedef-name must be provided.")))
       ((erp right-members) (param->string-list "right-members" obj t))
       ((unless (consp right-members))
        (reterr (jsonrpc::make-invalid-params-error
                 "At least one right member must be specified.")))
       ((erp filepath-present filepath) (param->string "filepath" obj nil))
       ((erp new-tag-present new-tag) (param->string "new-tag" obj nil))
       ((erp safety-checks) (param->boolean "safety-checks" obj t))
       (tag? (and struct-tag-present (c$::ident struct-tag)))
       (typedef-name? (and typedef-name-present (c$::ident typedef-name)))
       (filepath? (and filepath-present (c$::filepath filepath)))
       (right-member-idents (c$::string-list-map-ident right-members))
       (new-tag? (and new-tag-present (c$::ident new-tag)))
       ((mv er? code$ warnings)
        (sts-split-code-ensemble
         right-member-idents tag? typedef-name? filepath? new-tag? safety-checks
         code))
       ((when er?)
        (reterr (jsonrpc::make-internal-error
                 (concatenate 'string
                              "struct-type-split error: "
                              (warning-to-string er?)))))
       (code-env (ensembles-put target code$ code-env)))
    (retok (json::value-object
            (list (json::make-member
                   :name "warnings"
                   ;; sts-split-code-ensemble returns warnings in reverse
                   ;; chronological order; present them chronologically.
                   :value (json::value-array
                           (warnings-to-values (reverse warnings))))))
           code-env)))
