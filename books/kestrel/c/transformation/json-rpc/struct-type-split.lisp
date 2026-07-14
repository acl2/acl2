; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/jsonrpc/types" :dir :system)
(include-book "kestrel/json/top" :dir :system)
(include-book "kestrel/utilities/print-to-string" :dir :system)
(include-book "kestrel/c/syntax/input-files" :dir :system)
(include-book "kestrel/c/syntax/output-files" :dir :system)
(include-book "kestrel/c/transformation/struct-type-split" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable* c$::abstract-syntax-annop-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define maybe-errorp (x)
  :returns (yes/no booleanp)
  :parents (jsonrpc::error)
  :short "Recognize an optional @(see jsonrpc::error)."
  (or (not x)
      (jsonrpc::errorp x)))

(defrulel maybe-errorp-when-errorp
  (implies (jsonrpc::errorp x)
           (maybe-errorp x))
  :enable maybe-errorp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ struct-type-split-method
  :parents (c-transformation-json-rpc)
  :short "A JSON-RPC 2.0 method that runs the @(tsee struct-type-split)
          C-to-C transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a "
    (xdoc::seetopic "jsonrpc::jsonrpc" "JSON-RPC 2.0")
    " @('struct-type-split') method, suitable for use as one of the
     @('allowed-methods') of @(see jsonrpc::run-jsonrpc-server) (or @(see
     jsonrpc::process-json-rpc-file)).  It exposes the @(see struct-type-split)
     transformation over JSON-RPC, mirroring the
     command-line/JSON interface in @('kestrel/c/transformation/command-line').")
   (xdoc::p
    "The request @('params') must be a JSON Object (by-name parameters) with
     the following members.  The names match the keyword arguments of @(tsee
     struct-type-split) and of @(tsee c$::input-files) / @(tsee
     c$::output-files), but as strings without leading colons.
     It is an error for a member name to appear more than once.")
   (xdoc::section
    "Request Parameters"
    (xdoc::desc
     "@('\"old-dir\"') &mdash; required"
     (xdoc::p
      "A string denoting the base directory of the input files."))
    (xdoc::desc
     "@('\"new-dir\"') &mdash; required"
     (xdoc::p
      "A string denoting the base directory for the output files."))
    (xdoc::desc
     "@('\"files\"') &mdash; required"
     (xdoc::p
      "An array of strings denoting the input files to read,
       relative to @('\"old-dir\"')."))
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
     "@('\"unsafe\"') &mdash; optional, default @('false')"
     (xdoc::p
      "A boolean that, when @('true'), disables the transformation's safety
       checks."))
    (xdoc::desc
     "@('\"preprocess\"') &mdash; optional, default @('\"auto\"')"
     (xdoc::p
      "A boolean or string controlling preprocessing:
       @('false') disables it, @('true') preprocesses with auto-detection
       (like the default), and a string names the preprocessor."))
    (xdoc::desc
     "@('\"preprocess-args\"') &mdash; optional"
     (xdoc::p
      "Either an array of strings denoting extra arguments passed to the
       preprocessor for every file, or an object whose member names are file
       paths and whose member values are arrays of strings denoting the extra
       arguments for the corresponding files."))
    (xdoc::desc
     "@('\"extensions\"') &mdash; optional, default @('\"gcc\"')"
     (xdoc::p
      "A string or boolean:
       @('\"gcc\"'), @('\"clang\"'), or @('false') to disable extensions.")))
   (xdoc::p
    "On success the result is a JSON Object with a single member
     @('\"warnings\"'), an array of warning strings produced by the
     transformation (empty when there are none).  Success is implicit in the
     absence of a JSON-RPC error.")
   (xdoc::p
    "Example request:")
   (xdoc::codeblock
    "{\"jsonrpc\": \"2.0\","
    " \"method\": \"struct-type-split\","
    " \"params\": {\"old-dir\": \"input-files\","
    "             \"new-dir\": \"output\","
    "             \"files\": [\"test1.c\"],"
    "             \"struct-tag\": \"point\","
    "             \"right-members\": [\"z\"],"
    "             \"new-tag\": \"point_right\","
    "             \"unsafe\": true,"
    "             \"preprocess\": false},"
    " \"id\": 1}"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define warning-to-string (msg)
  :returns (str stringp)
  :short "Render a transformation warning/error message to a string."
  (mv-let (col str)
    ;; ec-call is necessary because acl2::fmt1-to-string is not guard-verified.
    (ec-call (acl2::fmt1-to-string-fn "~@0" (list (cons #\0 msg)) 0 nil
                                      '((fmt-soft-right-margin . 10000)
                                        (fmt-hard-right-margin . 10000))))
    (declare (ignore col))
    (if (stringp str) str "")))

(define warnings-to-values ((warnings true-listp))
  :returns (vals json::value-listp)
  :short "Render a list of warnings to a list of JSON string values."
  (if (endp warnings)
      nil
    (cons (json::value-string (warning-to-string (car warnings)))
          (warnings-to-values (cdr warnings)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-member ((name stringp) (obj json::valuep))
  :guard (json::value-case obj :object)
  :returns (mv (presentp booleanp) (val json::valuep))
  :short "Retrieve the (first) value associated with a member name."
  :long
  (xdoc::topstring-p
   "Returns @('(mv presentp val)'); @('val') is @(tsee json::value-null) when
    the member is absent.")
  (b* ((vals (json::object-member-values name obj)))
    (if (consp vals)
        (mv t (json::value-fix (car vals)))
      (mv nil (json::value-null)))))

(define param->string ((name stringp) (obj json::valuep) (requiredp booleanp))
  :guard (json::value-case obj :object)
  :returns (mv (erp maybe-errorp) (presentp booleanp) (str stringp))
  :short "Read a string-valued parameter."
  :long
  (xdoc::topstring-p
   "Returns @('(mv erp presentp str)').  @('str') is the empty string when the
    parameter is absent (in which case @('presentp') is @('nil')).")
  (b* (((reterr) nil "")
       ((mv presentp v) (get-member name obj))
       ((unless presentp)
        (if requiredp
            (reterr (jsonrpc::make-invalid-params-error
                     (concatenate 'string "Missing required parameter: " name)))
          (retok nil "")))
       ((unless (json::value-case v :string))
        (reterr (jsonrpc::make-invalid-params-error
                 (concatenate 'string "Parameter " name " must be a string.")))))
    (retok t (json::value-string->get v))))

(define value-list->strings ((vals json::value-listp))
  :returns (mv (erp booleanp) (strs string-listp))
  :short "Convert a list of JSON values to a list of strings,
          failing if any value is not a string."
  (b* (((reterr) nil)
       ((when (endp vals)) (retok nil))
       (v (car vals))
       ((unless (json::value-case v :string)) (reterr t))
       ((erp rest) (value-list->strings (cdr vals))))
    (retok (cons (json::value-string->get v) rest))))

(define param->string-list ((name stringp) (obj json::valuep) (requiredp booleanp))
  :guard (json::value-case obj :object)
  :returns (mv (erp maybe-errorp) (strs string-listp))
  :short "Read a parameter that is an array of strings."
  (b* (((reterr) nil)
       ((mv presentp v) (get-member name obj))
       ((unless presentp)
        (if requiredp
            (reterr (jsonrpc::make-invalid-params-error
                     (concatenate 'string "Missing required parameter: " name)))
          (retok nil)))
       ((unless (json::value-case v :array))
        (reterr (jsonrpc::make-invalid-params-error
                 (concatenate 'string
                              "Parameter " name " must be an array of strings."))))
       ((mv erp strs) (value-list->strings (json::value-array->elements v)))
       ((when erp)
        (reterr (jsonrpc::make-invalid-params-error
                 (concatenate 'string
                              "Parameter " name " must be an array of strings.")))))
    (retok strs)))

(define param->boolean ((name stringp)
                        (obj json::valuep)
                        (default booleanp))
  :guard (json::value-case obj :object)
  :returns (mv (erp maybe-errorp) (val booleanp))
  :short "Read an optional boolean-valued parameter."
  (b* ((default$ (and default t))
       ((reterr) default$)
       ((mv presentp v) (get-member name obj))
       ((unless presentp) (retok default$))
       ((when (json::value-case v :true)) (retok t))
       ((when (json::value-case v :false)) (retok nil)))
    (reterr (jsonrpc::make-invalid-params-error
             (concatenate 'string
                          "Parameter " name " must be a boolean.")))))

(define members->names ((members json::member-listp))
  :returns (names string-listp)
  :short "The list of member names in a JSON object member list."
  (if (endp members)
      nil
    (cons (json::member->name (car members))
          (members->names (cdr members)))))

(define members-first-duplicate ((members json::member-listp))
  :returns (dup acl2::maybe-stringp)
  :short "The first member name that occurs more than once, or @('nil')."
  (if (endp members)
      nil
    (if (member-equal (json::member->name (car members))
                      (members->names (cdr members)))
        (json::member->name (car members))
      (members-first-duplicate (cdr members)))))

(define members->string-stringlist-map ((members json::member-listp))
  :returns (mv (erp maybe-errorp)
               (map acl2::string-stringlist-mapp))
  :short "Convert JSON object members to a string-to-string-list omap."
  (b* (((reterr) nil)
       ((when (endp members)) (retok nil))
       (member (car members))
       (name (json::member->name member))
       (value (json::member->value member))
       ((unless (json::value-case value :array))
        (reterr (jsonrpc::make-invalid-params-error
                 "Parameter preprocess-args object values must be arrays of strings.")))
       ((mv erp strs) (value-list->strings (json::value-array->elements value)))
       ((when erp)
        (reterr (jsonrpc::make-invalid-params-error
                 "Parameter preprocess-args object values must be arrays of strings.")))
       ((erp rest) (members->string-stringlist-map (cdr members))))
    (retok (omap::update name strs rest))))

(define param->preprocess-args ((obj json::valuep))
  :guard (json::value-case obj :object)
  :returns (mv (erp maybe-errorp)
               (preprocess-args
                (or (string-listp preprocess-args)
                    (acl2::string-stringlist-mapp preprocess-args))))
  :short "Read the @('\"preprocess-args\"') parameter."
  (b* (((reterr) nil)
       ((mv presentp v) (get-member "preprocess-args" obj))
       ((unless presentp) (retok nil))
       ((when (json::value-case v :array))
        (b* (((mv erp strs) (value-list->strings (json::value-array->elements v)))
             ((when erp)
              (reterr (jsonrpc::make-invalid-params-error
                       "Parameter preprocess-args must be an array of strings or an object mapping strings to arrays of strings."))))
          (retok strs)))
       ((when (json::value-case v :object))
        (b* ((members (json::value-object->members v))
             (dup (members-first-duplicate members))
             ((when dup)
              (reterr (jsonrpc::make-invalid-params-error
                       (concatenate 'string
                                    "Duplicate preprocess-args entry: "
                                    dup)))))
          (members->string-stringlist-map members))))
    (reterr (jsonrpc::make-invalid-params-error
             "Parameter preprocess-args must be an array of strings or an object mapping strings to arrays of strings."))))

(define param->preprocess ((obj json::valuep))
  :guard (json::value-case obj :object)
  :returns (mv (erp maybe-errorp)
               (preprocess
                c$::input-files-preprocess-inputp
                :hints (("Goal"
                         :in-theory (enable c$::input-files-preprocess-inputp)))))
  :short "Read the @('\"preprocess\"') parameter (default @(':auto'))."
  (b* (((reterr) :auto)
       ((mv presentp v) (get-member "preprocess" obj))
       ((unless presentp) (retok :auto))
       ((when (json::value-case v :false)) (retok nil))
       ;; JSON true means "preprocess with auto-detection", i.e. :auto (the
       ;; default); it must be a valid input-files-preprocess-inputp value.
       ((when (json::value-case v :true)) (retok :auto))
       ((when (json::value-case v :string))
        (b* ((s (json::value-string->get v)))
          (retok (if (equal s "auto") :auto s)))))
    (reterr (jsonrpc::make-invalid-params-error
             "Parameter preprocess must be a boolean or a string."))))

(define param->ienv ((obj json::valuep))
  :guard (json::value-case obj :object)
  :returns (mv (erp maybe-errorp)
               (ienv c$::ienvp
                     :hints (("Goal" :in-theory (enable c$::ienv-default)))))
  :short "Read the @('\"extensions\"') parameter and build an implementation
          environment (default @(':gcc'))."
  (b* (((reterr) (c$::ienv-default))
       ((mv presentp v) (get-member "extensions" obj))
       (ext (cond ((not presentp) :gcc)
                  ((json::value-case v :false) :none)
                  ((json::value-case v :string)
                   (let ((s (json::value-string->get v)))
                     (cond ((equal s "gcc") :gcc)
                           ((equal s "clang") :clang)
                           (t :bad))))
                  (t :bad)))
       ((when (eq ext :bad))
        (reterr (jsonrpc::make-invalid-params-error
                 "Parameter extensions must be \"gcc\", \"clang\", or false.")))
       (dialect (c::make-dialect :std (c::standard-c17)
                                 :gcc (eq ext :gcc)
                                 :clang (eq ext :clang))))
    (retok (c$::ienv-default :dialect dialect))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The dispatched method must be in the JSONRPC package: the JSON-RPC interface
; interns the requested method name into that package to find the function.

(define jsonrpc::struct-type-split ((params jsonrpc::structuredp) state)
  :returns (mv (erp maybe-errorp) (res json::valuep) state)
  :short "JSON-RPC method implementing the @(tsee c2c::struct-type-split)
          transformation."
  :stobjs state
  (b* (((reterr) (json::value-null) state)
       ((unless (jsonrpc::structured-case params :object))
        (reterr (jsonrpc::make-invalid-params-error
                 "params must be a JSON object.")))
       (members (jsonrpc::structured-object->members params))
       ;; Reject duplicate parameter names rather than silently
       ;; using the first occurrence (cf. get-member).
       (dup (members-first-duplicate members))
       ((when dup)
        (reterr (jsonrpc::make-invalid-params-error
                 (concatenate 'string "Duplicate parameter: " dup))))
       (obj (json::value-object members))
       ;; Common input/output arguments:
       ((erp & old-dir) (param->string "old-dir" obj t))
       ((erp & new-dir) (param->string "new-dir" obj t))
       ((erp files) (param->string-list "files" obj t))
       ((erp preprocess) (param->preprocess obj))
       ((erp preprocess-args) (param->preprocess-args obj))
       ((erp ienv) (param->ienv obj))
       ;; Transformation-specific arguments:
       ((erp struct-tag-present struct-tag)
        (param->string "struct-tag" obj nil))
       ((erp typedef-name-present typedef-name)
        (param->string "typedef-name" obj nil))
       ((when (eq struct-tag-present typedef-name-present))
        (reterr (jsonrpc::make-invalid-params-error
                 "Exactly one of struct-tag and typedef-name must be provided.")))
       ((erp right-members) (param->string-list "right-members" obj t))
       ((unless (consp right-members))
        (reterr (jsonrpc::make-invalid-params-error
                 "At least one right member must be specified.")))
       ((erp filepath-present filepath) (param->string "filepath" obj nil))
       ((erp new-tag-present new-tag) (param->string "new-tag" obj nil))
       ((erp unsafe) (param->boolean "unsafe" obj nil))
       ;; Read the input files into a code ensemble:
       ((mv erp code state)
        (c$::input-files-prog-fn t files old-dir preprocess preprocess-args
                                 nil nil :validate nil nil nil ienv state))
       ((when erp)
        (reterr (jsonrpc::make-internal-error "Error reading input files.")))
       ;; The transformation requires an annotated (validated) code ensemble.
       ;; input-files-prog-fn with :validate produces one, but that is not
       ;; statically guaranteed, so we check it here.
       ((unless (code-ensemble-annop code))
        (reterr (jsonrpc::make-internal-error
                 "Internal error: the input code ensemble is not annotated.")))
       ;; Run the transformation on the code ensemble:
       (tag? (and struct-tag-present (c$::ident struct-tag)))
       (typedef-name? (and typedef-name-present (c$::ident typedef-name)))
       (filepath? (and filepath-present (c$::filepath filepath)))
       (right-member-idents (c$::string-list-map-ident right-members))
       (new-tag? (and new-tag-present (c$::ident new-tag)))
       ((mv er? code$ warnings)
        (sts-split-code-ensemble
         right-member-idents tag? typedef-name? filepath? new-tag? unsafe code))
       ((when er?)
        (reterr (jsonrpc::make-internal-error
                 (concatenate 'string
                              "struct-type-split error: "
                              (warning-to-string er?)))))
       ;; Write the transformed code ensemble to the output directory:
       ((mv erp state)
        (c$::output-files-prog-fn code$ (list :base-dir new-dir) state))
       ((when erp)
        (reterr (jsonrpc::make-internal-error "Error writing output files."))))
    (retok (json::value-object
            (list (json::make-member
                   :name "warnings"
                   ;; sts-split-code-ensemble returns warnings in reverse
                   ;; chronological order; present them chronologically.
                   :value (json::value-array
                           (warnings-to-values (reverse warnings))))))
           state)))
