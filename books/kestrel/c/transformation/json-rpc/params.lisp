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

(include-book "code-env")

(local (include-book "std/typed-lists/string-listp" :dir :system))

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ json-rpc-params
  :parents (c-transformation-json-rpc)
  :short "Reading the parameters of the JSON-RPC methods."
  :long
  (xdoc::topstring
   (xdoc::p
    "The methods take their @('params') as a JSON Object (by-name parameters).
     These utilities check the parameter names
     and read and validate individual parameters,
     reporting problems as JSON-RPC invalid-params errors.
     Some parameters name code ensembles in the @(see code-env)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define maybe-errorp (x)
  :returns (yes/no booleanp)
  :parents (jsonrpc::error)
  :short "Recognize an optional @(see jsonrpc::error)."
  (or (not x)
      (jsonrpc::errorp x))
  ///

  (defrule maybe-errorp-when-errorp
    (implies (jsonrpc::errorp x)
             (maybe-errorp x))
    :enable maybe-errorp))

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

(define members-first-unknown ((members json::member-listp)
                               (known-names string-listp))
  :returns (name acl2::maybe-stringp)
  :short "The first unknown member name, or @('nil')."
  (b* ((known-names (str::string-list-fix known-names))
       ((when (endp members)) nil)
       (name (json::member->name (car members))))
    (if (member-equal name known-names)
        (members-first-unknown (cdr members) known-names)
      name)))

(define params->members ((params jsonrpc::structuredp)
                         (known-names string-listp))
  :returns (mv (erp maybe-errorp) (members json::member-listp))
  :short "Check that the params are a JSON Object
          whose member names are distinct and known,
          and return its members."
  (b* (((reterr) nil)
       ((unless (jsonrpc::structured-case params :object))
        (reterr (jsonrpc::make-invalid-params-error
                 "params must be a JSON object.")))
       (members (jsonrpc::structured-object->members params))
       ;; Reject duplicate parameter names rather than
       ;; silently using the first occurrence (cf. get-member).
       (dup (members-first-duplicate members))
       ((when dup)
        (reterr (jsonrpc::make-invalid-params-error
                 (concatenate 'string "Duplicate parameter: " dup))))
       (unknown (members-first-unknown members known-names))
       ((when unknown)
        (reterr (jsonrpc::make-invalid-params-error
                 (concatenate 'string "Unknown parameter: " unknown)))))
    (retok members)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-member ((name stringp) (obj json::valuep))
  :guard (json::value-case obj :object)
  :returns (mv (presentp booleanp) (val json::valuep))
  :short "Retrieve the (first) value associated with a member name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns @('(mv presentp val)');
     @('val') is @(tsee json::value-null) when the member is absent."))
  (b* ((name (acl2::str-fix name))
       (obj (json::value-fix obj))
       (vals (json::object-member-values name obj)))
    (if (consp vals)
        (mv t (json::value-fix (car vals)))
      (mv nil (json::value-null)))))

(define param->string ((name stringp) (obj json::valuep) (requiredp booleanp))
  :guard (json::value-case obj :object)
  :returns (mv (erp maybe-errorp) (presentp booleanp) (str stringp))
  :short "Read a string-valued parameter."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns @('(mv erp presentp str)').
     @('str') is the empty string when the parameter is absent
     (in which case @('presentp') is @('nil'))."))
  (b* ((name (acl2::str-fix name))
       ((reterr) nil "")
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
  :returns (mv (bad-index acl2::maybe-natp :rule-classes :type-prescription)
               (strs string-listp))
  :short "Convert a list of JSON values to a list of strings,
          returning the index of the first non-string value, if any."
  :verify-guards :after-returns
  (if (endp vals)
      (mv nil nil)
    (b* ((v (car vals))
         ((unless (json::value-case v :string)) (mv 0 nil))
         ((mv bad-index rest) (value-list->strings (cdr vals)))
         ((when bad-index) (mv (1+ bad-index) nil)))
      (mv nil (cons (json::value-string->get v) rest)))))

(define param->string-list ((name stringp)
                            (obj json::valuep)
                            (requiredp booleanp))
  :guard (json::value-case obj :object)
  :returns (mv (erp maybe-errorp) (strs string-listp))
  :short "Read a parameter that is an array of strings."
  (b* ((name (acl2::str-fix name))
       ((reterr) nil)
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
       ((mv bad-index strs)
        (value-list->strings (json::value-array->elements v)))
       ((when bad-index)
        (reterr
         (jsonrpc::make-invalid-params-error
          (warning-to-string
           (msg "Element at index ~x0 of parameter ~x1 must be a string."
                bad-index
                name))))))
    (retok strs)))

(define param->boolean ((name stringp)
                        (obj json::valuep)
                        (default booleanp))
  :guard (json::value-case obj :object)
  :returns (mv (erp maybe-errorp) (val booleanp))
  :short "Read an optional boolean-valued parameter."
  (b* ((name (acl2::str-fix name))
       (default$ (and default t))
       ((reterr) default$)
       ((mv presentp v) (get-member name obj))
       ((unless presentp) (retok default$))
       ((when (json::value-case v :true)) (retok t))
       ((when (json::value-case v :false)) (retok nil)))
    (reterr (jsonrpc::make-invalid-params-error
             (concatenate 'string
                          "Parameter " name " must be a boolean.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param->base-dir ((obj json::valuep))
  :guard (json::value-case obj :object)
  :returns (mv (erp maybe-errorp) (base-dir stringp))
  :short "Read the @('\"base-dir\"') parameter (default @('\".\"'))."
  (b* (((reterr) ".")
       ((erp presentp base-dir) (param->string "base-dir" obj nil)))
    (retok (if presentp base-dir "."))))

(define members->string-stringlist-map ((members json::member-listp))
  :returns (mv (erp maybe-errorp)
               (map acl2::string-stringlist-mapp))
  :short "Convert JSON object members to a string-to-string-list omap."
  :verify-guards :after-returns
  (b* (((reterr) nil)
       ((when (endp members)) (retok nil))
       (member (car members))
       (name (json::member->name member))
       (value (json::member->value member))
       ((unless (json::value-case value :array))
        (reterr
         (jsonrpc::make-invalid-params-error
          (warning-to-string
           (msg "Entry ~x0 of parameter ~x1 must be an array of strings."
                name
                "preprocess-args")))))
       ((mv bad-index strs)
        (value-list->strings (json::value-array->elements value)))
       ((when bad-index)
        (reterr
         (jsonrpc::make-invalid-params-error
          (warning-to-string
           (msg "Element at index ~x0 of entry ~x1 in parameter ~x2 ~
                 must be a string."
                bad-index
                name
                "preprocess-args")))))
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
        (b* (((mv bad-index strs)
              (value-list->strings (json::value-array->elements v)))
             ((when bad-index)
              (reterr
               (jsonrpc::make-invalid-params-error
                (warning-to-string
                 (msg "Element at index ~x0 of parameter ~x1 ~
                       must be a string."
                      bad-index
                      "preprocess-args"))))))
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
  :short "Read the @('\"extensions\"') parameter
          and build an implementation environment (default @(':gcc'))."
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

(define param->source ((obj json::valuep) code-env)
  :guard (json::value-case obj :object)
  :returns (mv (erp maybe-errorp)
               (code ann-code-ensemblep :hyp (code-envp code-env)))
  :stobjs code-env
  :short "Read the @('\"source\"') parameter
          and look up the code ensemble it names."
  (b* (((reterr) (irr-ann-code-ensemble))
       ((erp & source) (param->string "source" obj t))
       (code? (ensembles-get source code-env))
       ((unless code?)
        (reterr (jsonrpc::make-invalid-params-error
                 (concatenate 'string "Unbound name: " source)))))
    (retok code?)))

(define param->target ((obj json::valuep) code-env)
  :guard (json::value-case obj :object)
  :returns (mv (erp maybe-errorp) (target stringp))
  :stobjs code-env
  :short "Read the @('\"target\"') and @('\"overwrite\"') parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The target names the code ensemble that the method produces.
     If the name is already bound, it is an error
     unless @('\"overwrite\"') is @('true') (the default is @('false')).
     Methods check this before doing any work,
     so that the error is reported promptly."))
  (b* (((reterr) "")
       ((erp & target) (param->string "target" obj t))
       ((erp overwrite) (param->boolean "overwrite" obj nil))
       ((when (and (not overwrite)
                   (ensembles-boundp target code-env)))
        (reterr (jsonrpc::make-invalid-params-error
                 (concatenate 'string
                              "Name already bound: "
                              target
                              " (set overwrite to true to replace it)")))))
    (retok target)))
