; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Example:
;   (include-book "top")
;   (json-message-group-string-to-constraints *field-compare--message-json*)

; Future possibilities: make versions that return PFCS value or FTY version of R1CS

;;;;;;;;;;;;;;;;;;;;

; Currently, this code parses JSON structures like the following.
#||
{
  "scope_index": 0,
  "entries": [
    {
      "depth": 0,
      "message": "{\n  \"a\": [\n    [\n      \"w2\",\n      \"8444461749428370424248824938781546531375899335154063827935233455917409239040\"\n    ],\n    [\n      \"ONE\",\n      \"1\"\n    ]\n  ],\n  \"b\": [\n    [\n      \"w2\",\n      \"1\"\n    ]\n  ],\n  \"c\": []\n}"
    },
    {
      "depth": 0,
      "message": "{\n  \"a\": [\n    [\n      \"w3\",\n      \"8444461749428370424248824938781546531375899335154063827935233455917409239040\"\n    ],\n    [\n      \"ONE\",\n      \"1\"\n    ]\n  ],\n  \"b\": [\n    [\n      \"w3\",\n      \"1\"\n    ]\n  ],\n  \"c\": []\n}"
    }
      ]
}
||#
; The top-level JSON structure we call a JSON message group, which contains
; one JSON message entry for each constraint,
; and for each entry, the string value of "message" must be parsed to get the
; constraint.

; This structure differs from the previous structure parsed by
; "gadget-json-to-r1cs-defagg.lisp" in that
; 1. it does does not have the "num_constants", etc. fields --- each message
; string contains just a single constraint;
; 2. there are two levels of parsing JSON from strings here: the outer JSON
;    and then the per-constraint parsing from message strings.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "gadget-json-to-r1cs-defagg")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-message-string-to-constraint ((json-message-string stringp))
  :returns (mv (erp booleanp) (ret-val r1cs::r1cs-constraintp))
  (b* (((mv erp json-sexp) (acl2::parse-string-as-json json-message-string))
       ((when erp) (mv t *error-constraint*))
       ((mv erp json-fty-value) (json::parsed-to-value json-sexp))
       ((when erp) (mv t *error-constraint*))
       ((unless (json::valuep json-fty-value))
        (mv t *error-constraint*))
       ((mv erp constraint)
        (json-constraint-to-r1cs json-fty-value))
       ((when erp) (mv t *error-constraint*))
       ((unless (r1cs::r1cs-constraintp constraint))
        (mv t *error-constraint*)))
    (mv nil constraint)))

(define json-message-entry-to-constraint ((json-message-entry json::valuep))
  :returns (mv (erp booleanp) (ret-val r1cs::r1cs-constraintp))
  (b* (((json::pattern (:object (:member "depth" _) ; Note 1
                                (:member message (:string message-string))))
        json-message-entry)
       ((unless (and json::match? (stringp message-string)))
        (mv t *error-constraint*))
       ((mv erp constraint)
        (json-message-string-to-constraint message-string))
       ((when erp) (mv t *error-constraint*)))
    (mv nil constraint)))
; Note 1: We have not yet seen a depth other than 0, so we ignore the value for
; now.

(define json-message-entries-to-constraints ((json-message-entries json::value-listp))
  :returns (mv (erp booleanp) (ret-val r1cs::r1cs-constraint-listp))
  (b* (((when (atom json-message-entries))
        (mv nil nil))
       ((mv erp first-constraint)
        (json-message-entry-to-constraint (first json-message-entries)))
       ((when erp) (mv t nil))
       ((mv erp rest-constraints)
        (json-message-entries-to-constraints (rest json-message-entries)))
       ((when erp) (mv t nil)))
    (mv nil
        (cons first-constraint rest-constraints))))

(define json-message-group-to-constraints ((json-message-group json::valuep))
  :returns (mv (erp booleanp) (ret-val r1cs::r1cs-constraint-listp))
  (b* (((json::pattern (:object (:member "scope_index" _) ; Note 2
                                (:member "entries"
                                         (:array entries..))))
        json-message-group)
       ((unless json::match?)
        (mv t nil))
       ((mv erp constraints)
        (json-message-entries-to-constraints entries..))
       ((when erp) (mv t nil)))
    (mv nil constraints)))
; Note 2: We have not yet seen a scope index other than 0, so we ignore the
; value for now.

(define json-message-group-string-to-constraints ((json-message-group-string
                                                   stringp))
  :returns (mv (erp booleanp) (ret-val r1cs::r1cs-constraint-listp))
  (b* (((mv erp json-sexp) (acl2::parse-string-as-json json-message-group-string))
       ((when erp) (mv t nil))
       ((mv erp json-fty-value) (json::parsed-to-value json-sexp))
       ((when erp) (mv t nil))
       ((unless (json::valuep json-fty-value))
        (mv t nil))
       ((mv erp constraints)
        (json-message-group-to-constraints json-fty-value))
       ((when erp) (mv t nil))
       ((unless (listp constraints))
        (mv t nil)))
    (mv nil constraints)))
