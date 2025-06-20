; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Currently, this code parses JSON structures like this (this is just a bit constraint):
#||
{
  "num_constants": 0,
  "num_public": 1,
  "num_private": 1,
  "num_constraints": 1,
  "is_satisfied": true,
  "constraints": [
    {
      "a": [
        [
          "w0",
          "8444461749428370424248824938781546531375899335154063827935233455917409239040"
        ],
        [
          "ONE",
          "1"
        ]
      ],
      "b": [
        [
          "w0",
          "1"
        ]
      ],
      "c": []
    }
  ]
}
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "parse-json/r1cs-json2acl2")

(include-book "std/strings/decimal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; same enable list as json2ast.lisp
(in-theory (enable json::value-kind
                   ;; all the light-ast-check functions used by json::pattern
                   json::jnullp json::jtruep json::jfalsep
                   json::jstringp json::jnumberp
                   json::top-jarrayp json::top-jobjectp
                   json::top-jmemberp json::top-jmember-listp))

(define json-term-to-r1cs ((json-term json::valuep))
  :returns (mv (erp booleanp) (ret-val listp))
  (b* (((json::pattern (:array (:string varstring)
                               (:string valstring)))
        json-term)
       ((unless (and json::match?))
        (mv t nil))
       (val (str::strval valstring))
       ((unless (natp val))
        (mv t nil)))
    (mv nil
        (list val
              (intern-in-package-of-symbol varstring 'r1cs::hoy)))))

(define json-terms-to-r1cs ((json-terms json::value-listp))
  :returns (mv (erp booleanp) (ret-val listp))
  (b* (((when (atom json-terms))
        (mv nil nil))
       ((mv erp first-term)
        (json-term-to-r1cs (first json-terms)))
       ((when erp) (mv t nil))
       ((mv erp rest-terms)
        (json-terms-to-r1cs (rest json-terms)))
       ((when erp) (mv t nil)))
    (mv nil
        (cons first-term rest-terms))))

(define json-linear-combination-to-r1cs ((json-lc json::valuep))
  :returns (mv (erp booleanp) (ret-val listp))
  (b* (((json::pattern (:array json-terms..)) json-lc)
       ((unless (and json::match? (listp json-terms..)))
        (mv t nil))
       ((mv erp terms)
        (json-terms-to-r1cs json-terms..))
       ((when erp) (mv t nil))
       ((unless (listp terms))
        (mv t nil)))
    (mv nil terms)))

(define json-constraint-to-r1cs ((json-constraint json::valuep))
  :returns (mv (erp booleanp) (ret-val listp))
  (b* (((json::pattern (:object (:member "a" json-lca)
                                (:member "b" json-lcb)
                                (:member "c" json-lcc)))
        json-constraint)
       ((unless json::match?)
        (mv t nil))
       ((mv erp lca)
        (json-linear-combination-to-r1cs json-lca))
       ((when erp) (mv t nil))
       ((mv erp lcb)
        (json-linear-combination-to-r1cs json-lcb))
       ((when erp) (mv t nil))
       ((mv erp lcc)
        (json-linear-combination-to-r1cs json-lcc))
       ((when erp) (mv t nil)))
    (mv nil
        `((R1CS::A ,@lca)
          (R1CS::B ,@lcb)
          (R1CS::C ,@lcc)))))

(define json-constraints-to-r1cs ((json-constraints json::value-listp))
  :returns (mv (erp booleanp) (ret-val listp))
  (b* (((when (atom json-constraints))
        (mv nil nil))
       ((mv erp first-constraint)
        (json-constraint-to-r1cs (first json-constraints)))
       ((when erp) (mv t nil))
       ((mv erp rest-constraints)
        (json-constraints-to-r1cs (rest json-constraints)))
       ((when erp) (mv t nil)))
    (mv nil
        (cons first-constraint rest-constraints))))

; Note, this returns a list of constraints, not a full
; value of the defaggregate r1cs.
(define json-gadget-to-r1cs ((json-gadget json::valuep))
  :returns (mv (erp booleanp) (ret-val listp))
  (b* (((json::pattern (:object (:member "num_constants" _)
                                (:member "num_public" _)
                                (:member "num_private" _)
                                (:member "num_constraints" _)
                                (:member "is_satisfied" _)
                                (:member "constraints"
                                         (:array json-constraints..))))
        json-gadget)
       ((unless json::match?)
        (mv t nil))
       ((mv erp constraints)
        (json-constraints-to-r1cs json-constraints..))
       ((when erp) (mv t nil))
       ((unless (listp constraints))
        (mv t nil))
       )
    (mv nil constraints)))

; Note, this returns a list of constraints, not a full
; value of the defaggregate r1cs.
; Also, The constant value pseudo-var is the symbol ONE rather than the nat 1.
(define json-gadget-string-to-r1cs ((json-gadget-string stringp))
  :returns (mv (erp booleanp) (ret-val listp))
  (b* (((mv erp json-sexp) (acl2::parse-string-as-json json-gadget-string))
       ((when erp) (mv t nil))
       ((mv erp json-fty-value) (json::parsed-to-value json-sexp))
       ((when erp) (mv t nil))
       ((unless (json::valuep json-fty-value))
        (mv t nil))
       ((mv erp gadget)
        (json-gadget-to-r1cs json-fty-value))
       ((when erp) (mv t nil))
       ((unless (listp gadget))
        (mv t nil)))
    (mv nil gadget)))

; Example:
;   (include-book "top")
;   (ALEO::JSON-GADGET-STRING-TO-R1CS ALEO::*BOOLEAN-AND-JSON*)
