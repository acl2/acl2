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
          "w0",  <-- now also supports "w(N, 0)"
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

(define json-var-with-parens-0 ((varstring stringp))
  ;; 2024-03-04 The standard output for variables in the constraints
  ;; now shows a witness value along with the variable number, e.g.
  ;; w(NNN, WV) instead of wNNN.
  ;; For now we drop the witness value, but we may want to use it
  ;; for some purpose later.
  :returns (result stringp :hyp :guard)
  (let ((open-paren (position #\( varstring))
        (comma (position #\, varstring)))
    (if (and open-paren comma (< open-paren comma))
        (string-append
         (subseq varstring 0 open-paren) ; the alphabetic prefix, currently only "w"
         (subseq varstring (+ open-paren 1) comma)) ; the numeric suffix
        varstring))
  :prepwork ((local (include-book "kestrel/lists-light/position-equal" :dir :system))))

; The json-term uses "ONE" as the "variable name" for the constant.
; The r1cs defaggregate uses symbols for variables and the number 1 for the constant.
(define json-term-to-r1cs ((json-term json::valuep))
  :returns (mv (erp booleanp) (ret-val listp))
  ; the actual return type is a list of integerp and r1cs::pseudo-varp
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
              (if (equal varstring "ONE")
                  1
                (intern-in-package-of-symbol (json-var-with-parens-0 varstring) 'r1cs::hoy))))))

; I want to call this r1cs::pseudo-termp but that name is taken
; This should live in acl2/books/kestrel/crypto/r1cs/sparse/r1cs.lisp
; and be factored out of r1cs::sparse-vectorp
(defun r1cs::r1cs-termp (term)
  (and (true-listp term)
       (equal 2 (len term))
       (integerp (first term))
       (r1cs::pseudo-varp (second term))))

(verify-guards r1cs::r1cs-termp)

(define json-terms-to-r1cs ((json-terms json::value-listp))
  :returns (mv (ret-erp booleanp) (ret-val r1cs::sparse-vectorp
                                           :hints (("Goal" :in-theory (enable r1cs::sparse-vectorp)))))
  (b* (((when (atom json-terms))
        (mv nil nil))
       ((mv erp first-term)
        (json-term-to-r1cs (first json-terms)))
       ((when erp) (mv t nil))
       ((unless (r1cs::r1cs-termp first-term))
        (mv t nil))
       ((mv erp rest-terms)
        (json-terms-to-r1cs (rest json-terms)))
       ((when erp) (mv t nil)))
    (mv nil
        (cons first-term rest-terms)))
  ///
  (defret sparse-vectorp-of-json-terms-to-r1cs
    (implies (not ret-erp)
             (r1cs::sparse-vectorp ret-val))))

(define json-linear-combination-to-r1cs ((json-lc json::valuep))
  :returns (mv (ret-erp booleanp) (ret-val r1cs::sparse-vectorp))
  (b* (((json::pattern (:array json-terms..)) json-lc)
       ((unless (and json::match? (listp json-terms..)))
        (mv t nil))
       ((mv erp terms)
        (json-terms-to-r1cs json-terms..))
       ((when erp) (mv t nil)))
    (mv nil terms))
  ///
  (defret sparse-vectorp-of-json-linear-combination-to-r1cs
    (implies (not ret-erp)
             (r1cs::sparse-vectorp ret-val))))

(defconst *error-constraint*
  (r1cs::r1cs-constraint nil nil nil))

(define json-constraint-to-r1cs ((json-constraint json::valuep))
  :returns (mv (erp booleanp) (ret-val r1cs::r1cs-constraintp))
  (b* (((json::pattern (:object (:member "a" json-lca)
                                (:member "b" json-lcb)
                                (:member "c" json-lcc)))
        json-constraint)
       ((unless json::match?)
        (mv t *error-constraint*))
       ((mv erp lca)
        (json-linear-combination-to-r1cs json-lca))
       ((when erp) (mv t *error-constraint*))
       ((mv erp lcb)
        (json-linear-combination-to-r1cs json-lcb))
       ((when erp) (mv t *error-constraint*))
       ((mv erp lcc)
        (json-linear-combination-to-r1cs json-lcc))
       ((when erp) (mv t *error-constraint*))
       )
    (mv nil
        (r1cs::r1cs-constraint lca lcb lcc))))

(define json-constraints-to-r1cs ((json-constraints json::value-listp))
  :returns (mv (erp booleanp) (ret-val r1cs::r1cs-constraint-listp))
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
  :returns (mv (erp booleanp) (ret-val r1cs::r1cs-constraint-listp))
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
(define json-gadget-string-to-r1cs ((json-gadget-string stringp))
  :returns (mv (erp booleanp) (ret-val r1cs::r1cs-constraint-listp))
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

; Future possibilities: make versions that return PFCS value or FTY version of R1CS
