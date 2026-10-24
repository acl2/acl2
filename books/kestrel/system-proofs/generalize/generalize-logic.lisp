; Putting parts of generalize-clause into :logic mode
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book puts into :logic mode the functions that generalize-clause (via
;; generalize1) uses to build its result clause: sublis-expr, disjoin-clauses,
;; and generalize-rule-segment, which applies :generalize rules.  Guards are
;; not verified here.
;;
;; The rest of generalize-clause cannot be put into :logic mode this way,
;; because type-restriction-segment and generate-variable-lst call type-set,
;; whose supporters include linear arithmetic and clausify.

;; Several measures below have the form (if x (+ 1 (len x)) 0), the number of
;; steps to reach NIL by taking CDRs, which handles recursions that stop when x
;; is NIL (rather than when x is an atom).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Replacing terms by variables
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination
  (sublis-expr (declare (xargs :measure (+ 1 (* 2 (acl2-count term)))
                               :verify-guards nil)))
  (sublis-expr-lst (declare (xargs :measure (+ (* 2 (acl2-count lst)) (if lst 2 0))
                                   :verify-guards nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Disjoining clauses
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination comm-equal (declare (xargs :verify-guards nil)))

(verify-termination member-term2
  (declare (xargs :measure (if cl (+ 1 (len cl)) 0) :verify-guards nil)))

(verify-termination member-complement-term1
  (declare (xargs :measure (if cl (+ 1 (len cl)) 0) :verify-guards nil)))

(verify-termination member-complement-term2
  (declare (xargs :measure (if cl (+ 1 (len cl)) 0) :verify-guards nil)))

(verify-termination
  (member-term (declare (xargs :measure (+ 1 (* 2 (acl2-count lit)))
                               :verify-guards nil)))
  (member-complement-term (declare (xargs :measure (* 2 (acl2-count lit))
                                          :verify-guards nil))))

(verify-termination add-literal (declare (xargs :verify-guards nil)))
(verify-termination disjoin-clauses1 (declare (xargs :verify-guards nil)))
(verify-termination disjoin-clauses (declare (xargs :verify-guards nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Applying :generalize rules
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination
  (subterm-one-way-unify (declare (xargs :measure (+ 1 (* 2 (acl2-count pat)))
                                         :verify-guards nil)))
  (subterm-one-way-unify-lst (declare (xargs :measure (+ (* 2 (acl2-count pat-lst)) (if pat-lst 2 0))
                                             :verify-guards nil))))

(verify-termination
  (free-varsp (declare (xargs :measure (+ 1 (* 2 (acl2-count term)))
                              :verify-guards nil)))
  (free-varsp-lst (declare (xargs :measure (+ (* 2 (acl2-count args)) (if args 2 0))
                                  :verify-guards nil))))

(verify-termination apply-generalize-rule (declare (xargs :verify-guards nil)))

(verify-termination generalize-rule-segment1
  (declare (xargs :measure (if generalize-rules (+ 1 (len generalize-rules)) 0)
                  :verify-guards nil)))

(verify-termination generalize-rule-segment
  (declare (xargs :measure (if terms (+ 1 (len terms)) 0)
                  :verify-guards nil)))
