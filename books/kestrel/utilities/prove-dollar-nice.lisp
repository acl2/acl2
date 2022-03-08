; A wrapper for prove$ that provides nicer behavior
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This wrapper for prove$ attempts to address several (arguable!) deficiencies
;; in prove$, including printing of step-limit errors (these are not errors),
;; handling of the time-limit argument (error if the value is nil but not the
;; term "nil"), and disallowing ignored vars by default (unless allowed by the
;; acl2-defaults-table -- the checking of which is best avoided in a tool that
;; will be called programmatically, to prevent that behavior from depending on
;; such a global setting).

;; Example problematic calls of prove$ for which prove$-nice works better (see below):
;; (prove$ '(equal (car (cons x y)) x) :step-limit 2) ; prints an error message, but this is not an error
;; (let ((time-limit nil)) (prove$ '(equal (car (cons x y)) x) :time-limit time-limit)) ; gives an error, because time-limit arg is not actually "nil"
;; (prove$ '(let ((w 1)) (equal (car (cons x y)) x))) ; error about ignored var W, should be suppressed by default

(include-book "tools/prove-dollar" :dir :system)

;; Returns (mv erp provedp state).
(defun prove$-nice-fn (term
                       hints
                       instructions
                       otf-flg
                       time-limit ; warning: not portable!
                       step-limit
                       state)
  (declare (xargs :guard (and (booleanp otf-flg)
                              (or (natp time-limit)
                                  (null time-limit))
                              (or (natp step-limit)
                                  (null step-limit)))
                  :mode :program
                  :stobjs state))
  (revert-world
   (er-progn
    ;; Step-limit reached is not an error, so this makes it not print an error
    ;; message:
    (with-output! :off :all ; silence TABLE-FN
      (TABLE-FN 'INHIBIT-ER-SOFT-TABLE
                (list "step-limit" nil)
                STATE
                '(TABLE INHIBIT-ER-SOFT-TABLE "step-limit" nil)))
    (if time-limit ;awkward, due to how prove$ handles time-limit
        (prove$ term
                :hints hints
                :instructions instructions
                :otf-flg otf-flg
                :ignore-ok t ; okay to have ignored let-vars
                :time-limit time-limit
                :step-limit step-limit)
      (prove$ term
              :hints hints
              :instructions instructions
              :otf-flg otf-flg
              :ignore-ok t ; okay to have ignored let-vars
              :step-limit step-limit)))))

;; Returns (mv erp provedp state).
;; See also prove-dollar+.
(defmacro prove$-nice (term
                       &key
                       (hints 'nil)
                       (instructions 'nil)
                       (otf-flg 'nil)
                       (time-limit 'nil) ; warning: not portable!
                       (step-limit 'nil))
  `(prove$-nice-fn ,term
                   ,hints
                   ,instructions
                   ,otf-flg
                   ,time-limit
                   ,step-limit
                   state))

;; Tests:
;; (prove$-nice '(equal (car (cons x y)) x))
;; (prove$-nice '(equal (car (cons x y)) x) :step-limit 2) ; fails quietly (call last-prover-steps to see that the step limit was reached)
;; (let ((time-limit nil)) (prove$-nice '(equal (car (cons x y)) x) :time-limit time-limit)) ; works
;; (prove$-nice '(let ((w 1)) (equal (car (cons x y)) x))) ; no error about W
