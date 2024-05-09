; Wrappers for prove$
;
; Copyright (C) 2022-2023 Kestrel Institute
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
(include-book "tables")
(include-book "last-prover-steps-dollar")

;; Turns on inhibiting of the error type indicated by STR (case insensitive).
;; Returns an error triple, (mv erp val state).
(defun add-inhibit-er-programmatic (str state)
  (declare (xargs :guard (stringp str) :mode :program :stobjs state))
  ;; Oddly, keys are set to nil in this table (the values are irrelevant):
  (set-table-entry-programmatic 'inhibit-er-table str nil state))

;; Returns (mv erp provedp state), where PROVEDP is valid only when ERP is nil.
(defun prove$-nice-fn (term
                       hints
                       instructions
                       otf-flg
                       time-limit ; warning: not portable!
                       step-limit
                       state)
  (declare (xargs :guard (and (booleanp otf-flg)
                              (or (and (rationalp time-limit)
                                       (<= 0 time-limit))
                                  (null time-limit))
                              (or (natp step-limit)
                                  (null step-limit)))
                  :mode :program
                  :stobjs state))
  (revert-world
   (er-progn
    ;; Step-limit reached is not an error, so this makes it not print an error
    ;; message:
    (add-inhibit-er-programmatic "step-limit" state) ; todo: this may no longer be needed?
    ;; Don't print an error if the rewrite stack depth is exceeded:
    (add-inhibit-er-programmatic "Call depth" state) ; todo: this may no longer be needed?
    (if time-limit ;awkward, due to how prove$ handles time-limit (todo: is this still an issue?)
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

;; Returns (mv erp provedp state), where PROVEDP is valid only when ERP is nil.
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Calls prove$ on TERM using the HINTS and/or INSTRUCTIONS and/or OTF-FLG.
;; Returns (mv erp provedp elapsed-time prover-steps-counted state), where if
;; the error indicator, ERP, is non-nil, then PROVEDP indicates whether the
;; proof succeeded, and ELAPSED-TIME (in seconds) and PROVER-STEPS-COUNTED are
;; meaningful for the proof attempt or failure.  TODO: Consider also returning
;; the number of proof steps.
(defun prove$-nice-with-time-and-steps (term
                                        hints
                                        instructions
                                        otf-flg
                                        time-limit ; warning: not portable!
                                        step-limit
                                        state)
  (declare (xargs :guard (and (booleanp otf-flg)
                              (or (and (rationalp time-limit)
                                       (<= 0 time-limit))
                                  (null time-limit))
                              (or (natp step-limit)
                                  (null step-limit)))
                  :mode :program
                  :stobjs state))
  ;; Record the start time:
  (mv-let (start-time state)
    (get-real-time state)
    (mv-let (erp provedp state)
      (prove$-nice-fn term hints instructions otf-flg time-limit step-limit state)
      ;; Record the end time:
      (mv-let (end-time state)
        (get-real-time state)
        (if erp
            (mv erp nil nil nil state)
          (mv nil provedp (- end-time start-time) (last-prover-steps$ state) state))))))

;; A wrapper for prove$-nice-with-time-and-steps that discards the steps, returning only the time.
;; Returns (mv erp provedp elapsed-time state).  See doc for prove$-nice-with-time-and-steps.
(defun prove$-nice-with-time (term
                              hints
                              instructions
                              otf-flg
                              time-limit ; warning: not portable!
                              step-limit
                              state)
  (declare (xargs :guard (and (booleanp otf-flg)
                              (or (and (rationalp time-limit)
                                       (<= 0 time-limit))
                                  (null time-limit))
                              (or (natp step-limit)
                                  (null step-limit)))
                  :mode :program
                  :stobjs state))
  (mv-let (erp provedp elapsed-time prover-steps-counted state)
    (prove$-nice-with-time-and-steps term hints instructions otf-flg time-limit step-limit state)
    (declare (ignore prover-steps-counted))
    (mv erp provedp elapsed-time state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp provedp elapsed-time state).
;; Like prove$-nice-with-time, except this one does the proof twice to avoid
;; inaccurate timing info due to garbage collection.
(defun prove$-twice-with-time (term
                               hints
                               instructions
                               otf-flg
                               time-limit ; warning: not portable!
                               step-limit
                               state)
  (declare (xargs :guard (and (booleanp otf-flg)
                              (or (and (rationalp time-limit)
                                       (<= 0 time-limit))
                                  (null time-limit))
                              (or (natp step-limit)
                                  (null step-limit)))
                  :mode :program
                  :stobjs state))
  (mv-let (erp provedp1 elapsed-time1 state)
    (prove$-nice-with-time term hints instructions otf-flg time-limit step-limit state)
    (if erp
        (mv erp nil nil state)
      (mv-let (erp provedp2 elapsed-time2 state)
        (prove$-nice-with-time term hints instructions otf-flg time-limit step-limit state)
        (if erp
            (mv erp nil nil state)
          (if (not (equal provedp1 provedp2))
              ;; I suppose this might happen due to garbage collection triggering a time-limit:
              ;; Can we actually detect whether a time-limit or step-limit was reached?
              (prog2$ (cw "WARNING: The two tries differ on whether the goal was proved.~%")
                      ;; We return the time for the attempt that worked:
                      (if provedp1
                          (mv nil t elapsed-time1 state)
                        (if provedp2
                            (mv nil t elapsed-time2 state)
                          (mv :bad-provedp-value nil nil state))))
            ;; Either both proved or both failed:
            ;; We return the min, so as to try to get the time without garbage collection:
            (mv nil provedp1 (min elapsed-time1 elapsed-time2) state)))))))

;; Tries the given HINTS and INSTRUCTIONS but tries again without them if there
;; is an error (maybe they mention something that was only locally defined).
;; Returns (mv erp provedp state).
(defun prove$-nice-trying-hints (term
                                 hints
                                 instructions
                                 otf-flg
                                 time-limit ; warning: not portable!
                                 step-limit
                                 state)
  (declare (xargs :guard (and (booleanp otf-flg)
                              (or (and (rationalp time-limit)
                                       (<= 0 time-limit))
                                  (null time-limit))
                              (or (natp step-limit)
                                  (null step-limit)))
                  :mode :program
                  :stobjs state))
  ;; First try with the original hints and instructions, though they may now be illegal:
  (mv-let (erp provedp state)
    ;; todo: add with-output argument to prove$-nice-fn and pass :off :all here:
    (prove$-nice-fn term hints instructions otf-flg time-limit step-limit state)
    (if erp
        ;; Try again with no hints and no instructions (maybe the hints/instructions mentioned something that doesn't exist):
        ;; TODO: Perhaps we could do better by keeping parts of the hints are legal:
        (prove$-nice-fn term nil nil otf-flg time-limit step-limit state)
      ;; No error:
      (mv nil provedp state))))
