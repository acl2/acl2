; A utility that suggests ways to speed up a theorem
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See improve-book for a tool that applies this tool to an entire book or set
;; of books (along with suggesting other improvements).

(include-book "kestrel/utilities/prove-dollar-nice" :dir :system)
(include-book "kestrel/utilities/theory-hints" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system)
(include-book "kestrel/utilities/runes" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)
(include-book "kestrel/utilities/print-levels" :dir :system)

;; move these:

;; Returns (mv erp val state) where erp is non-nil if the event failed. val is always nil.
;; This wrapper returns an error triple, so we can wrap it in a call to revert-world.
;;todo: name clash
(defun submit-event-error-triple2 (event print throw-errorp state)
  (declare (xargs :guard (and (member-eq print '(nil :brief t :verbose))
                              (booleanp throw-errorp))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp state)
    (submit-event event print throw-errorp state)
    (mv erp nil state)))

;; Returns (mv erp state) where erp is non-nil if the event failed.
(defun submit-and-revert-event (event print throw-errorp state)
  (declare (xargs :guard (and (member-eq print '(nil :brief t :verbose))
                              (booleanp throw-errorp))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp value state)
    (revert-world (submit-event-error-triple2 event print throw-errorp state))
    (declare (ignore value))
    (mv erp state)))

;; Returns (mv erp provedp elapsed-time state)
;move
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
  ;; Record the start time:
  (mv-let (start-time state)
    (acl2::get-real-time state)
    (mv-let (erp provedp state)
      (prove$-nice-fn term hints instructions otf-flg time-limit step-limit state)
      ;; Record the end time:
      (mv-let (end-time state)
        (acl2::get-real-time state)
        (if erp
            (mv erp nil nil state)
          (mv nil provedp (- end-time start-time) state))))))

;; in seconds
(defconst *minimum-time-savings-to-report* 1/10)

;; Returns state.
;; Each line printed starts with a newline.
;todo: rules are usually actually runes?
(defun try-to-drop-rules-from-defthm (rules body hints otf-flg time-to-beat print state)
  (declare (xargs :guard (and (true-listp rules)
                              (booleanp otf-flg)
                              (rationalp time-to-beat)
                              (print-levelp print))
                  :mode :program
                  :stobjs state))
  (if (endp rules)
      state
    (let ((rule-to-drop (first rules)))
      (mv-let (erp provedp time state)
        (prove$-nice-with-time body
                               (disable-items-in-hints hints (list rule-to-drop) nil)
                               nil ; instructions
                               otf-flg
                               time-to-beat ; time-limit ; warning: not portable!
                               nil          ; step-limit
                               state)
        (if erp
            (prog2$ (er hard? 'try-to-drop-rules-from-defthm "Error trying to disable ~x0." rule-to-drop)
                    state)
          (progn$ (and provedp
                       (if (< time time-to-beat)
                           (let* ((savings (- time-to-beat time))
                                  (percent-saved (floor (* 100 (/ savings time-to-beat)) 1)))
                             (if (<= *minimum-time-savings-to-report* savings)
                                 (progn$ (cw "~%  (Speedup: disable ~x0 to save " rule-to-drop)
                                         (print-to-hundredths savings)
                                         (cw " of ")
                                         (print-to-hundredths time-to-beat)
                                         (cw " seconds (~x0%))" percent-saved))
                               (and (print-level-at-least-tp print)
                                    (progn$ (cw "~%  (Minimal speedup: disable ~x0 to save " rule-to-drop)
                                            (print-to-hundredths savings)
                                            (cw " of ")
                                            (print-to-hundredths time-to-beat)
                                            (cw " seconds (~x0%))" percent-saved)))))
                         (and (print-level-at-least-tp print)
                              (progn$  (cw "~%  (Slower: disable ~x0: " rule-to-drop)
                                       (print-to-hundredths time)
                                       (cw " vs ")
                                       (print-to-hundredths time-to-beat)
                                       (cw " seconds)")
                                       ))))
                  (try-to-drop-rules-from-defthm (rest rules) body hints otf-flg time-to-beat print state)))))))

;; Prints suggested ways to speed up a theorem.  EVENT should be a defthm (or a variant, like defthmd).
;; Returns (mv erp state).
(defun speed-up-defthm (event print state)
  (declare (xargs :guard (member-eq print '(nil :brief t :verbose)) ; todo: caller doesn't allow t?
                  :mode :program
                  :stobjs state))
  (let* ( ;;(defthm-variant (first event))
         (defthm-args (rest event))
         (name (first defthm-args))
         (body (second defthm-args))
         (keyword-value-list (rest (rest defthm-args)))
         (hintsp (assoc-keyword :hints keyword-value-list))
         (hints (cadr hintsp))
         (otf-flgp (assoc-keyword :otf-flg keyword-value-list))
         (otf-flg (cdr otf-flgp))
         (instructionsp (assoc-keyword :instructions keyword-value-list)))
    (if instructionsp
        (progn$ ;; (cw "Not trying to speed up ~x0 because it uses :instructions." name) ; todo: elsewhere, could try to prove without instructions
         (mv nil state))
      ;; Record the start time:
      (mv-let (start-time state)
        (acl2::get-real-time state)
        ;; Do the proof and time it:
        (mv-let (erp provedp state)
          (prove$-nice-fn body
                          hints
                          nil
                          otf-flg
                          nil ; time-limit
                          nil ; step-limit
                          state)
          ;; Record the end time:
          (mv-let (end-time state)
            (acl2::get-real-time state)
            (if erp
                (mv erp state)
              (if (not provedp)
                  (prog2$ (er hard? 'speed-up-defthm "~x0 was expected to prove, but it failed." name)
                          (mv :failed state))
                (let* ((elapsed-time (- end-time start-time)))
                  (if (< elapsed-time 1/100)
                      (prog2$ (and (print-level-at-least-tp print)
                                   (progn$ (cw "  ~%(Not trying to speed up ~x0 because it only takes " name)
                                           (print-to-hundredths elapsed-time)
                                           (cw " seconds)~%")))
                              (mv nil state))
                    (prog2$ (and (print-level-at-least-tp print)
                                 (progn$ (cw "(Original time for ~x0: " name)
                                         (print-to-hundredths elapsed-time)
                                         (cw " seconds)~%")))
                            ;; Get the list of runes used in the proof:
                            (let* ((runes-used (get-event-data 'rules state))
                                   (state (try-to-drop-rules-from-defthm (drop-fake-runes runes-used) body hints otf-flg elapsed-time print state)))
                              (mv nil state)))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns state.  Prints a suggestion if disabling RUNE beforehand can significantly speed up EVENT.
;; Each line printed starts with a newline.
(defun try-to-drop-rune-from-event (rune event time-to-beat state)
  (declare (xargs :guard (rationalp time-to-beat)
                  :mode :program
                  :stobjs state))
  ;; Record the start time:
  (mv-let (start-time state)
    (acl2::get-real-time state)
    ;; Try the event with the rune disabled::
    (mv-let (erp state)
      (submit-and-revert-event `(saving-event-data (progn (in-theory (disable ,rune))
                                                          ,event))
                               nil nil state)
      ;; Record the end time:
      (mv-let (end-time state)
        (acl2::get-real-time state)
        (if erp
            state ; the event failed after doing the disable
          (if (member-equal rune (get-event-data 'rules state))
              ;; the disable didn't really work (perhaps there is an explicit enable hint), so don't recommend it
              (prog2$ (cw "Disablng ~x0 didn't really take effect.")
                      state)
            (let* ((elapsed-time (- end-time start-time)))
              (if (< elapsed-time time-to-beat)
                  (let* ((savings (- time-to-beat elapsed-time))
                         (percent-saved (floor (* 100 (/ savings time-to-beat)) 1)))
                    (if (<= *minimum-time-savings-to-report* savings)
                        (progn$ (cw "~%  (Speedup: disable ~x0 to save " rune)
                                (print-to-hundredths savings)
                                (cw " of ")
                                (print-to-hundredths time-to-beat)
                                (cw " seconds (~x0%))" percent-saved)
                                state)
                      (progn$ ;;  (cw "~%  (Minimal speedup: disable ~x0 to save " rune)
                       ;; (print-to-hundredths savings)
                       ;; (cw " of ")
                       ;; (print-to-hundredths time-to-beat)
                       ;; (cw " seconds (~x0%))" percent-saved)
                       state
                       )))
                (progn$ ;;  (cw "~%  (Slower: disable ~x0: " rune)
                 ;; (print-to-hundredths elapsed-time)
                 ;; (cw " vs ")
                 ;; (print-to-hundredths time-to-beat)
                 ;; (cw " seconds)")
                 state)))))))))

;; Returns state.  Prints suggestion for RUNES which, if disabled beforehand, lead to significant speed ups for EVENT.
(defun try-to-drop-runes-from-event (runes event time-to-beat state)
  (declare (xargs :guard (and (true-listp runes)
                              (rationalp time-to-beat))
                  :mode :program
                  :stobjs state))
  (if (endp runes)
      state
    (let ((state (try-to-drop-rune-from-event (first runes) event time-to-beat state)))
      (try-to-drop-runes-from-event (rest runes) event time-to-beat state))))

;; Returns (mv erp state).
;; Each line printed starts with a newline.
(defun speed-up-defrule (event state)
  (declare (xargs :mode :program
                  :stobjs state))
  (let ((name (cadr event)))
    ;; Record the start time:
    (mv-let (start-time state)
      (acl2::get-real-time state)
      ;; Do the proof and time it:
      (mv-let (erp state)
        (submit-and-revert-event `(saving-event-data ,event) nil nil state)
        ;; Record the end time:
        (mv-let (end-time state)
          (acl2::get-real-time state)
          (if erp
              (prog2$ (er hard? 'speed-up-defrule "~x0 was expected to prove, but it failed." name)
                      (mv erp state))
            (let* ((elapsed-time (- end-time start-time)))
              (if (< elapsed-time 1/100)
                  (progn$ ;; (cw "~%(Not trying to speed up ~x0 because it only takes " name)
                   ;; (print-to-hundredths elapsed-time)
                   ;; (cw " seconds)")
                   (mv nil state))
                ;; Get the list of runes used in the proof:
                (let* ((runes-used (get-event-data-1 'rules (cadr (hons-get name (f-get-global 'event-data-fal state))))))
                  (if (not runes-used)
                      (prog2$ (cw "~%WARNING: No runes reported as used by ~x0." name)
                              (mv nil state))
                    (let ((state (try-to-drop-runes-from-event (drop-fake-runes runes-used) event elapsed-time state)))
                      (mv nil state))))))))))))

;; Returns (mv erp state).
(defun speed-up-event-fn (event print state)
  (declare (xargs :guard (print-levelp print) ; todo: finish threading this through
                  :mode :program
                  :stobjs state))
  (if (not (consp event))
      (prog2$ (er hard? 'speed-up-event-fn "~x0 is not a valid event.")
              (mv :invalid-event state))
    (let ((fn (ffn-symb event)))
      (case fn
        ((defthm defthmd) (speed-up-defthm event print state))
        ((defrule defruled) (speed-up-defrule event state))
        (otherwise (prog2$ (er hard? 'speed-up-event-fn "Unsupported event type: ~X01." event nil)
                           (mv :unsupported-event state)))))))

(defmacro speed-up-event (event)
  `(speed-up-event-fn ',event state))
