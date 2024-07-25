; A utility that suggests ways to speed up a theorem
;
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This tool tries various things to speed up theorems (e.g., disabling rules
;; that were used in the proof but were not needed -- for example, the
;; definition of some function).  The speedups found should be separate from
;; those found by ACL2's useless-runes mechanism, because this tool focuses on
;; rules that do contribute to the original proof (i.e., appear in the list of
;; runes used printed in the event summary), whereas the useless-runes
;; mechanism deals with runes that do not contribute to the proof (and do not
;; appear in the summary).

;; See also improve-book.lisp, for a tool that applies this tool to an entire
;; book or set of books (along with suggesting other improvements).

;; TODO: Add support for speeding up defuns and defines.

(include-book "kestrel/utilities/prove-dollar-nice" :dir :system)
(include-book "kestrel/utilities/theory-hints" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system)
(include-book "kestrel/utilities/runes" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)
(include-book "kestrel/utilities/print-levels" :dir :system)
(include-book "kestrel/utilities/print-to-string" :dir :system)
(include-book "kestrel/hints/combine-hints" :dir :system)

;; move these?

(verify-termination get-event-data-1)
;(verify-guards get-event-data-1) ; todo: needs a guard, perhaps (and (symbolp key) (symbol-alistp event-data)).
;; Requires NAME to have been submitted inside a call of saving-event-data.
(defund runes-used-for-event (name state)
  (declare (xargs :stobjs state
                  :mode :program))
  (get-event-data-1 'rules (cadr (hons-get name (f-get-global 'event-data-fal state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tests whether any of the RUNES is an induction rune.
;; TODO: Generalize.
(defund exists-induction-runep (runes)
  (declare (xargs :guard (true-listp runes)))
  (if (endp runes)
      nil
    (let ((rune (first runes)))
      (or (and (consp rune)
               (eq :induction (car rune)))
          (exists-induction-runep (rest runes))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; in seconds
(defconst *minimum-time-savings-to-report* 1/10)

(defun maybe-print-speedup-message (provedp time time-to-beat speedup-description print)
  (declare (xargs :guard (and (booleanp provedp)
                              (rationalp time)
                              (<= 0 time)
                              (rationalp time-to-beat)
                              (<= 0 time-to-beat)
                              (stringp speedup-description)
                              (print-levelp print))))
  (and provedp
       (if (< time time-to-beat)
           (let* ((savings (- time-to-beat time))
                  (percent-saved (floor (* 100 (/ savings time-to-beat)) 1)))
             (if (<= *minimum-time-savings-to-report* savings)
                 (progn$ (cw "~%  (Speedup: ~s0 to save " speedup-description)
                         (print-to-hundredths savings)
                         (cw " of ")
                         (print-to-hundredths time-to-beat)
                         (cw " seconds (~x0%))" percent-saved))
               (and (print-level-at-least-tp print)
                    (progn$ (cw "~%  (Minimal speedup: ~s0 to save " speedup-description)
                            (print-to-hundredths savings)
                            (cw " of ")
                            (print-to-hundredths time-to-beat)
                            (cw " seconds (~x0%))" percent-saved)))))
         (and (print-level-at-least-tp print)
              (progn$  (cw "~%  (Slower: ~s0: " speedup-description)
                       (print-to-hundredths time)
                       (cw " vs ")
                       (print-to-hundredths time-to-beat)
                       (cw " seconds)")
                       )))))

;; Returns state.
;; Each line printed starts with a newline.
;rename?
(defun try-to-drop-runes-from-defthm (runes body hints otf-flg time-to-beat print state)
  (declare (xargs :guard (and (true-listp runes)
                              (booleanp otf-flg)
                              (rationalp time-to-beat)
                              (print-levelp print))
                  :mode :program
                  :stobjs state))
  (if (endp runes)
      state
    (let ((rune-to-drop (first runes)))
      (mv-let (erp provedp time state)
        (prove$-nice-with-time body
                               (disable-items-in-hints hints (list rune-to-drop) nil)
                               nil ; instructions
                               otf-flg
                               time-to-beat ; time-limit ; warning: not portable!
                               nil          ; step-limit
                               state)
        (if erp
            (prog2$ (er hard? 'try-to-drop-runes-from-defthm "Error trying to disable ~x0." rune-to-drop)
                    state)
          (progn$ (maybe-print-speedup-message provedp time time-to-beat (concatenate 'string "Disable " (print-to-string rune-to-drop)) print)
                  (try-to-drop-runes-from-defthm (rest runes) body hints otf-flg time-to-beat print state)))))))

;; Prints suggested ways to speed up EVENT, which should be a defthm (or a variant, like defthmd, that supports :hints).
;; Returns (mv erp state).
;; Currently, this does the following:
;; - tries disabling each rune that was used in the original proof.
;; - tries :induct t if the proof used induction, in case time was wasted before reverting to induction
;; TODO: Compare to speed-up-defrule.  Keep in sync, or merge them.
(defun speed-up-defthm (event print state)
  (declare (xargs :guard (print-levelp print) ; todo: caller doesn't allow t?
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
      ;; Do the proof and time it:
      (mv-let (erp provedp original-time state)
        ;; This seems to save the event-data, at least the rules used:
        (prove$-twice-with-time body
                                hints
                                nil
                                otf-flg
                                nil ; time-limit
                                nil ; step-limit
                                state)
        (if erp
            (mv erp state)
          (if (not provedp)
              (prog2$ (er hard? 'speed-up-defthm "~x0 was expected to prove, but it failed." name)
                      (mv :failed state))
            (if (< original-time 1/100) ; todo: make this threshold customizable
                (prog2$ (and (print-level-at-least-tp print)
                             (progn$ (cw "  ~%(Not trying to speed up ~x0 because it only takes " name)
                                     (print-to-hundredths original-time)
                                     (cw " seconds)~%")))
                        (mv nil state))
              ;; It's worth trying to speed up:
              (prog2$ (and (print-level-at-least-tp print)
                           (progn$ (cw "(Original time for ~x0: " name)
                                   (print-to-hundredths original-time)
                                   (cw " seconds)~%")))
                      ;; Get the list of runes used in the proof:
                      (let* ((runes-used (get-event-data 'rules state))
                             ;; Try dropping each rule that contributed to the proof
                             (state (try-to-drop-runes-from-defthm (drop-fake-runes runes-used) body hints otf-flg original-time print state))
                             ;; If the proof used induction, try again with :induct t (maybe time was wasted before reverting to proof by induction)
                             (state (if (exists-induction-runep runes-used)
                                        (mv-let (erp provedp time-with-induct-t state)
                                          (prove$-nice-with-time body
                                                                 (merge-hint-setting-into-hint :induct t "Goal" hints)
                                                                 nil ; instructions
                                                                 otf-flg
                                                                 original-time
                                                                 nil ; step-limit
                                                                 state)
                                          (if erp
                                              (prog2$ (cw "~%   Error adding :induct t." name)
                                                      state)
                                            (if provedp
                                                (prog2$ (maybe-print-speedup-message provedp time-with-induct-t original-time "Add :induct t hint on Goal" print)
                                                        state)
                                              (prog2$ (and (print-level-at-least-tp print) (cw "~%   Adding :induct t caused the proof to break."))
                                                      ;; todo: print something here in verbose mode
                                                      state))))
                                      state)))
                        (mv nil state))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns state.  Prints a suggestion if disabling RUNE beforehand can significantly speed up EVENT.
;; Each line printed starts with a newline.
(defun try-to-drop-rune-from-event (rune event time-to-beat state)
  (declare (xargs :guard (rationalp time-to-beat)
                  :mode :program
                  :stobjs state))
  ;; Record the start time:
  (mv-let (start-time state)
    (get-real-time state)
    ;; Try the event with the rune disabled::
    (mv-let (erp state)
      (submit-and-revert-event `(saving-event-data (progn (in-theory (disable ,rune))
                                                          ,event))
                               nil nil state)
      ;; Record the end time:
      (mv-let (end-time state)
        (get-real-time state)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp state).
;; Each line printed starts with a newline.
(defun speed-up-defrule (event state)
  (declare (xargs :mode :program
                  :stobjs state))
  (let ((name (cadr event)))
    ;; Record the start time:
    (mv-let (start-time state)
      (get-real-time state)
      ;; Do the proof and time it (todo: do it twice, like we do for defthm, for better timings):
      (mv-let (erp state)
        (submit-and-revert-event `(saving-event-data ,event) nil nil state)
        ;; Record the end time:
        (mv-let (end-time state)
          (get-real-time state)
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
                (let* ((runes-used (runes-used-for-event name state)))
                  (if (not runes-used)
                      (prog2$ (cw "~%WARNING: No runes reported as used by ~x0." name)
                              (mv nil state))
                    (let ((state (try-to-drop-runes-from-event (drop-fake-runes runes-used) event elapsed-time state)))
                      (mv nil state))))))))))))

;; Returns (mv erp state).
(defun speed-up-event-fn (form print state)
  (declare (xargs :guard (print-levelp print) ; todo: finish threading this through
                  :mode :program
                  :stobjs state))
  (if (not (consp form))
      (prog2$ (er hard? 'speed-up-event-fn "~x0 is not a valid event.")
              (mv :invalid-event state))
    (let ((fn (ffn-symb form)))
      (case fn
        ((defthm defthmd) (speed-up-defthm form print state))
        ((defrule defruled) (speed-up-defrule form state))
        (otherwise (prog2$ (er hard? 'speed-up-event-fn "Unsupported event: ~X01." form nil)
                           (mv :unsupported-event state)))))))

(defmacro speed-up-event (form &key (print ':brief))
  `(speed-up-event-fn ',form ',print state))

;; TODO: Add a way to apply to all events in a book.
