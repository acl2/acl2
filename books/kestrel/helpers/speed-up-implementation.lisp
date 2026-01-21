; A utility that suggests ways to speed up events and books
;
; Copyright (C) 2023-2025 Kestrel Institute
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
;; TODO: Try removing cases hints
;; TODO: TODO: Handle theorems not at the top level
;; TODO: Handle defthm-flags
;; TODO: Try different ruler-extenders
;; todo: disallow print nil?

(include-book "replay-book-helpers") ; for load-port-file-if-exists
(include-book "books-in-subtree")
(include-book "kestrel/file-io-light/read-book-contents" :dir :system)
(include-book "kestrel/utilities/widen-margins" :dir :system)
(include-book "kestrel/utilities/prove-dollar-nice" :dir :system)
(include-book "kestrel/utilities/theory-hints" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system)
(include-book "kestrel/utilities/runes" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)
(include-book "kestrel/utilities/print-levels" :dir :system)
(include-book "kestrel/utilities/print-to-string" :dir :system)
(include-book "kestrel/utilities/split-path" :dir :system)
(include-book "kestrel/utilities/magic-macroexpand1-dollar" :dir :system)
(include-book "kestrel/hints/combine-hints" :dir :system)
(include-book "kestrel/strings-light/strip-suffix-from-string" :dir :system)

;; Returns state
;move
(defun set-cbd-simple (cbd state)
  (declare (xargs :guard (stringp cbd)
                  :stobjs state
                  :mode :program))
  (mv-let (erp val state)
    (set-cbd-fn cbd state)
    (declare (ignore val))
    (if erp
        (prog2$ (er hard? 'set-cbd-simple "Failed to set the cbd to ~x0." cbd)
                state)
      state)))

;; move these?

(verify-termination get-event-data-1)
;(verify-guards get-event-data-1) ; todo: needs a guard, perhaps (and (symbolp key) (symbol-alistp event-data)).
;; Requires NAME to have been submitted inside a call of saving-event-data.
(defund runes-used-for-event (name state)
  (declare (xargs :stobjs state
                  :mode :program))
  (get-event-data-1 'rules (cadr (hons-get name (f-get-global 'event-data-fal state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; these are in seconds:
(defconst *minimum-time-savings-to-report* 1/10)
(defconst *minimum-event-time-to-speed-up* 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tests whether any of the RUNES is an induction rune.
;; TODO: Generalize.
(defund exists-rune-of-classp (runes class)
  (declare (xargs :guard (and (true-listp runes)
                              (keywordp class))))
  (if (endp runes)
      nil
    (let ((rune (first runes)))
      (or (and (consp rune)
               (eq class (car rune)))
          (exists-rune-of-classp (rest runes) class)))))

(defund filter-runes-of-class (runes class)
  (declare (xargs :guard (and (true-listp runes)
                              (keywordp class))))
  (if (endp runes)
      nil
    (let ((rune (first runes)))
      (if (and (consp rune)
               (eq class (car rune)))
          (cons rune (filter-runes-of-class (rest runes) class))
        (filter-runes-of-class (rest runes) class)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun current-linear-rules (world)
  (declare (xargs :guard (plist-worldp world)
                  :mode :program))
  (filter-runes-of-class (current-theory-fn ':here world) :linear))

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

;; Returns (mv erp seconds state) where erp is non-nil if the event failed.
(defun submit-and-revert-event-with-time (event print throw-errorp state)
  (declare (xargs :guard (and (member-eq print '(nil :brief t :verbose))
                              (booleanp throw-errorp))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  ;; Record the start time:
  (mv-let (start-time state)
    (get-real-time state)
    ;; Submit and revert the event:
    (mv-let (erp state)
      (submit-and-revert-event event print throw-errorp state)
      ;; Record the end time:
      (mv-let (end-time state)
        (get-real-time state)
        (if erp
            (mv erp nil state)
          (let* ((elapsed-time (- end-time start-time)))
            (mv nil elapsed-time state)))))))

;; Returns (mv erp seconds state) where erp is non-nil if the event failed.
;; We time the event twice in case one is slow (e.g., if garbage collection happens to occur):
(defun submit-and-revert-event-twice-with-time (event print throw-errorp state)
  (declare (xargs :guard (and (member-eq print '(nil :brief t :verbose))
                              (booleanp throw-errorp))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp elapsed-time1 state)
    (submit-and-revert-event-with-time event print throw-errorp state)
    (if erp
        (mv erp nil state)
      (mv-let (erp elapsed-time2 state)
        (submit-and-revert-event-with-time event print throw-errorp state)
        (if erp
            (mv erp nil state)
          ;; We return the min, so as to try to get the time without garbage collection:
          (mv nil (min elapsed-time1 elapsed-time2) state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; returns a string
(defun abbreviate-event (event)
  (declare (xargs :guard t
                  :mode :program))
  (if (not (and (consp event)
                (symbolp (car event))))
      (er hard? 'abbreviate-event "Unexpected event: ~X01." event nil)
    (let ((fn (car event)))
      (case fn
        (local (if (= 1 (len (cdr event)))
                   (concatenate 'string "(local "
                                (abbreviate-event (cadr event))
                                ")")
                 (er hard? 'abbreviate-event "Unexpected event: ~X01." event nil) ;; "(local ...)" ; can this happen?
                 ))
        (include-book (print-to-string event))
        (otherwise
         (concatenate 'string
                      "("
                      (symbol-name (car event))
                      (if (not (consp (rest event)))
                          ")"
                        (if (symbolp (cadr event))
                            ;; example (defblah name ...)
                            (concatenate 'string " " (symbol-name (cadr event))
                                         (if (consp (rest (rest event)))
                                             " ...)"
                                           ")"))
                          ;; todo: do better in this case?
                          ;; example (progn (defun foo ...) ...)
                          (concatenate 'string " ...)")))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun maybe-print-speedup-message (provedp time time-to-beat speedup-description min-time-savings print)
  (declare (xargs :guard (and (booleanp provedp)
                              (rationalp time)
                              (<= 0 time)
                              (rationalp time-to-beat)
                              (<= 0 time-to-beat)
                              (stringp speedup-description)
                              (rationalp min-time-savings) ; in seconds
                              (print-levelp print))))
  (and provedp
       (if (< time time-to-beat)
           (let* ((savings (- time-to-beat time))
                  (percent-saved (floor (* 100 (/ savings time-to-beat)) 1)))
             (if (<= min-time-savings savings)
                 (progn$ (cw "~%  Speedup: ")
                         (print-to-hundredths savings)
                         (cw "s (~x0%): ~s1." percent-saved speedup-description))
               (and (print-level-at-least-tp print)
                    (progn$ (cw "~%  Minimal Speedup: ")
                            (print-to-hundredths savings)
                            (cw "s (~x0%): ~s1." percent-saved speedup-description)))))
         (and (print-level-at-least-tp print)
              (progn$ (cw "~%  (Slower: ~s0: " speedup-description)
                      (print-to-hundredths time)
                      (cw " vs ")
                      (print-to-hundredths time-to-beat)
                      (cw " seconds)"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns state.
;; Each line printed starts with a newline.
;rename?
;; Does not change the world.
(defun try-hints-for-defthm (hint-description-alist body otf-flg time-to-beat min-time-savings print state)
  (declare (xargs :guard (and (alistp hint-description-alist)
                              (booleanp otf-flg)
                              (rationalp time-to-beat)
                              (print-levelp print))
                  :mode :program
                  :stobjs state))
  (if (endp hint-description-alist)
      state
    (let* ((entry (first hint-description-alist))
           (hints (car entry))
           (description (cdr entry)))
      (prog2$
        (and (print-level-at-least-tp print) (cw "~%Trying ~x0:" description))
        (mv-let (erp provedp time state)
          (prove$-nice-with-time body
                                 hints
                                 nil ; instructions
                                 otf-flg
                                 time-to-beat ; time-limit
                                 nil          ; step-limit
                                 state)
          (if erp
              (prog2$ (er hard? 'try-hints-for-defthm "Error trying hints ~x0 representing ~x1." hints description)
                      state)
            (progn$ (maybe-print-speedup-message provedp time time-to-beat description min-time-savings print)
                    (try-hints-for-defthm (rest hint-description-alist) body otf-flg time-to-beat min-time-savings print state))))))))

;; Returns a list of entries of the form (hints . description-string).
(defun hint-description-alist-that-disables-each-rune (runes hints acc)
  (declare (xargs :guard (and (true-listp runes)
                              (true-listp acc))
                  :mode :program ;todo
                  ))
  (if (endp runes)
      (reverse acc)
    (let* ((rune (first runes))
           (description (concatenate 'string "Disable " (print-to-string rune)))
           (hints-that-disable-rune (disable-items-in-hints hints (list rune) nil)))
      (hint-description-alist-that-disables-each-rune (rest runes)
                                                     hints
                                                     (cons (cons hints-that-disable-rune description)
                                                           acc)))))

;; Returns state.  Prints a suggestion if disabling RUNE beforehand can significantly speed up EVENT.
;; Each line printed starts with a newline.
;; Does not change the world.
(defun try-to-drop-rune-from-event (rune event time-to-beat min-time-savings state)
  (declare (xargs :guard (rationalp time-to-beat)
                  :mode :program
                  :stobjs state))
  ;; Try the event with the rune disabled::
  (mv-let (erp elapsed-time state)
    ;; todo: save event-data only on the second try?  or avoid that, since it can interfere with the timing?
    (submit-and-revert-event-twice-with-time `(saving-event-data (progn (in-theory (disable ,rune)) ; todo: event may re-enable the rune
                                                                  ,event)) nil nil state)
    (if erp
        state ; the event failed after doing the disable
      (if (member-equal rune (get-event-data 'rules state))
          ;; the disable didn't really work (perhaps there is an explicit enable hint), so don't recommend it
          (prog2$ (cw "Disablng ~x0 didn't really take effect." rune)
                  state)
        (if (< elapsed-time time-to-beat)
            (let* ((savings (- time-to-beat elapsed-time))
                   (percent-saved (floor (* 100 (/ savings time-to-beat)) 1)))
              (if (<= min-time-savings savings)
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
           state))))))

;; Returns state.  Prints suggestion for RUNES which, if disabled beforehand, lead to significant speed ups for EVENT.
;; Does not change the world.
(defun try-to-drop-runes-from-event (runes event time-to-beat min-time-savings state)
  (declare (xargs :guard (and (true-listp runes)
                              (rationalp time-to-beat))
                  :mode :program
                  :stobjs state))
  (if (endp runes)
      state
    (let ((state (try-to-drop-rune-from-event (first runes) event time-to-beat min-time-savings state)))
      (try-to-drop-runes-from-event (rest runes) event time-to-beat min-time-savings state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun runes-to-try-disabling (runes-used world)
  (declare (xargs :mode :program))
  (let* ((runes-used (drop-fake-runes runes-used)) ; todo: use cons-with-hint in this?
         (current-linear-rules (current-linear-rules world)))
    (add-to-set-equal '(:executable-counterpart tau-system)
                      (union-equal current-linear-rules
                                   runes-used))))

;; Prints suggested ways to speed up EVENT, which should be a defthm (or a variant, like defthmd, that supports :hints).
;; Returns (mv erp state).
;; Currently, this does the following:
;; - tries disabling each rune that was used in the original proof.
;; - tries disabling each :linear rune that is currently enabled (in case they slow things down but don't show up in the summary)
;; - tries turning off TAU
;; - tries :induct t if the proof used induction, in case time was wasted before reverting to induction
;; TODO: Compare to speed-up-defrule.  Keep in sync, or merge them.
;; todo: refactor to generate list of hints, with descriptions, to try.
;; Does not change the world.
;; TODO: What about corollaries?
(defun speed-up-defthm (event min-time-savings min-event-time print print-headerp state)
  (declare (xargs :guard (and (print-levelp print) ; todo: caller doesn't allow t?
                              (booleanp print-headerp))
                  :mode :program
                  :stobjs state))
  (prog2$
   (and print print-headerp (cw "~%For ~s0" (first (rest event)))) ; speedups are indented below this, and start with newlines
   (let* ( ;;(defthm-variant (first event))
          (defthm-args (rest event)) ; (defthm <name> <body> ...)
          (name (first defthm-args))
          (body (second defthm-args))
          (keyword-value-list (rest (rest defthm-args)))
          (hintsp (assoc-keyword :hints keyword-value-list))
          (hints (cadr hintsp))
          (otf-flgp (assoc-keyword :otf-flg keyword-value-list))
          (otf-flg (cadr otf-flgp))
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
             (prog2$
               (if print
                   (progn$ (cw " (")
                           (print-to-hundredths original-time)
                           (cw "s):"))
                 (cw ":"))
               (if (< original-time min-event-time)
                   (prog2$ (and (print-level-at-least-tp print)
                                (progn$ (cw "~%  (Not trying to speed up: only takes ")
                                        (print-to-hundredths original-time)
                                        (cw " seconds)")))
                           (mv nil state))
              ;; It's worth trying to speed up:
                 (prog2$ (and (print-level-at-least-tp print)
                              (progn$ (cw "~%  (Original time: ")
                                      (print-to-hundredths original-time)
                                      (cw " seconds)")))
                      ;; Get the list of runes used in the proof:
                         (let* ((runes-used (get-event-data 'rules state))
                                ;; Try disabling each rule that contributed to the proof:
                                (hint-description-alist (hint-description-alist-that-disables-each-rune (runes-to-try-disabling runes-used (w state)) hints nil))
                                ;; If the proof used induction, try with :induct t (maybe time was wasted before reverting to proof by induction):
                                (hint-description-alist (if (exists-rune-of-classp runes-used :induction)
                                                            (acons (merge-hint-setting-into-hint :induct t "Goal" hints) "Add :induct t hint on Goal" hint-description-alist)
                                                          hint-description-alist))
                                (state (try-hints-for-defthm hint-description-alist body otf-flg original-time min-time-savings print state)))
                           (mv nil state))))))))))))

;; Returns (mv erp state).
;; Each line printed starts with a newline.
;; TODO: Try the :induct t speedup as we do with defthms just above
;; Does not change the world.
(defun speed-up-defrule (event min-time-savings min-event-time print print-headerp state)
  (declare (xargs :mode :program
                  :guard (and (print-levelp print) ; todo: caller doesn't allow t?
                              (booleanp print-headerp))
                  :stobjs state))
  (prog2$
   (and print print-headerp (cw "~%For ~s0:" (first (rest event)))) ; speedups are indented below this, and start with newlines
   (let ((name (cadr event)))
     ;; Do the proof and time it
     ;; todo: consider excluding prep-lemmas and prep-books from the timing, somehow
     ;; could try dropping prep-books or any local prep lemmas -- see improve-book
     ;; todo: save event date only on the second try?  or avoid that, since it can interfere with the timing?
     (mv-let (erp elapsed-time state)
       (submit-and-revert-event-twice-with-time `(saving-event-data ,event) nil nil state)
       (if erp
           (prog2$ (er hard? 'speed-up-defrule "~x0 was expected to prove, but it failed." name)
                   (mv erp state))
         (if (< elapsed-time min-event-time)
             (progn$ ;; (cw "~%(Not trying to speed up ~x0 because it only takes " name)
              ;; (print-to-hundredths elapsed-time)
              ;; (cw " seconds)")
              (mv nil state))
           ;; Get the list of runes used in the proof:
           (let* ((runes-used (runes-used-for-event name state)))
             (if (not runes-used)
                 (prog2$ (cw "~%WARNING: No runes reported as used by ~x0." name)
                         (mv nil state))
               (let* ((rules-to-try-to-drop (runes-to-try-disabling runes-used (w state)))
                      (state (try-to-drop-runes-from-event rules-to-try-to-drop event elapsed-time min-time-savings state)))
                 (mv nil state))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag remove-untouchable)
(remove-untouchable protected-eval t)

(mutual-recursion

 ;; Submits the event, after printing suggestions for improving it.
 ;; Returns (mv erp state).
 ;; TODO: Handle more kinds of events, like defun!  And make-event!  Also verify-termination and verify-guards.
 ;; todo: expand macros, evaluate make-events (revert the world?),
 (defun speed-up-and-submit-event (event synonym-alist min-time-savings min-event-time print throw-errorp state)
   (declare (xargs :guard (and (print-levelp print) ; todo: finish threading this through
                               (booleanp throw-errorp))
                   :mode :program
                   :stobjs state))
   (if (not (consp event))
       (prog2$ (cw "Error: ~x0 is not an event we can handle." event)
               (mv :invalid-event state))
     (let* ((fn (ffn-symb event))
            ;; See if FN is an alias for some other command
            (fn (let ((res (assoc-eq fn synonym-alist)))
                  (if res
                      (cdr res)
                    fn))))
       (case fn
         ((defthm defthmd) (mv-let (erp state)
                             (speed-up-defthm event min-time-savings min-event-time print t state)
                             (if erp
                                 (mv erp state)
                               ;; Skip the proof:
                               (submit-event `(skip-proofs ,event) nil t state))))
         ((defrule defruled defrulel defruledl) (mv-let (erp state)
                                                  (speed-up-defrule event min-time-savings min-event-time print t state)
                                                  (if erp
                                                      (mv erp state)
                                                    (submit-event `(skip-proofs ,event) nil t state))))
         ;; todo: try dropping local events (that is a kind of speed-up) -- see improve-book
         (local (speed-up-and-submit-event (farg1 event) synonym-alist min-time-savings min-event-time print throw-errorp state)) ; strip the local ; todo: this submits it as non-local (ok?)
         ;; For a call of with-output, the form is the last arg:
         (with-output (speed-up-and-submit-event (car (last (fargs event))) synonym-alist min-time-savings min-event-time print throw-errorp state))
         ;; Things we don't try to speed up (but improve-book could try to change in-theory events):
         ;; TODO: Add to this list (see :doc events):
         ((in-package
           defconst
           deflabel
           defmacro defmacro+
           defstobj
           defstub
           deftheory defthy
           defttag
           defxdoc defxdoc+
           include-book
           in-theory
           set-case-split-limitations
           set-ignore-ok set-state-ok set-irrelevant-formals-ok set-well-founded-relation
           set-induction-depth-limit
           set-induction-depth-limit!
           skip-proofs
           table
           theory-invariant
           value-triple)
          (submit-event `(skip-proofs ,event) nil t state))
         ;; For an encapsulate, we attempt to speed up each of the subsidiary
         ;; events (submitting each as we go), then we revert the world and
         ;; finally submit the whole encapsulate:
         (encapsulate
             (let (;; (signatures (first (fargs event))) ; we ignore the signatures
                   (events (rest (fargs event))))
               (mv-let (erp val state)
                 (revert-world
                  (mv-let (erp state)
                    (speed-up-and-submit-events events synonym-alist min-time-savings min-event-time print throw-errorp state)
                    (mv erp :invisible state)))
                 (declare (ignore val))
                 (if erp
                     (mv erp state)
                   (submit-event `(skip-proofs ,event) nil t state)))))
         ;; For progn, we just process the subsidiary events in order (no need to revert the world and re-submit the event):
         (progn
           (let ((events (fargs event)))
             (speed-up-and-submit-events events synonym-alist min-time-savings min-event-time print throw-errorp state)))
         (make-event
           (let ((event (farg1 event)))
             (mv-let (erp result state)
               ;; todo: or use revert-world-on-error? (see comment in protected-eval)
               (revert-world
                 (protected-eval event
                                 'speed-up-and-submit-event
                                 'speed-up-and-submit-event
                                 state
                                 t))
               (if erp
                   (mv :error-in-make-event state)
                 (let ((result-event (car result))) ; todo: do anything with new-kpa and new-ttags-seen?
                   (speed-up-and-submit-event result-event synonym-alist min-time-savings min-event-time print throw-errorp state))))))
         (otherwise
          (if (macro-namep fn (w state))
              (progn$ ;; (cw "Macroexpanding ~x0.~%" event)
                      (speed-up-and-submit-event (magic-macroexpand1$$ event 'speed-up-and-submit-event (w state) state) synonym-alist min-time-savings min-event-time print throw-errorp state))
            (if throw-errorp
                (prog2$ (er hard? 'speed-up-event-fn "Unsupported event: ~s0.~%" (abbreviate-event event))
                        (mv :unsupported-event state))
              (prog2$ (cw "~%Unsupported event: ~s0." (abbreviate-event event))
                              ;; For speed, we skip the proofs (todo: can this interfere with calls to make-event?) when submitting the event:
                      (submit-event `(skip-proofs ,event) nil t state)))))))))

;; Submits each event, after printing suggestions for improving it.
;; Returns (mv erp state).
 (defun speed-up-and-submit-events (events synonym-alist min-time-savings min-event-time print throw-errorp state)
   (declare (xargs :guard (and (true-listp events)
                               (symbol-alistp synonym-alist)
                               (print-levelp print))
                   :mode :program
                   :stobjs state))
   (if (endp events)
       (mv nil state)
     (mv-let (erp state)
       (speed-up-and-submit-event (first events) synonym-alist min-time-savings min-event-time print throw-errorp state)
       (if erp
           (mv erp state)
         (speed-up-and-submit-events (rest events) synonym-alist min-time-savings min-event-time print throw-errorp state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun speed-up-event-fn (event synonym-alist min-time-savings min-event-time print state)
  (declare (xargs :guard (and (symbol-alistp synonym-alist)
                              (print-levelp print))
                  :mode :program
                  :stobjs state))
  (let* ((state (widen-margins state))
         ;; Suppress annoying time tracker messages.
         (fake (time-tracker-fn nil nil nil nil nil nil nil)) ; from :trans (time-tracker nil)
         (min-time-savings (if (eq :auto min-time-savings) *minimum-time-savings-to-report* min-time-savings))
         (min-event-time (if (eq :auto min-event-time) *minimum-event-time-to-speed-up* min-event-time)))
    (declare (ignore fake))
    (mv-let (erp state)
      (speed-up-and-submit-event event synonym-alist min-time-savings min-event-time print
                                 t ; throw error on unsupported event
                                 state)
      (prog2$ (cw "~%")
              (if erp
                  (mv erp nil state)
                (mv erp :invisible state))))))

;; Tries to speed up the given event but does not submit it.
;; See doc in doc.lisp.
(defmacro speed-up-event (event &key
                               (synonym-alist 'nil) ;; example '((local-defthm . defthm)) ; means treat local-defthm like defthm
                               (min-time-savings ':auto) ; in seconds
                               (min-event-time ':auto) ; in seconds
                               (print ':brief))
  `(speed-up-event-fn ',event ',synonym-alist ,min-time-savings ,min-event-time ',print
                      state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp state).
;; TODO: Set induction depth limit to nil?
(defun speed-up-book-fn-aux (bookname ; may include .lisp extension
                             dir      ; todo: allow a keyword?
                             synonym-alist
                             min-time-savings
                             min-event-time
                             print
                             state)
  (declare (xargs :guard (and (stringp bookname)
                              (or (eq :cbd dir)
                                  (stringp dir))
                              (symbol-alistp synonym-alist)
                              (or (rationalp min-time-savings) (eq :auto min-time-savings))
                              (or (rationalp min-event-time) (eq :auto min-event-time))
                              (member-eq print '(nil :brief t :verbose)))
                  :mode :program ; because this calls submit-events
                  :stobjs state))
  (let ((full-book-path (full-book-path bookname dir state)))
    (prog2$
      (and print (cw "~%~%(SPEEDING UP ~x0.~%" full-book-path)) ; matches the close paren below
      (let* ((old-cbd (cbd-fn state)) ; save the CBD so we can restore it below
             (full-book-dir (dir-of-path full-book-path))
             ;; We set the CBD so that the book is replayed in its own directory:
             (state (set-cbd-simple full-book-dir state))
             ;; Load the .port file, so that packages (especially) exist:
             (state (load-port-file-if-exists (strip-suffix-from-string ".lisp" full-book-path) state)))
        (mv-let (erp events state)
          (read-book-contents full-book-path state)
          (if erp
              (mv erp state)
            (let* ((state (widen-margins state))
                   ;; Suppress annoying time tracker messages.
                   (fake (time-tracker-fn nil nil nil nil nil nil nil)) ; from :trans (time-tracker nil)
                   (min-time-savings (if (eq :auto min-time-savings) *minimum-time-savings-to-report* min-time-savings))
                   (min-event-time (if (eq :auto min-event-time) *minimum-event-time-to-speed-up* min-event-time)))
              (declare (ignore fake))
              (progn$ (and (eq print :verbose) (cw "  (Book contains ~x0 forms.)~%" (len events)))
                      (mv-let (erp state)
                        (speed-up-and-submit-events events synonym-alist min-time-savings min-event-time print
                                                    nil ; no error for unknown events
                                                    state)
                        (let* ((state (unwiden-margins state))
                               (state (set-cbd-simple old-cbd state)))
                          (prog2$ (cw ")~%")
                                  (mv erp state))))))))))))

;; Returns (mv erp nil state).  Does not change the world.
(defun speed-up-book-fn (bookname ; no extension
                         dir
                         synonym-alist
                         min-time-savings ; in seconds
                         min-event-time ; in seconds
                         print
                         state)
  (declare (xargs :guard (and (stringp bookname)
                              (or (eq :cbd dir)
                                  (stringp dir))
                              (symbol-alistp synonym-alist)
                              (or (rationalp min-time-savings) (eq :auto min-time-savings))
                              (or (rationalp min-event-time) (eq :auto min-event-time))
                              (member-eq print '(nil :brief t :verbose)))
                  :mode :program ; because this calls submit-events
                  :stobjs state))
  (revert-world
   (mv-let (erp state)
     (speed-up-book-fn-aux bookname dir synonym-alist min-time-savings min-event-time print state)
     (mv erp :invisible state))))

;; Example: (SPEED-UP-BOOK "helper").  This makes no changes to the world, just
;; prints suggestions for speeding up the book.
;; todo: add doc
(defmacro speed-up-book (bookname ; no extension
                        &key
                        (dir ':cbd)
                        (synonym-alist 'nil) ;; example '((local-defthm . defthm)) ; means treat local-defthm like defthm
                        (min-time-savings ':auto) ; in seconds
                        (min-event-time ':auto) ; in seconds
                        (print ':brief))
  `(speed-up-book-fn ,bookname ,dir ,synonym-alist ,min-time-savings ,min-event-time ,print state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp nil state) where EVENT is usually (value-triple :invisible).
(defun speed-up-books-fn-aux (books dir synonym-alist min-time-savings min-event-time print state)
  (declare (xargs :guard (and (string-listp books)
                              (or (eq :cbd dir)
                                  (stringp dir))
                              (symbol-alistp synonym-alist)
                              (or (rationalp min-time-savings) (eq :auto min-time-savings))
                              (or (rationalp min-event-time) (eq :auto min-event-time))
                              (member-eq print '(nil :brief t :verbose)))
                  :stobjs state :mode :program))
  (if (endp books)
      (mv nil '(value-triple :invisible) state)
    (mv-let (erp val state)
      (speed-up-book-fn (first books) dir synonym-alist min-time-savings min-event-time print state)
      (declare (ignore val))
      (if erp
          (prog2$ (er hard? 'speed-up-books-fn-aux "Error improving ~x0." (first books))
                  (mv erp nil state))
        (speed-up-books-fn-aux (rest books) dir synonym-alist min-time-savings min-event-time print state)))))

;; Returns (mv erp nil state) where EVENT is usually (value-triple :invisible).
(defun speed-up-books-fn (dir subdirsp synonym-alist min-time-savings min-event-time print state)
  (declare (xargs :guard (and (or (eq :cbd dir)
                                  (stringp dir))
                              (booleanp subdirsp)
                              (symbol-alistp synonym-alist)
                              (or (rationalp min-time-savings) (eq :auto min-time-savings))
                              (or (rationalp min-event-time) (eq :auto min-event-time))
                              (member-eq print '(nil :brief t :verbose)))
                  :stobjs state :mode :program))
  (let* ((dir (if (eq dir :cbd) "." dir))
         (full-dir (canonical-pathname dir t state))
         ;; (state (set-cbd-simple full-dir state))
         )
    (mv-let (books state)
      (if subdirsp
          (books-in-subtree state)
        (books-in-dir state))
      (prog2$ (if subdirsp
                  (cw "~%(Will try to speed-up ~x0 books in ~s1 and subdirs.)" (len books) full-dir)
                (cw "~%(Will try to speed-up ~x0 books in ~s1.)" (len books) full-dir))
              ;; pass full-dir here?:
              (speed-up-books-fn-aux books dir synonym-alist min-time-savings min-event-time print state)))))

;; Tries to speed-up all books in DIR, not including books in subdirectories.
;; By default, uses the connected book directory for DIR.
(defmacro speed-up-books (&key
                         (synonym-alist 'nil) ;; example '((local-defthm . defthm)) ; means treat local-defthm like defthm
                         (min-time-savings ':auto) ; in seconds
                         (min-event-time ':auto)
                         (print ':brief)
                         ;; (dir ':cbd) ; doesn't work since the sys-call to get the list of books runs in the current dir
                         )
  `(make-event (speed-up-books-fn ':cbd ;;',dir
                                  nil ; do not look in subdirs
                                  ',synonym-alist ,min-time-savings ,min-event-time
                                  ,print state)))

;; Tries to speed-up all books in DIR, including books in subdirectories.
;; By default, uses the connected book directory for DIR.
(defmacro speed-up-books-in-subtree (&key
                                     (synonym-alist 'nil) ;; example '((local-defthm . defthm)) ; means treat local-defthm like defthm
                                     (min-time-savings ':auto) ; in seconds
                                     (min-event-time ':auto)
                                     (print ':brief)
                                    ;; (dir ':cbd) ; doesn't work since the sys-call to get the list of books runs in the current dir
                                     )
  `(make-event (speed-up-books-fn ':cbd ;;',dir
                                  t ; do look into subdirs
                                  ',synonym-alist ,min-time-savings ,min-event-time
                                  ',print state)))
