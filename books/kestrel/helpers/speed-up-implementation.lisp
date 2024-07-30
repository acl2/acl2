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
;; TODO: Try removing cases hints
;; TODO: TODO: Handle theorems not at the top level
;; TODO: Handle defthm-flags
;; TODO: Try different ruler-extenders

(include-book "replay-book-helpers") ; for load-port-file-if-exists
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

;; in seconds
(defconst *minimum-time-savings-to-report* 1/10)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun abbreviate-event (event)
  (declare (xargs :guard t
                  :mode :program))
  (if (not (and (consp event)
                (symbolp (car event))))
      ;; todo: can this happen?
      "..."
    (let ((fn (car event)))
      (case fn
        (local (if (= 1 (len (cdr event)))
                   (concatenate 'string "(local "
                                (abbreviate-event (cadr event))
                                ")")
                 "(local ...)" ; can this happen?
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
(defun try-to-drop-runes-from-defthm (runes body hints otf-flg time-to-beat min-time-savings print state)
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
          (progn$ (maybe-print-speedup-message provedp time time-to-beat (concatenate 'string "Disable " (print-to-string rune-to-drop)) min-time-savings print)
                  (try-to-drop-runes-from-defthm (rest runes) body hints otf-flg time-to-beat min-time-savings print state)))))))

;; Returns state.  Prints a suggestion if disabling RUNE beforehand can significantly speed up EVENT.
;; Each line printed starts with a newline.
(defun try-to-drop-rune-from-event (rune event time-to-beat min-time-savings state)
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
                 state)))))))))

;; Returns state.  Prints suggestion for RUNES which, if disabled beforehand, lead to significant speed ups for EVENT.
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
(defun speed-up-defthm (event min-time-savings print print-headerp state)
  (declare (xargs :guard (and (print-levelp print) ; todo: caller doesn't allow t?
                              (booleanp print-headerp))
                  :mode :program
                  :stobjs state))
  (prog2$
   (and print print-headerp (cw "~%For ~s0" (first (rest event)))) ; speedups are indented below this, and start with newlines
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
             (prog2$
               (if print
                   (progn$ (cw " (")
                           (print-to-hundredths original-time)
                           (cw "s):"))
                 (cw ":"))
               (if (< original-time 1/100) ; todo: make this threshold customizable
                   (prog2$ (and (print-level-at-least-tp print)
                                (progn$ (cw "~%  (Not trying to speed up: only takes " name)
                                        (print-to-hundredths original-time)
                                        (cw " seconds)")))
                           (mv nil state))
              ;; It's worth trying to speed up:
                 (prog2$ (and (print-level-at-least-tp print)
                              (progn$ (cw "~%  (Original time: " name)
                                      (print-to-hundredths original-time)
                                      (cw " seconds)")))
                      ;; Get the list of runes used in the proof:
                         (let* ((runes-used (get-event-data 'rules state))
                                (rules-to-try-to-drop (runes-to-try-disabling runes-used (w state)))
                              ;; Try dropping each rule that contributed to the proof
                                (state (try-to-drop-runes-from-defthm rules-to-try-to-drop body hints otf-flg original-time min-time-savings print state))
                             ;; If the proof used induction, try again with :induct t (maybe time was wasted before reverting to proof by induction)
                                (state (if (exists-rune-of-classp runes-used :induction)
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
                                                   (prog2$ (maybe-print-speedup-message provedp time-with-induct-t original-time "Add :induct t hint on Goal" min-time-savings print)
                                                           state)
                                                 (prog2$ (and (print-level-at-least-tp print) (cw "~%   Adding :induct t caused the proof to break."))
                                                      ;; todo: print something here in verbose mode
                                                         state))))
                                         state)))
                           (mv nil state))))))))))))

;; Returns (mv erp state).
;; Each line printed starts with a newline.
;; TODO: Try the :induct t speedup as we do with defthms just above
(defun speed-up-defrule (event min-time-savings print print-headerp state)
  (declare (xargs :mode :program
                  :guard (and (print-levelp print) ; todo: caller doesn't allow t?
                              (booleanp print-headerp))
                  :stobjs state))
  (prog2$
   (and print print-headerp (cw "~%For ~s0:" (first (rest event)))) ; speedups are indented below this, and start with newlines
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
                     (let* ((rules-to-try-to-drop (runes-to-try-disabling runes-used (w state)))
                            (state (try-to-drop-runes-from-event rules-to-try-to-drop event elapsed-time min-time-savings state)))
                       (mv nil state)))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp state).
;; TODO: Handle more kinds of events, like defun!
(defun speed-up-event-fn (form synonym-alist min-time-savings print throw-errorp state)
  (declare (xargs :guard (and (print-levelp print) ; todo: finish threading this through
                              (booleanp throw-errorp))
                  :mode :program
                  :stobjs state))
  (if (not (and (consp form)
                (consp (cdr form))))
      (prog2$ (cw "Note: ~x0 is not an event we can handle." form)
              (mv :invalid-event state))
    (let* ((fn (ffn-symb form))
           ;; See if FN is an alias for some other command
           (fn (let ((res (assoc-eq fn synonym-alist)))
                 (if res
                     (cdr res)
                   fn))))
      (case fn
        ((defthm defthmd) (speed-up-defthm form min-time-savings print t state))
        ((defrule defruled) (speed-up-defrule form min-time-savings print t state))
        (local (speed-up-event-fn (cadr form) synonym-alist min-time-savings print throw-errorp state)) ; strip the local ; todo: this submits it as non-local (ok?)
        ;; Things we don't try to speed up (but improve-book could try to change in-theory events):
        ;; TODO: Add to this list (see :doc events):
        ((in-package defconst deflabel defmacro
                     defstobj
                     defstub
                     deftheory
                     defthy
                     defttag
                     defxdoc
                     include-book in-theory theory-invariant
                     set-ignore-ok set-state-ok set-irrelevant-formals-ok set-well-founded-relation
                     table)
         (mv nil state))
        (otherwise (if throw-errorp
                       (prog2$ (er hard? 'speed-up-event-fn "Unsupported event: ~X01." form nil)
                               (mv :unsupported-event state))
                     (prog2$ (cw "~%Unsupported event: ~X01." form nil)
                             (mv nil state))))))))

(defmacro speed-up-event (form &key
                               (synonym-alist 'nil) ;; example '((local-dethm . defthm)) ; means treat local-defthm like defthm
                               (min-time-savings ':auto) ; in seconds
                               (print ':brief))
  `(speed-up-event-fn ',form ',synonym-alist ,min-time-savings ',print
                      t ; throw error on unsupported event
                      state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Submits the event, after printing suggestions for improving it.
;; Returns (mv erp state).
(defun speed-up-events-aux (event synonym-alist min-time-savings print state)
  (declare (xargs :guard (print-levelp print) ; todo: finish threading this through
                  :mode :program
                  :stobjs state))
  (mv-let (erp state)
    (speed-up-event-fn event synonym-alist min-time-savings print
                       nil ; no error on unhandled things
                       state)
    (if nil ; erp ; todo
        (mv erp state)
      (submit-event event nil t state))))

;; Submits each event, after printing suggestions for improving it.
;; Returns (mv erp state).
(defun speed-up-events (events synonym-alist min-time-savings print state)
  (declare (xargs :guard (and (true-listp events)
                              (symbol-alistp synonym-alist)
                              (print-levelp print))
                  :mode :program
                  :stobjs state))
  (if (endp events)
      (mv nil state)
    (mv-let (erp state)
      (speed-up-events-aux (first events) synonym-alist min-time-savings print state)
      (if erp
          (mv erp state)
        (speed-up-events (rest events) synonym-alist min-time-savings print state)))))

;; Returns (mv erp state).
;; TODO: Set induction depth limit to nil?
(defun speed-up-book-fn-aux (bookname ; may include .lisp extension
                             dir      ; todo: allow a keyword?
                             synonym-alist
                             min-time-savings
                             print
                             state)
  (declare (xargs :guard (and (stringp bookname)
                              (or (eq :cbd dir)
                                  (stringp dir))
                              (symbol-alistp synonym-alist)
                              (or (rationalp min-time-savings) (eq :auto min-time-savings))
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this calls submit-events
                  :stobjs state))
  (mv-let (erp events full-book-path state)
    (read-book-contents bookname dir state)
    (if erp
        (mv erp state)
      (let* ((state (widen-margins state))
             ;; Suppress annoying time tracker messages.
             (fake (time-tracker-fn nil nil nil nil nil nil nil)) ; from :trans (time-tracker nil)
             (min-time-savings (if (eq :auto min-time-savings) *minimum-time-savings-to-report* min-time-savings)))
        (declare (ignore fake))
        (prog2$
          (and print (cw "~%~%(SPEEDING UP ~x0.~%" full-book-path)) ; matches the close paren below
          (let* ((old-cbd (cbd-fn state))
                 (full-book-dir (dir-of-path full-book-path))
                ;; We set the CBD so that the book is replayed in its own directory:
                 (state (set-cbd-simple full-book-dir state))
                ;; Load the .port file, so that packages (especially) exist:
                 (state (load-port-file-if-exists (strip-suffix-from-string ".lisp" full-book-path) state)))
            (progn$ (and (eq print :verbose) (cw "  (Book contains ~x0 forms.)~%" (len events)))
                    (mv-let (erp state)
                      (speed-up-events events synonym-alist min-time-savings print state)
                      (let* ((state (unwiden-margins state))
                             (state (set-cbd-simple old-cbd state)))
                        (prog2$ (cw ")~%")
                                (mv erp state)))))))))))

;; Returns (mv erp nil state).  Does not change the world.
(defun speed-up-book-fn (bookname ; no extension
                         dir
                         synonym-alist
                         min-time-savings ; in seconds
                         print
                         state)
  (declare (xargs :guard (and (stringp bookname)
                              (or (eq :cbd dir)
                                  (stringp dir))
                              (symbol-alistp synonym-alist)
                              (or (rationalp min-time-savings) (eq :auto min-time-savings))
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this calls submit-events
                  :stobjs state))
  (revert-world
   (mv-let (erp state)
     (speed-up-book-fn-aux bookname dir synonym-alist min-time-savings print state)
     (mv erp :invisible state))))

;; Example: (SPEED-UP-BOOK "helper").  This makes no changes to the world, just
;; prints suggestions for speeding up the book.
(defmacro speed-up-book (bookname ; no extension
                        &key
                        (dir ':cbd)
                        (synonym-alist 'nil) ;; example '((local-dethm . defthm)) ; means treat local-defthm like defthm
                        (min-time-savings ':auto) ; in seconds
                        (print ':brief))
  `(speed-up-book-fn ,bookname ,dir ,synonym-alist ,min-time-savings ,print state))
