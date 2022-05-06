; Replaying the events in a book (perhaps with changes).
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

;; TODO: Support adding a hook to run on each kind of event

(include-book "kestrel/file-io-light/read-objects-from-file" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)

;; Returns (mv erp nil state).
(defun submit-event-error-triple (event print state)
  (declare (xargs :guard (and (member-eq print '(nil :brief :verbose)))
                  :mode :program ;; because we call trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp state)
    (submit-event-helper event print nil state)
    (mv erp nil state)))

;; Returns (mv erp state).
;; Example: (REPLAY-BOOK "helper.lisp" state)
(defun replay-book (filename state)
  (declare (xargs :guard (stringp filename)
                  :mode :program ; because this calls submit-events
                  :stobjs state))
  (mv-let (erp events state)
    (read-objects-from-file filename state)
    (if erp
        (mv erp state)
      (let ((state (submit-events events state)))
        (mv nil ; no error
            state)))))

;; Returns (mv erp state).
(defun submit-and-check-events (events print state)
  (declare (xargs :guard (and (true-listp events)
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ;; because we call trans-eval-error-triple
                  :stobjs state))
  (if (endp events)
      (mv nil state)
    (mv-let (erp state)
      (submit-event-helper (first events) print nil state)
      (if erp
          (mv erp state)
        (submit-and-check-events (rest events) print state)))))

;; Returns (mv erp nil state).
(defun submit-and-check-events-error-triple (events print state)
  (declare (xargs :guard (and (true-listp events)
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ;; because we call trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp state)
    (submit-and-check-events events print state)
    (mv erp nil state)))

;; Returns (mv erp state).
(defun submit-event-expect-no-error (event print state)
  (declare (xargs :guard (member-eq print '(nil :brief :verbose))
                  :mode :program ;; because we call trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp state)
    (submit-event-helper event print nil state)
    (if erp
        (prog2$ (cw "ERROR submitting event ~X01." event)
                (mv :error-submitting-event state))
      (mv nil state))))

;; ;; See if some events would be admitted, but undo them even if so.
;; ;; Returns (mv erp state) where ERP is non-nil if there was an error submitting the events.
;; (defun try-events-and-undo (events state)
;;   (declare (xargs :guard (true-listp events)
;;                   :mode :program
;;                   :stobjs state))
;;   (mv-let (erp state) ; make a deflabel to support undoing
;;     (submit-event-helper '(deflabel improve-book-undo-label) nil nil state)
;;     (if erp ; shouldn't happen
;;         (mv erp state)
;;       (mv-let (erp state)
;;         ;; todo: inhibit even errors in this?:
;;         (submit-and-check-events events nil ;print
;;                                  state)
;;         ;; Try to undo whatever was submitted:
;;         (mv-let (erp2 res state)
;;           (ubt-ubu-fn :ubt 'improve-book-undo-label state)
;;           (declare (ignore res erp2)) ; ERP determines whether we throw an error
;;           (mv erp state))))))

;; Returns (mv erp state).
(defun improve-defthm-event (event rest-events print state)
  (declare (xargs :guard (and (member-eq print '(nil :brief :verbose)))
                  :mode :program
                  :stobjs state)
           (ignore rest-events) ; for now
           )
  (let* ((defthm-variant (first event))
         (defthm-args (rest event))
         (name (first defthm-args))
         (term (second defthm-args))
         (keyword-value-list (rest (rest defthm-args)))
         (hintsp (assoc-keyword :hints keyword-value-list))
         (event-to-try `(,defthm-variant ,name ,term ,@(remove-keyword :hints keyword-value-list))))
    (if hintsp
        (mv-let (erp val state)
          (revert-world (submit-event-error-triple event-to-try print state))
          (declare (ignore val))
          (if erp
              ;; The hints are needed, so submit the event unchanged:
              (submit-event-helper event nil nil state)
            (prog2$ (cw "NOTE: The hints on ~x0 are unnecessary.~%" name)
                    ;; The hints are not, so submit the improved event: ;; TODO: This means we submit the event twice -- can we do something other than call revert world above?
                    (submit-event-helper event-to-try nil nil state))))
      (submit-event-helper event nil nil state))))

;; Returns (mv erp state).
(defun improve-event (event rest-events print state)
  (declare (xargs :guard (and (true-listp rest-events)
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program
                  :stobjs state))
  (case (car event)
    (local
     ;; For a local event, try skipping it and see if the rest of the events
     ;; work.  If so, that should be fine to do, since the event is local.
     (mv-let (erp res state)
       (revert-world (submit-and-check-events-error-triple rest-events nil state)) ; todo: use a prover-step-limit for these!  Maybe call get-event-data on the original events
       (declare (ignore res))
       (if (not erp)
           ;; This event can simply be skipped:  TODO: Still, try improving it (it may be a defthm, etc.)
           (prog2$ (cw "NOTE: The local event ~X01 can be skipped.~%" event nil)
                   (mv nil state))
         ;;failed to submit the rest of the events, so we can't just skip this one:
         (progn$ ;; (cw "Note: The local event ~x0 cannot be skipped.~%" event)
                 (submit-event-expect-no-error event print state)))))
    (defthm (improve-defthm-event event rest-events print state))
    ;; TODO: Add more event types here (e.g., for theorems try to remove hints
    (t (submit-event-expect-no-error event print state))))

;; Returns (mv erp state)
(defun improve-events (events state)
  (declare (xargs :guard (true-listp events)
                  :mode :program
                  :stobjs state))
  (if (endp events)
      (mv nil state)
    (mv-let (erp state)
      (improve-event (first events) (rest events) nil ; :brief
                     state)
      (if erp
          (mv erp state)
        (improve-events (rest events) state)))))

;; Returns (mv erp state).
;; Example: (IMPROVE-BOOK "helper.lisp" state)
;; TODO: Add support for :dir
;; TODO: Set the CBD first
(defun improve-book (bookname ; no extension
                     state)
  (declare (xargs :guard (stringp bookname)
                  :mode :program ; because this calls submit-events
                  :stobjs state))
  (mv-let (erp events state)
    (read-objects-from-file (concatenate 'string bookname ".lisp") state)
    (if erp
        (mv erp state)
      (improve-events events state))))
