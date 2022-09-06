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

;; TODO: Support adding a hook to run on each kind of event.
;; TODO: Time the events and alert the user when improvements slow things down.
;; TODO: Set the cbd if needed
;; TODO: Collect the suggested improvements and print them at the end.
;; TODO: Detect redundant include-books
;; TODO: Call the linter
;; TODO: Time each type of event and print a report
;; TODO: Start by making sure we can replay the book (and time it).
;; TODO: Special treatment for any books used to define this tool (will be redundant)
;; TODO: Add the ability to run on many files
;; TODO: Add the ability to suppress slow stuff (like dropping a local event or an include-book and trying the entire file).

(include-book "kestrel/file-io-light/read-objects-from-file" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)

;move
;; Returns (mv erp nil state).
(defun submit-event-error-triple (event print state)
  (declare (xargs :guard (and (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp state)
    (submit-event-helper event print nil state)
    (mv erp nil state)))

;; Reads and then submits all the events in FILENAME.
;; Returns (mv erp state).
;; Example: (replay-book "helper.lisp" state)
(defun replay-book (filename state)
  (declare (xargs :guard (stringp filename)
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp events state)
    (read-objects-from-file filename state)
    (if erp
        (mv erp state)
      (let ((state (submit-events events state)))
        (mv nil ; no error
            state)))))

;; Submits the EVENTS.  If an error is encountered, it is returned and further events are ignored.
;; Returns (mv erp state).
(defun submit-and-check-events (events print state)
  (declare (xargs :guard (and (true-listp events)
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (if (endp events)
      (mv nil state)
    (mv-let (erp state)
      (submit-event-helper (first events) print nil state)
      (if erp
          (mv erp state)
        (submit-and-check-events (rest events) print state)))))

;; Returns (mv erp nil state).  This version returns an error-triple, so it can
;; be used with revert-world.
;; TODO: use a prover-step-limit for these!  Maybe call get-event-data on the original events.
(defun submit-and-check-events-error-triple (events print state)
  (declare (xargs :guard (and (true-listp events)
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp state)
    (submit-and-check-events events print state)
    (mv erp nil state)))

;; Returns (mv successp state).  Doesn't change the world (because it reverts it after submitting the events).
(defun events-would-succeedp (events print state)
  (declare (xargs :guard (and (true-listp events)
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp res state)
    (revert-world (submit-and-check-events-error-triple events print state))
    (declare (ignore res))
    (mv (not erp) state)))

;; Returns (mv erp state).
(defun submit-event-expect-no-error (event print state)
  (declare (xargs :guard (member-eq print '(nil :brief :verbose))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp state)
    (submit-event-helper event print nil state)
    (if erp
        (prog2$ (cw "ERROR submitting event ~X01." event nil)
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
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state)
           (ignore rest-events) ; for now, todo: use these when trying to change the theorem statement
           )
  (prog2$
   (and print (cw "(Attempting to improve ~x0: " (first (rest event))))
   (let* ((defthm-variant (first event))
          (defthm-args (rest event))
          (name (first defthm-args))
          (term (second defthm-args))
          (keyword-value-list (rest (rest defthm-args)))
          (hintsp (assoc-keyword :hints keyword-value-list))
          ;; TODO: Try deleting each hint separately
          ;; TODO: Try deleting the :otf-flg
          ;; TODO: Try deleting/weakening hyps
          (event-without-hints `(,defthm-variant ,name ,term ,@(remove-keyword :hints keyword-value-list))))
     (if (not hintsp)
         ;; No hints, so just submit the defthm:
         (prog2$ (and print (cw "No improvement found.)~%"))
                 (submit-event-helper event nil nil state))
       ;; There are hints, so lets try without them:
       (mv-let (erp val state)
         (revert-world (submit-event-error-triple event-without-hints nil state))
         (declare (ignore val))
         (if erp
             ;; The hints are needed, so submit the event unchanged:
             ;; TODO: It's a pity to do it again here.
             (prog2$ (cw "No improvement found.)~%")
                     (submit-event-helper event nil nil state))
           (prog2$ (cw "~%IMPROVEMENT: The hints on ~x0 are unnecessary.)~%" name)
                   ;; The hints are not needed, so submit the defthm without them:
                   ;; TODO: This means we submit the event twice -- can we do something other than call revert-world above?
                   (submit-event-helper event-without-hints nil nil state))))))))

;; Returns (mv erp state).
(defun improve-event (event rest-events print state)
  (declare (xargs :guard (and (true-listp rest-events)
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (case (car event)
    (local
     ;; For a local event, try skipping it and see if the rest of the events
     ;; work.  If so, deleting the event should be safe, since the event is local.
     (mv-let (successp state)
       (events-would-succeedp rest-events nil state)
       (if successp
           ;; This event can simply be skipped:  TODO: Still, try improving it (it may be a defthm, etc.)?
           ;; TODO: Skipping this may change the improvements we suggest on later events, so perhaps we should not skip it?
           (prog2$ (cw "NOTE: The local event ~X01 can be skipped.~%" event nil)
                   (mv nil state))
         ;;failed to submit the rest of the events, so we can't just skip this one:
         (progn$ ;; (cw "Note: The local event ~x0 cannot be skipped.~%" event)
          (submit-event-expect-no-error event nil state)))))
    (defthm (improve-defthm-event event rest-events print state))
    ;; TODO: Try dropping include-books.
    ;; TODO: Add more event types here.
    (t (submit-event-expect-no-error event nil state))))

;; Returns (mv erp state)
(defun improve-events (events print state)
  (declare (xargs :guard (true-listp events)
                  :mode :program
                  :stobjs state))
  (if (endp events)
      (mv nil state)
    (mv-let (erp state)
      (improve-event (first events) (rest events) print state)
      (if erp
          (mv erp state)
        (improve-events (rest events) print state)))))

;; Returns (mv erp state).
;; Example: (IMPROVE-BOOK "helper.lisp" state)
;; TODO: Add support for :dir
;; TODO: Set the CBD first
(defun improve-book-fn (bookname ; no extension
                        print
                        state)
  (declare (xargs :guard (stringp bookname)
                  :mode :program ; because this calls submit-events
                  :stobjs state))
  (prog2$
   (and print (cw "~%Attempting to improve ~x0.~%" bookname))
   (mv-let (erp events state)
     (read-objects-from-file (concatenate 'string bookname ".lisp") state)
     (if erp
         (mv erp state)
       (prog2$ (and print (cw "~x0 contains ~x1 events.~%" bookname (len events)))
               (improve-events events print state))))))

(defmacro improve-book (bookname ; no extension
                        &key
                        (print ':brief))
  `(improve-book-fn ,bookname ,print state))
