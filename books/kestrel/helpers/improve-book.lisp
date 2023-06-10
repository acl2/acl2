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
(include-book "kestrel/utilities/submit-events" :dir :system) ; todo: use prove$ instead
(include-book "kestrel/lists-light/remove-nth" :dir :system)
(include-book "kestrel/hints/remove-hints" :dir :system)

;move
;; Returns (mv erp nil state).
(defun submit-event-error-triple (event print state)
  (declare (xargs :guard (and (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp state)
    (submit-event-helper event print nil state)
    (mv erp nil state)))

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
        (prog2$ (cw "ERROR (~x0) submitting event ~X12.~%" erp event nil)
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

;; Tries the EVENT and prints the MESSAGE if the event succeeds.
;; Returns (mv improvement-foundp state).
;; TODO: Make the limits customizable.
(defun try-improved-event (event message state)
  (declare (xargs :stobjs state
                  :mode :program))
  (mv-let (erp val state)
    (revert-world (submit-event-error-triple `(with-prover-time-limit 10 (with-prover-step-limit 100000 ,event)) nil state))
    (declare (ignore val))
    (if erp
        ;; failure (don't print the message):
        (mv nil state)
      ;; success:
      (prog2$ (cw "~s0" message)
              (mv t state)))))

;; Tries each event and, if it succeeds, prints the corresponding message.
;; Returns (mv improvement-foundp state).
;; Does not change the world.
(defun try-improved-events (event-message-alist improvement-foundp state)
  (declare (xargs :stobjs state
                  :mode :program))
  (if (endp event-message-alist)
      (mv improvement-foundp state)
    (let* ((pair (first event-message-alist))
           (event (car pair))
           (message (cdr pair)))
      (mv-let (improvedp state)
        (try-improved-event event message state)
        (try-improved-events (rest event-message-alist)
                             (or improvedp improvement-foundp)
                             state)))))

;; Returns an alist mapping reduced lists to string descriptions
(defun remove-and-label-nth-items (n lim items)
  (declare (xargs :guard (and (natp n)
                              (natp lim)
                              (true-listp items))
                  :mode :program))
  (if (or (not (mbt (natp n)))
          (not (mbt (natp lim)))
          (<= lim n))
      nil
    (let* ((remove-item (nth n items))
           (new-list (remove-nth n items)))
      (acons new-list
             (fms-to-string "  Drop ~x0." (acons #\0 remove-item nil))
             (remove-and-label-nth-items (+ 1 n) lim items)))))

;; Returns an alist mapping theorems to try to string descriptions
(defun theorems-with-new-hints (defthm-variant name term alist)
  (declare (xargs :mode :program))
  (if (endp alist)
      nil
    (let* ((pair (first alist))
           (new-hints (car pair))
           (description (cdr pair)))
      (acons `(,defthm-variant ,name ,term :hints ,new-hints)
             description
             (theorems-with-new-hints defthm-variant name term (rest alist))))))

;; Returns an alist from new keyword-value-lists to decsriptions
(defun remove-hint-parts-and-label-aux (n ways keyword-value-list goal-name)
  (declare (xargs :mode :program))
  (if (or (not (mbt (natp n)))
          (not (mbt (natp ways)))
          (<= ways n))
      nil
    (mv-let (breakage-type new-keyword-value-list)
      (break-hint-keyword-value-list-in-nth-way n keyword-value-list)
      (acons new-keyword-value-list
             ;; the breakage-type currently include the "remove":
             (fms-to-string "  For ~x0: ~x1" (acons #\0 goal-name (acons #\1 breakage-type nil)))
             (remove-hint-parts-and-label-aux (+ 1 n) ways keyword-value-list goal-name)))))

;; Returns an alist from new keyword-value-lists to decsriptions
(defun remove-hint-parts-and-label (keyword-value-list goal-name)
  (declare (xargs :mode :program))
  (let ((ways (num-ways-to-break-hint-keyword-value-list keyword-value-list)))
    (remove-hint-parts-and-label-aux 0 ways keyword-value-list goal-name)))

(defun replace-hints-for-goal-name (hints goal-name new-keyword-value-list)
  (declare (xargs :guard (and (true-listp hints)
                              (stringp goal-name)
                              (keyword-value-listp new-keyword-value-list))
                   :mode :program))
  (if (endp hints)
      nil
    (let ((hint (first hints)))
      (if (and (consp hint)
               (equal goal-name (car hint)) ; could allow case to differ, in general but not needed now
               )
          (cons (cons (car hint) new-keyword-value-list)
                (rest hints) ; i suppose we could replace later, if there are dups
                )
        (cons hint (replace-hints-for-goal-name (rest hints) goal-name new-keyword-value-list))))))

;; Returns an alist from new hint-lists to decsriptions
(defun replace-hint-with-each (alist-with-new-keyword-value-lists goal-name all-hints)
  (declare (xargs :mode :program))
  (if (endp alist-with-new-keyword-value-lists)
      nil
    (let* ((pair (first alist-with-new-keyword-value-lists))
           (new-keyword-value-list (car pair))
           (description (cdr pair))
           (new-hints (replace-hints-for-goal-name all-hints goal-name new-keyword-value-list)))
      (acons new-hints
             description
             (replace-hint-with-each (rest alist-with-new-keyword-value-lists) goal-name all-hints)))))

;; Goes through the HINTS. For each, may use many replacements for it.
;; Returns an alist mapping reduced hint-lists to string descriptions.
;; RES is an alist from hint-lists to descriptions
(defun remove-and-label-hint-parts (hints theorem-name all-hints res)
  (declare (xargs :guard (and (true-listp hints)
                              (symbolp theorem-name)
                              (true-listp all-hints)
                              (alistp res))
                  :mode :program))
  (if (endp hints)
      (reverse res)
    (let* ((hint (first hints)))
      (if (not (and (consp hint)
                    (stringp (car hint))))
          ;; not a regular hint, so nothing to do
          (remove-and-label-hint-parts (rest hints) theorem-name all-hints res)
        ;; regular hint:
        (let* ((goal-name (car hint))
               (keyword-value-list (cdr hint))
               (alist-with-new-keyword-value-lists (remove-hint-parts-and-label keyword-value-list goal-name))
               (alist-with-replacements-for-hint (replace-hint-with-each alist-with-new-keyword-value-lists goal-name all-hints)))
          (remove-and-label-hint-parts (rest hints) theorem-name all-hints (append alist-with-replacements-for-hint res)))))))

;; Returns an alist mapping theorems with reduced lists to string descriptions of what was removed.
(defun defthms-with-removed-hints (defthm-variant name term hints)
  (declare (xargs :mode :program))
  (let* ((len (len hints))
         (hint-lists-to-try (append (remove-and-label-nth-items 0 len hints) ;remove entire hints like ("goal ...)
                                    (remove-and-label-hint-parts hints name hints nil) ; remove parts of hints
                                    )))
    (theorems-with-new-hints defthm-variant name term hint-lists-to-try)))

;; Submits and improves the events.
;; Returns (mv erp state).
;; TODO: Use limits based on how many steps were needed for the original proof.
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
          ;; TODO: Try deleting the :otf-flg
          ;; TODO: Try deleting/weakening hyps
          (event-without-hints `(,defthm-variant ,name ,term ,@(remove-keyword :hints keyword-value-list)))
          (alist (if (not hintsp)
                     nil ; nothing to do (currently)
                   (let ((hints (cadr hintsp)))
                     (acons event-without-hints
                            (fms-to-string "IMPROVEMENT for ~x0: Drop the :hints.~%" (acons #\0 name nil))
                            (defthms-with-removed-hints defthm-variant name term hints))))))
     (mv-let (improvement-foundp state)
       (try-improved-events alist nil state)
       (prog2$ (if (not improvement-foundp)
                   (and print (cw "No improvement found.)~%"))
                 (and print (cw ")~%")))
               ;; TODO: This means we may submit the event multiple times -- can we do something other than call revert-world above?
               (submit-event-helper event nil nil state))))))

;; Submit EVENT, after printing suggestions for improving it.
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
           ;; TODO: What if this is redundant, given stuff already in the world?
           (prog2$ (cw "IMPROVEMENT: Drop the local event ~X01.~%" event nil)
                   (mv nil state))
         ;;failed to submit the rest of the events, so we can't just skip this one:
         (progn$ ;; (cw "(Note: The local event ~x0 cannot be skipped.)~%" event)
                 (submit-event-expect-no-error event nil state)))))
    ((defthm defthmd) (improve-defthm-event event rest-events print state))
    ;; TODO: Try dropping include-books.
    ;; TODO: Add more event types here.
    (t (submit-event-expect-no-error event nil state))))

;; Submits each event, after printing suggestions for improving it.
;; Returns (mv erp state).
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
;; TODO: Add support for :dir
;; TODO: Set the CBD first
;; TODO: Read in the .port file first, if it exists.
;; TODO: Set induction depth limit to nil?
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

;; Example: (IMPROVE-BOOK "helper").  This makes no changes to the world, just
;; prints suggestions for improvement.
(defmacro improve-book (bookname ; no extension
                        &key
                        (print ':brief))
  `(revert-world
    (mv-let (erp state)
      (improve-book-fn ,bookname ,print state)
      (mv erp nil state))))
