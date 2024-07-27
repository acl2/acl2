; Replaying the events in a book (perhaps with changes).
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: Working prototype

;; TODO: Support adding a hook to run on each kind of event.
;; TODO: Time the events and alert the user when improvements slow things down.
;; TODO: Call the linter?
;; TODO: Time each type of event and print a report
;; TODO: Start by making sure we can replay the book (and time it).
;; TODO: Special treatment for any books used to define this tool (will be redundant, don't recommend dropping their include-books, even withn local)
;; TODO: Add the ability to suppress slow stuff (like dropping a local event or an include-book and trying the entire file).
;; TODO: Improve hints for defuns
;; TODO: Detect :guard-debug
;; TOOD: Suppress suggestions to drop set-default-parents and things to disable built-in rules.
;; TODO: Handle verify-guards
;; TODO: Handle progn
;; TODO: Handle encapsulate
;; TOOD: Handle defsection
;; TODO: Handle define (prepwork, ///, etc.)
;; TODO: Handle defrule
;; TODO: Handle with-output
;; TODO: Perhaps try turning off tau, to see if that saves a lot of time.

(include-book "kestrel/file-io-light/read-book-contents" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system) ; todo: use prove$ instead
(include-book "kestrel/utilities/strings" :dir :system)
(include-book "kestrel/utilities/widen-margins" :dir :system)
(include-book "kestrel/utilities/split-path" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "kestrel/utilities/all-included-books" :dir :system)
(include-book "kestrel/utilities/extend-pathname-dollar" :dir :system)
(include-book "kestrel/utilities/maybe-add-dot-lisp-extension" :dir :system)
(include-book "kestrel/lists-light/remove-nth" :dir :system)
(include-book "kestrel/world-light/defthm-or-defaxiom-symbolp" :dir :system)
(include-book "kestrel/hints/remove-hints" :dir :system)
(include-book "kestrel/strings-light/split-string-repeatedly" :dir :system)
(include-book "kestrel/strings-light/strip-suffix-from-strings" :dir :system)
(include-book "replay-book-helpers") ; todo: reduce, for load-port...
(include-book "linter")
(include-book "speed-up-implementation") ; also gets us abbreviate-event
(local (include-book "kestrel/typed-lists-light/string-listp" :dir :system))


;move
(defund duplicate-items-aux (lst acc)
  (declare (xargs :guard (and (true-listp lst)
                              (true-listp acc))))
  (if (endp lst)
      acc
    (let ((item (first lst))
          (rest (rest lst)))
      (if (and (member-equal item rest) ; it's a dup
               (not (member-equal item acc)) ; don't report more than once
               )
          (duplicate-items-aux (rest lst) (cons item acc))
        (duplicate-items-aux (rest lst) acc)))))

;; Returns a list of the items that appear more than once in LST.
;move
(defund duplicate-items (lst)
  (declare (xargs :guard (true-listp lst)))
  (duplicate-items-aux lst nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag books-in-subtree) ; for sys-call+ below

;; Looks for .lisp files in the current subtree.
;; Returns (mv book-paths state) where the BOOK-PATHS have no .lisp extensions.
;move
(defun books-in-subtree (state)
  (declare (xargs :stobjs state))
  (mv-let (erp filename-lines state)
    (sys-call+ "find" '("." "-name" "*.lisp") state)
    (if erp
        (prog2$ (er hard? 'books-in-subtree "Failed to find books: ~x0." erp)
                (mv nil state))
      (mv (strip-suffix-from-strings ".lisp" (remove-equal "" (split-string-repeatedly filename-lines #\Newline)))
          state))))

;move
;; Looks for .lisp files in the current subtree.
;; Returns (mv book-paths state) where the BOOK-PATHS have no .lisp extensions.
(defun books-in-dir (state)
  (declare (xargs :stobjs state))
  (mv-let (erp filename-lines state)
    (sys-call+ "find" '("." "-maxdepth" "1" "-name" "*.lisp") state)
    (if erp
        (prog2$ (er hard? 'books-in-dir "Failed to find books: ~x0." erp)
                (mv nil state))
      (mv (strip-suffix-from-strings ".lisp" (remove-equal "" (split-string-repeatedly filename-lines #\Newline)))
          state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move
;; Returns (mv erp nil state).
(defun submit-event-error-triple (event print state)
  (declare (xargs :guard (and (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp state)
    (submit-event event print nil state)
    (mv erp nil state)))

;; Submits the EVENTS.  If an error is encountered, it is returned and further events are ignored.
;; Returns (mv erp state).
(defun submit-and-check-events (events skip-proofsp skip-localsp print state)
  (declare (xargs :guard (and (true-listp events)
                              (booleanp skip-proofsp)
                              (booleanp skip-localsp)
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (if (endp events)
      (mv nil state)
    (let* ((event (first events))
           ;; TODO: How to skip all local things embedded in progns (including those generated by macros)?
           (localp (and (consp event)
                        (eq 'local (ffn-symb event))))
           (skipp (and localp skip-localsp)))
      (if skipp
          (submit-and-check-events (rest events) skip-proofsp skip-localsp print state)
        (mv-let (erp state)
          (submit-event (if skip-proofsp `(skip-proofs ,event) event)
                        nil ;print
                        nil state)
          (if erp
              (mv erp state)
            (submit-and-check-events (rest events) skip-proofsp skip-localsp print state)))))))

;; Returns (mv erp nil state).  This version returns an error-triple, so it can
;; be used with revert-world.
;; TODO: use a prover-step-limit for these!  Maybe call get-event-data on the original events.
(defun submit-and-check-events-error-triple (events skip-proofsp skip-localsp print state)
  (declare (xargs :guard (and (true-listp events)
                              (booleanp skip-proofsp)
                              (booleanp skip-localsp)
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp state)
    (submit-and-check-events events skip-proofsp skip-localsp print state)
    (mv erp nil state)))

;; Returns (mv successp state).  Doesn't change the world (because it reverts it after submitting the events).
;; TODO: Suppress error printing here.
(defun events-would-succeedp (events print state)
  (declare (xargs :guard (and (true-listp events)
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  ;; First, quickly detect whether something would fail in the second pass of
  ;; certify-book (local incompatibility check).  We skip local events here to
  ;; prevent a local event from making a bad name mention seem ok.  We skip
  ;; proofs to help this fail fast.  TODO: Do we really need to start this check at the beginning
  ;; of the book, in case there was already a local event which masks a failure here?
  (mv-let (erp res state)
    (revert-world (submit-and-check-events-error-triple events t t print state))
    (declare (ignore res))
    (if erp
        (mv nil state) ; some event gave an error
      ;; TODO: Can we do something else fast here, like checking all the hints but not doing the proofs?  May cause includes to be done again...
      ;; Try again for real (without skip-proofs):
      (mv-let (erp res state)
        (revert-world (submit-and-check-events-error-triple events nil nil print state))
        (declare (ignore res))
        (if erp
            (mv nil state) ; some event gave an error
          (mv t state)     ; all events succeeded
          )))))

;; Returns (mv erp state).
(defun submit-event-expect-no-error (event print state)
  (declare (xargs :guard (member-eq print '(nil :brief :verbose))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp state)
    (submit-event event print nil state)
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
;;     (submit-event '(deflabel improve-book-undo-label) nil nil state)
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
             (concatenate 'string (newline-string) "  Drop " (print-to-string remove-item))
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
    (mv-let (removal-type new-keyword-value-list)
      (remove-from-hint-keyword-value-list-in-nth-way n keyword-value-list)
      (acons new-keyword-value-list
             ;; the removal-type currently include the "remove":
             (concatenate 'string (newline-string) "   For \"" goal-name "\": " (decode-removal-type removal-type))
             (remove-hint-parts-and-label-aux (+ 1 n) ways keyword-value-list goal-name)))))

;; Returns an alist from new keyword-value-lists to decsriptions
(defun remove-hint-parts-and-label (keyword-value-list goal-name)
  (declare (xargs :mode :program))
  (let ((ways (num-ways-to-remove-from-hint-keyword-value-list keyword-value-list)))
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

;; Submits and improves the event.
;; Returns (mv erp state).
;; TODO: Use limits based on how many steps were needed for the original proof.
(defun improve-defthm-event (event rest-events print state)
  (declare (xargs :guard (and (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state)
           (ignore rest-events) ; for now, todo: use these when trying to change the theorem statement
           )
  (prog2$
   (and print (cw " (For ~x0:" (first (rest event))))
   (let* ((defthm-variant (first event))
          (defthm-args (rest event))
          (name (first defthm-args))
          (body (second defthm-args))
          (keyword-value-list (rest (rest defthm-args)))
          (hintsp (assoc-keyword :hints keyword-value-list))
          (hints (cadr hintsp)))
     (if (defthm-or-defaxiom-symbolp name (w state))
         ;; It already exists (presumably identical):
         (prog2$ (cw "   Drop (redundant).)~%") ; no more checking to do, though we have seen a redundant event with a bad subst in the hints...
                 (mv nil state))
       (let* ( ;; TODO: Try deleting the :otf-flg
              ;; Try removing hints:
              (state (if (not hintsp)
                         state ; no hints to try dropping
                       (let ((event-without-hints `(,defthm-variant ,name ,body ,@(remove-keyword :hints keyword-value-list)))
                             (drop-hints-message (concatenate 'string (newline-string) "   Drop all :hints.")))
                         (mv-let (improvement-foundp state)
                           (try-improved-event event-without-hints drop-hints-message state)
                           (if improvement-foundp
                               state
                             ;; could not drop all hints, so try one by one:
                             (let* ((alist (defthms-with-removed-hints defthm-variant name body hints)))
                               (mv-let (improvement-foundp state)
                                 (try-improved-events alist nil state)
                                 (declare (ignore improvement-foundp)) ;todo: don't bother to return this?
                                 state)))))))
              ;; Apply the linter:
              (state (lint-defthm name (translate-term body 'improve-defthm-event (w state)) hints nil 100000 state)))
         ;; Try to speed up the proof:
         (mv-let (erp state)
           (speed-up-defthm event print nil state)
           (if erp
               (mv erp state)
             (prog2$ (and print (cw ")~%"))
                     ;; TODO: This means we may submit the event multiple times -- can we do something other than call revert-world above?
                     (submit-event event nil nil state)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp state).
;; TODO: Check for redundant.
(defun improve-defun-event (event rest-events print state)
  (declare (xargs :guard (and (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state)
           (ignore rest-events) ; for now, todo: use these when trying to change the theorem statement
           )
  (progn$
   (and print (cw " (For ~x0:" (first (rest event))))
   ;; todo: try to improve hints, etc.
   ;; Must submit it before we lint it:
   (mv-let (erp state)
     (submit-event event nil nil state)
     (if erp
         (mv erp state)
       (let* ((fn (cadr event))
              (state (lint-defun fn t   ;assume-guards
                                 nil    ; suppress
                                 100000 ;step-limit
                                 state)))

         (prog2$ (and print (cw ")~%"))
                 (mv nil state)))))))

;;TODO: Do more here, like we do for defthm!
;; Returns (mv erp state).
(defun improve-defrule-event (event rest-events print state)
  (declare (xargs :guard (and (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state)
           (ignore rest-events) ; for now, todo: use these when trying to change the theorem statement
           )
  (prog2$
   (and print (cw " (For ~x0:" (first (rest event))))
   (mv-let (erp state)
     (speed-up-defrule event print nil state)
     (declare (ignore erp)) ; todo: why?
     (prog2$ (and print (cw ")~%"))
             (submit-event event nil nil state)))))

;; Currently, there is nothing to try for an in-package.
(defun improve-in-package-event (event rest-events print state)
  (declare (xargs :guard (and (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state)
           (ignore rest-events) ; for now, todo: use these when trying to change the theorem statement
           )
  (prog2$ (and print (cw " (For ~x0:)~%" event))
          (mv nil state)))

;; ;; Test whether the given book is incldued in the wrld.  FILENAME should include the .lisp extension.
;; (defun book-includedp (dir filename state)
;;   (declare (xargs :guard (and (or (keywordp dir)
;;                                   (stringp dir))
;;                               (stringp filename))
;;                   :mode :program
;;                   :stobjs state))
;;   (member-equal (extend-pathname$ dir filename state) (all-included-books (w state))))

;; Submits EVENT and prints suggestions for improving it.
;; Returns (mv erp state).
(defun improve-include-book-event (event rest-events initial-included-books print state)
  (declare (xargs :guard (and (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state)
           (ignore print))
  ;; For an include-book, try skipping it and see if the rest of the events
  ;; work.
  (prog2$
   (cw " (For ~x0:" event)
   (let* ((book (cadr event))
          (dir (cadr (assoc-keyword :dir (rest (fargs event))))) ; often nil
          (full-path (extend-pathname$ (or dir ".") (concatenate 'string book ".lisp") state)))
     (if (member-equal full-path initial-included-books)
         ;; Redundant and unable to trying dropping it (probably because it is included by improve-book itself):
         (prog2$ (cw "~%   Skipping: Already included before improve-book was called.)~%")
                 (submit-event-expect-no-error event nil state))
       (if (member-equal full-path (all-included-books (w state)))
           (prog2$ (cw "~%   Drop include (redundant).)~%" event nil)
                   ;; We submit the event anyway, so as to not interfere with subsequent suggested improvements:
                   (submit-event-expect-no-error event nil state))
         (mv-let (successp state)
           (events-would-succeedp rest-events nil state)
           (if successp
               ;; This event could be skipped: (but that might break books that use
               ;; this book) TODO: Also try reducing what is included?  TODO:
               ;; Somehow avoid suggesting to drop books that introduce names used
               ;; in macros (they will seem like they can be dropped, unless the
               ;; book contains an actual call of the macro).
               (prog2$ (cw "~%   Drop include.)~%" event nil)
                       ;; We submit the event anyway, so as to not interfere with subsequent suggested improvements:
                       (submit-event-expect-no-error event nil state))
             ;;failed to submit the rest of the events, so we can't just skip this one:
             (progn$ ;; (cw " Cannot be dropped.)~%" event)
              (cw ")~%" event)
              (submit-event-expect-no-error event nil state)))))))))

(defun improve-local-event (event rest-events initial-included-books print state)
  (declare (xargs :guard (and (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state)
           (ignore initial-included-books print))
  ;; For a local event, try skipping it and see if the rest of the events
  ;; work.  If so, deleting the event should be safe, since the event is local.
  (prog2$
   (cw " (For ~s0:" (abbreviate-event event))
   (mv-let (successp state)
     (events-would-succeedp rest-events nil state)
     (if successp
         ;; This event could be skipped:  TODO: Still, try improving it (it may be a defthm, etc.)?
         ;; TODO: What if this is redundant, given stuff already in the world?
         (prog2$ (cw "~%   Drop ~X01.)~%" event nil)
                 ;; We submit the event anyway, so as to not interfere with subsequent suggested improvements:
                 (submit-event-expect-no-error event nil state))
       ;;failed to submit the rest of the events, so we can't just skip this one:
       (progn$ ;(cw " Cannot be dropped.)~%" event)
        (cw ")~%" event)
        (submit-event-expect-no-error event nil state))))))

;; Submits EVENT and prints suggestions for improving it.
;; Returns (mv erp state).
(defun improve-event (event rest-events initial-included-books print state)
  (declare (xargs :guard (and (true-listp rest-events)
                              (member-eq print '(nil :brief :verbose))
                              (string-listp initial-included-books))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  ;; TODO: Do the submit-event outside this (but currently defuns must be submitted before linting):
  ;; todo: for some of these, we should print the event before submitting it:
  ;; TODO: Add more event types here.
  (case (car event)
    ;; Since it's just an assert, we can continue after an error, so we just warn:
    ((assert-event assert-equal)
     (let ((state (submit-event-handle-error event nil :warn state)))
       (mv nil state)))
    ((defcong) (submit-event event nil nil state) ; todo: try to clean up hints
     )
    ((defconst) (submit-event event nil nil state) ; todo: check the body?
     )
    ((deflabel) (submit-event event nil nil state) ; can't think of anything to do for labels
     )
    ((defmacro) (submit-event event nil nil state) ; todo: check the body?
     )
    ((defrule defruled) (improve-defrule-event event rest-events print state))
    ((defstub) (submit-event event nil nil state) ; anything to do?
     )
    ((defthm defthmd) (improve-defthm-event event rest-events print state))
    ((defun defund) (improve-defun-event event rest-events print state))
    ((defxdoc defxdoc+) (submit-event event nil nil state) ; todo: anything to check?
     )
    ((encapsulate) (submit-event event nil nil state) ; todo: handle! may be easy if no constrained functions and no local events
     )
    (include-book (improve-include-book-event event rest-events initial-included-books print state))
    ((in-package) (improve-in-package-event event rest-events print state))
    ((in-theory) (submit-event event nil nil state) ; todo: check if redundant, consider dropping (check the time difference)
     )
    (local (improve-local-event event rest-events initial-included-books print state))
    ((theory-invariant) (submit-event event nil nil state) ; todo: handle!  could warn about a name that is not defined.
     )
    ((verify-guards) (submit-event event nil nil state) ; todo: check if redundant, improve hints
     )
    (t (prog2$ (cw " (Just submitting unhandled event ~x0)~%" (abbreviate-event event))
               (submit-event-expect-no-error event nil state)))))

;; Submits each event, after printing suggestions for improving it.
;; Returns (mv erp state).
(defun improve-events-aux (events initial-included-books print state)
  (declare (xargs :guard (and (true-listp events)
                              (string-listp initial-included-books))
                  :mode :program
                  :stobjs state))
  (if (endp events)
      (mv nil state)
    (mv-let (erp state)
      (improve-event (first events) (rest events) initial-included-books print state)
      (if erp
          (mv erp state)
        (improve-events-aux (rest events) initial-included-books print state)))))

(defun improve-events (events initial-included-books print state)
  (declare (xargs :guard (and (true-listp events)
                              (string-listp initial-included-books))
                  :mode :program
                  :stobjs state))
  (prog2$ (let ((dupes (duplicate-items events)))
            (and dupes
                 ;; Some dupes may be okay, such as (logic) and (program), but
                 ;; that seems like bad style.
                 (cw "(Duplicate events: ~X01.)~%" dupes nil)))
          ;; todo: do local incompat checking without include-books (or making them local) here?
          (improve-events-aux events initial-included-books print state)))

;; Returns (mv erp state).
;; TODO: Set induction depth limit to nil?
(defun improve-book-fn-aux (bookname ; may include .lisp extension
                            dir      ; todo: allow a keyword?
                            print
                            state)
  (declare (xargs :guard (and (stringp bookname)
                              (or (eq :cbd dir)
                                  (stringp dir))
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
             )
        (declare (ignore fake))
        (prog2$
         (and print (cw "~%~%(IMPROVING ~x0.~%" full-book-path)) ; matches the close paren below
         (let* ((old-cbd (cbd-fn state))
                (full-book-dir (dir-of-path full-book-path))
                ;; We set the CBD so that the book is replayed in its own directory:
                (state (set-cbd-simple full-book-dir state))
                ;; Load the .port file, so that packages (especially) exist:
                (state (load-port-file-if-exists (strip-suffix-from-string ".lisp" full-book-path) state))
                ;; We cannot try omitting these from the book:
                (initial-included-books (all-included-books (w state))))
           (progn$ (and (eq print :verbose) (cw "  Book contains ~x0 forms.~%~%" (len events)))
                   (mv-let (erp state)
                     (improve-events events initial-included-books print state)
                     (let* ((state (unwiden-margins state))
                            (state (set-cbd-simple old-cbd state)))
                       (prog2$ (cw ")~%")
                               (mv erp state)))))))))))

;; Returns (mv erp nil state).  Does not change the world.
(defun improve-book-fn (bookname ; no extension
                        dir
                        print
                        state)
  (declare (xargs :guard (and (stringp bookname)
                              (or (eq :cbd dir)
                                  (stringp dir))
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this calls submit-events
                  :stobjs state))
  (revert-world
   (mv-let (erp state)
     (improve-book-fn-aux bookname dir print state)
     (mv erp :invisible state))))

;; Example: (IMPROVE-BOOK "helper").  This makes no changes to the world, just
;; prints suggestions for improvement.
(defmacro improve-book (bookname ; no extension
                        &key
                        (dir ':cbd)
                        (print ':brief))
  `(improve-book-fn ,bookname ,dir ,print state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp nil state) where EVENT is usually (value-triple :invisible).
(defun improve-books-fn-aux (books dir print state)
  (declare (xargs :guard (and (string-listp books)
                              (or (eq :cbd dir)
                                  (stringp dir))
                              (member-eq print '(nil :brief :verbose)))
                  :stobjs state :mode :program))
  (if (endp books)
      (mv nil '(value-triple :invisible) state)
    (mv-let (erp val state)
      (improve-book-fn (first books) dir print state)
      (declare (ignore val))
      (if erp
          (prog2$ (er hard? 'improve-books-fn-aux "Error improving ~x0." (first books))
                  (mv erp nil state))
        (improve-books-fn-aux (rest books) dir print state)))))

;; Returns (mv erp nil state) where EVENT is usually (value-triple :invisible).
(defun improve-books-fn (print dir subdirsp state)
  (declare (xargs :guard (and (member-eq print '(nil :brief :verbose))
                              (or (eq :cbd dir)
                                  (stringp dir))
                              (booleanp subdirsp))
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
                  (cw "~%(Will try to improve ~x0 books in ~s1 and subdirs.)" (len books) full-dir)
                (cw "~%(Will try to improve ~x0 books in ~s1.)" (len books) full-dir))
              ;; pass full-dir here?:
              (improve-books-fn-aux books dir print state)))))

;; Tries to improve all books in DIR, not including books in subdirectories.
;; By default, uses the connected book directory for DIR.
(defmacro improve-books (&key
                         (print ':brief)
                         ;; (dir ':cbd) ; doesn't work since the sys-call to get the list of books runs in the current dir
                         )
  `(make-event (improve-books-fn ',print ':cbd ;;',dir
                                 nil state)))

;; Tries to improve all books in DIR, including books in subdirectories.
;; By default, uses the connected book directory for DIR.
(defmacro improve-books-in-subtree (&key
                                    (print ':brief)
                                    ;; (dir ':cbd) ; doesn't work since the sys-call to get the list of books runs in the current dir
                                    )
  `(make-event (improve-books-fn ',print ':cbd ;;',dir
                                 t state)))
