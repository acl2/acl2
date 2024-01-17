; A tool to try proof advice on some or all defthms in a book
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: change to HELP package

(include-book "replay-book-helpers")
(include-book "advice")
(include-book "kestrel/utilities/split-path" :dir :system)
(include-book "kestrel/utilities/maybe-add-dot-lisp-extension" :dir :system)

;; NOTE: See eval-models for a similar but newer tool.

;; TODO: Try advice on defthms inside encapsulates (and perhaps other forms).
;; TODO: Consider excluding advice that uses a different version of the same library (e.g., rtl/rel9).
;; TODO: Instead of removing all :hints, just remove one hint-setting or rune (in enable or disable or e/d).  Use the acl2data files since they include info on how to break theorems?
;; TODO: Somehow remove libraries and see whether the advice can find something that works.
;; TODO: Consider removing hyps, but how can we tell whether a suggested hyp is good?

;; Example:
;; (replay-book-with-advice "../lists-light/append.lisp")

;; Determine whether to try advice for EVENT, given the list of THEOREMS-TO-TRY.
;; TODO: Add support for trying advice on local defthms.
(defun advice-eventp (event theorems-to-try)
  (declare (xargs :guard (or (eq :all theorems-to-try)
                             (symbol-listp theorems-to-try))))
  (and (or (call-of 'defthm event) ; todo: maybe handle thm, defrule, rule, etc.  maybe handle defun and variants (termination and guard proof)
           (call-of 'defthmd event))
       (consp (cdr event))
       (or (eq :all theorems-to-try)
           (member-eq (cadr event) theorems-to-try))))

;; Determines whether the Proof Advice tool can find advice for the given DEFTHM.  Either way, this also submits DEFTHM.
;; Returns (mv erp result state) where result is :yes, :no, :maybe (not currently used?), or :trivial.
(defun submit-defthm-event-with-advice (defthm num-recs-per-model current-book-absolute-path improve-recsp print model-info-alist timeout state)
  (declare (xargs :guard (and (natp num-recs-per-model)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp improve-recsp)
                              (acl2::print-levelp print)
                              (help::model-info-alistp model-info-alist)
                              (natp timeout))
                  :mode :program
                  :stobjs state))
  (b* ((defthm-variant (car defthm)) ; defthm or defthmd, etc.
       (theorem-name (cadr defthm))
       (theorem-body (caddr defthm))
       (rule-classes-result (assoc-keyword :rule-classes (cdddr defthm)))
       (rule-classes (if rule-classes-result
                         (cadr rule-classes-result)
                       ;; this really means don't put in any :rule-classes arg at all:
                       '(:rewrite)))
       (hints-presentp (if (assoc-keyword :hints (cdddr defthm)) t nil))
       (- (cw "(ADVICE: ~x0: " theorem-name))
       ;; Ignores any given hints (for now - todo: see the breakage-type stuff in eval-models.lisp):
       ((mv erp successp best-rec state)
        (help::best-rec-for-theorem theorem-name
                                    theorem-body
                                    (acl2::translate-term theorem-body 'submit-defthm-event-with-advice (w state))
                                    nil           ; don't use any hints
                                    nil           ; theorem-otf-flg
                                    defthm
                                    num-recs-per-model
                                    current-book-absolute-path
                                    t ; avoid using a book to prove its own checkpoints
                                    improve-recsp
                                    print
                                    model-info-alist timeout
                                    nil ; debug
                                    100000 ; step-limit (TODO: give time/steps proportional to what was needed for the original theorem?)
                                    5 ; time-limit
                                    '(:add-hyp) ; disallow :add-hyp, because no hyps are needed for these theorems
                                    1           ; max-wins
                                    t ; suppress warning about trivial rec, because below we ask if "original" is the best rec and handle trivial recs there
                                    nil ; todo: consider t here for start and return?
                                    state))
       ;; TODO: Maybe track errors separately?  Might be that a step limit was reached before checkpoints could even be generated, so perhaps that counts as a :no?
       ((when erp) (mv erp :no state)))
    (if (not successp)
        (prog2$ (cw "NO)~%") ; close paren matches (ADVICE
                (b* (;; Submit the original defthm, so we can keep going:
                     ((mv erp state) (submit-event defthm nil nil state))
                     ((when erp) (mv erp :no state)))
                  (mv nil :no state)))
      ;; We found advice that worked:
      (if (eq :add-hyp (help::successful-recommendation-type best-rec))
          ;; Note that :add-hyp is now disallowed above!
          ;; TODO: Consider marking add-hyp as a failure, since we know the theorem is true without a hyp, but then
          ;; we should allow the tool to keep looking for more recs
          (prog2$ (cw "Maybe: hyp added: ~x0)~%" (help::successful-recommendation-object best-rec)) ; close paren matches (ADVICE
                  (b* ( ;; Submit the original defthm (no extra hyp), so we can keep going:
                       ((mv erp state) (submit-event defthm nil nil state))
                       ((when erp) (mv erp :no state)))
                    (mv nil :maybe state)))
        (b* ((proved-with-no-hintsp (equal "original" (help::successful-recommendation-name best-rec)))
             (- (if proved-with-no-hintsp
                    ;; Since we passed nil for the hints, this means the theorem proved with no hints:
                    (if hints-presentp
                        (cw "TRIVIAL (no hints needed, though some were given))~%") ; close paren matches (ADVICE
                      (cw "TRIVIAL (no hints needed or given))~%") ; close paren matches (ADVICE
                      )
                  (progn$ (cw "YES: ~s0: " (help::successful-recommendation-name best-rec))
                          (help::show-successful-recommendation best-rec)
                          (cw ")~%")))) ; close paren matches (ADVICE
             ((mv erp state)
              ;; We submit the event with the hints found by ML, to ensure it works:
              ;; TODO: Instead, have the advice tool check the rec and submit the original event here.
              (submit-event (help::successful-rec-to-defthm defthm-variant theorem-name best-rec rule-classes) nil nil state))
             ((when erp)
              (er hard? 'submit-defthm-event-with-advice "The discovered advice for ~x0 did not work!" theorem-name)
              (mv :advice-didnt-work :no state)))
          (mv nil (if proved-with-no-hintsp :trivial :yes) state))))))

;; Returns (mv erp yes-count no-count maybe-count trivial-count error-count state).
;throws an error if any event fails
(defun submit-events-with-advice (events theorems-to-try num-recs-per-model current-book-absolute-path improve-recsp print model-info-alist timeout
                                         yes-count no-count maybe-count trivial-count error-count
                                         state)
  (declare (xargs :guard (and (true-listp events)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try))
                              (natp num-recs-per-model)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp improve-recsp)
                              (acl2::print-levelp print)
                              (help::model-info-alistp model-info-alist)
                              (natp timeout))
                  :mode :program
                  :stobjs state))
  (if (endp events)
      (mv nil yes-count no-count maybe-count trivial-count error-count state)
    (let ((event (first events)))
      (if (advice-eventp event theorems-to-try)
          ;; It's a theorem for which we are to try advice:
          (b* ( ;; Try to prove it using advice:
               ((mv erp result state)
                (submit-defthm-event-with-advice event num-recs-per-model current-book-absolute-path improve-recsp print model-info-alist timeout state))
               (- (and erp
                       (cw "ERROR (~x0) with advice attempt for event ~X12 (continuing...).~%" erp event nil)
                       )))
            (if erp
                ;; If there is an error, the result is meaningless.  Now, to continue with this book, we need to get the event submitted, so we do it with skip-proofs:
                (b* ((error-count (+ 1 error-count)) ; count this error
                     ((mv erp state)
                      ;; We use skip-proofs (but see the attachment to always-do-proofs-during-make-event-expansion below):
                      ;; TODO: Don't wrap certain events in skip-proofs?
                      (submit-event `(skip-proofs ,event) print nil state))
                     ((when erp)
                      (er hard? 'submit-events-with-advice "ERROR (~x0) with event ~X12 (trying to submit with skip-proofs after error trying to use advice).~%" erp event nil)
                      (mv erp yes-count no-count maybe-count trivial-count error-count state)))
                  (submit-events-with-advice (rest events) theorems-to-try num-recs-per-model current-book-absolute-path improve-recsp print model-info-alist timeout yes-count no-count maybe-count trivial-count error-count state))
              ;; No error, so count the result:
              (submit-events-with-advice (rest events) theorems-to-try num-recs-per-model current-book-absolute-path improve-recsp print model-info-alist timeout
                                         (if (eq :yes result) (+ 1 yes-count) yes-count)
                                         (if (eq :no result) (+ 1 no-count) no-count)
                                         (if (eq :maybe result) (+ 1 maybe-count) maybe-count)
                                         (if (eq :trivial result) (+ 1 trivial-count) trivial-count)
                                         error-count
                                         state)))
        ;; Not something for which we will try advice, so submit it and continue:
        (b* (((mv erp state)
              ;; We use skip-proofs for speed (but see the attachment to always-do-proofs-during-make-event-expansion below):
              (submit-event `(skip-proofs ,event) print nil state))
             ;; FIXME: Anything that tries to read from a file will give an error since the current dir won't be right.
             ((when erp)
              (cw "ERROR (~x0) with event ~X12.~%" erp event nil)
              (mv erp yes-count no-count maybe-count trivial-count error-count state))
             (- (cw "~x0~%" (shorten-event event))))
          (submit-events-with-advice (rest events) theorems-to-try num-recs-per-model current-book-absolute-path improve-recsp print model-info-alist timeout yes-count no-count maybe-count trivial-count error-count state))))))

(defun discard-events-before-first-advice-event (events theorems-to-try)
  (declare (xargs :guard (and (true-listp events)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try)))))
  (if (endp events)
      nil ; we've discarded everything, without finding an advice-event
    (let ((event (first events)))
      (if (advice-eventp event theorems-to-try)
          events ; stop discarding
        (discard-events-before-first-advice-event (rest events) theorems-to-try)))))

;; todo: can't a tool auto-generate this?
(local
 (defthm true-listp-of-discard-events-before-first-advice-event
   (implies (true-listp events)
            (true-listp (discard-events-before-first-advice-event events theorems-to-try)))))

(defun discard-events-after-last-advice-event (events theorems-to-try)
  (declare (xargs :guard (and (true-listp events)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try)))))
  (reverse (discard-events-before-first-advice-event (reverse events) theorems-to-try)))

;; Reads and then submits all the events in FILENAME, trying advice for the theorems.
;; Returns (mv erp counts state), where counts is (list yes-count no-count maybe-count trivial-count error-count).
;; Since this returns an error triple, it can be wrapped in revert-world.
(defun replay-book-with-advice-fn-aux (filename ; the book, with .lisp extension
                                       theorems-to-try
                                       num-recs-per-model
                                       improve-recsp
                                       print
                                       model-info-alist
                                       timeout
                                       state)
  (declare (xargs :guard (and (stringp filename)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try))
                              (natp num-recs-per-model)
                              (booleanp improve-recsp)
                              (acl2::print-levelp print)
                              (help::model-info-alistp model-info-alist)
                              (natp timeout))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (b* (((mv book-existsp state) (file-existsp filename state))
       ((when (not book-existsp))
        (er hard? 'replay-book-with-advice-fn-aux "The book ~x0 does not exist." filename)
        (mv :book-does-not-exist nil state))
       ;; We must avoid including the current book (or an other book that includes it) when trying to find advice:
       (current-book-absolute-path (canonical-pathname filename nil state))
       ((when (member-equal current-book-absolute-path
                            (all-included-books (w state))))
        (cw "WARNING: Can't replay ~s0 because it is already included in the world.~%" filename)
        (mv :book-already-included (list 0 0 0 0 0) state))
       ((mv dir &) (split-path filename))
       (- (cw "REPLAYING ~s0 with advice:~%" filename))
       ;; May be necessary for resolving #. constants in read-objects-from-book:
       (state (load-port-file-if-exists (remove-lisp-suffix filename t) state))
       ;; Read all the forms from the file:
       ((mv erp events state)
        (read-objects-from-book filename state))
       ((when erp) (cw "Error: ~x0.~%" erp) (mv erp (list 0 0 0 0 0) state))
       (len-all-events (len events))
       (events (discard-events-after-last-advice-event events theorems-to-try))
       (- (cw "(~x0 total events, ~x1 after discarding final events.)~%~%" len-all-events (len events)))
       ((when (null events))
        (cw "~%SUMMARY for book ~s0: NO EVENTS TO TEST.  Theorems to try were ~X12.~%" filename theorems-to-try nil)
        (mv nil ; no error, but nothing to do for this book
            (list 0 0 0 0 0) state))
              ;; Ensures we are working in the same dir as the book:
       ;; TODO: Ensure this gets reset upon failure, such as a package name clash.
       ((mv erp & state)
        (set-cbd-fn dir state))
       ((when erp) (mv erp (list 0 0 0 0 0) state))
       ;; Make margins wider for nicer printing:
       (state (widen-margins state))
       ;; Ensure proofs are done during make-event expansion, even if we use skip-proofs:
       ((mv erp state) (submit-event '(defattach (acl2::always-do-proofs-during-make-event-expansion acl2::constant-t-function-arity-0) :system-ok t) nil nil state))
       ((when erp) (mv erp (list 0 0 0 0 0) state))
       ;; Submit all the events, trying advice for each defthm in theorems-to-try:
       ((mv erp yes-count no-count maybe-count trivial-count error-count state)
        (submit-events-with-advice events theorems-to-try num-recs-per-model current-book-absolute-path improve-recsp print model-info-alist timeout 0 0 0 0 0 state))
       ((when erp) ; I suppose we could return partial results from this book instead
        (cw "Error: ~x0.~%" erp)
        (mv erp (list 0 0 0 0 0) state))
       ;; Print stats:
       (- (progn$ (cw "~%SUMMARY for book ~s0:~%" filename)
                  (cw "(Asked each model for ~x0 recommendations.)~%" num-recs-per-model)
                  (cw "ADVICE FOUND    : ~x0~%" yes-count)
                  (cw "NO ADVICE FOUND : ~x0~%" no-count)
                  ;; (cw "ADD HYP ADVICE FOUND : ~x0~%" maybe-count)
                  (cw "NO HINTS NEEDED : ~x0~%" trivial-count)
                  (cw "ERROR           : ~x0~%" error-count)))
       ;; Undo margin widening:
       (state (unwiden-margins state)))
    (mv nil ; no error
        (list yes-count no-count maybe-count trivial-count error-count)
        state)))

;; Reads and then submits all the events in the book indicated by BOOK-PATH,
;; trying advice for defthms that appear at the top level.  Returns (mv erp
;; event state).
(defun replay-book-with-advice-fn (book-path ; path to the book (with or without the .lisp extension)
                                   theorems-to-try ; can be :all
                                   num-recs-per-model
                                   improve-recsp
                                   print
                                   timeout
                                   models ; can be :all
                                   state)
  (declare (xargs :guard (and (stringp book-path)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try))
                              (natp num-recs-per-model)
                              (booleanp improve-recsp)
                              (acl2::print-levelp print)
                              (natp timeout)
                              (or (eq :all models)
                                  (help::model-namesp models)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (b* (;; Elaborate options:
       (book-path (maybe-add-dot-lisp-extension book-path))
       (model-info-alist (help::make-model-info-alist models (w state)))
       ((mv erp
            & ; counts
            state)
        (replay-book-with-advice-fn-aux book-path theorems-to-try num-recs-per-model improve-recsp print model-info-alist timeout state))
       ((when erp) (mv erp nil state)))
    ;; No error:
    (mv nil '(value-triple :replay-succeeded) state)))

;; Currently, when trying advice for a theorem, this deletes all the hints.
;; TODO: Add timing info.
;; This has no effect on the world, because all the work is done in make-event
;; expansion and such changes do not persist.
;; Example: (replay-book-with-advice "../lists-light/append")
(defmacro replay-book-with-advice (book-path ; path to the book (with or without the .lisp extension)
                                   &key
                                   (theorems-to-try ':all) ; gets evaluated
                                   (n '10) ; num-recs-per-model
                                   (improve-recsp 't)
                                   (print 'nil)
                                   (timeout '40) ; for both connection timeout and read timeout
                                   (models ':all)
                                   )
  `(make-event-quiet (replay-book-with-advice-fn ,book-path ,theorems-to-try ,n ,improve-recsp ,print ,timeout ,models state)))
